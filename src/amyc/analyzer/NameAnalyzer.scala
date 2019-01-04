package amyc
package analyzer

import utils._
import ast.{Identifier, NominalTreeModule => N, SymbolicTreeModule => S}

import scala.util.parsing.combinator.token.StdTokens

// Name analyzer for Amy
// Takes a nominal program (names are plain strings, qualified names are string pairs)
// and returns a symbolic program, where all names have been resolved to unique Identifiers.
// Rejects programs that violate the Amy naming rules.
// Also populates and returns the symbol table.
object NameAnalyzer extends Pipeline[N.Program, (S.Program, SymbolTable)] {
  def run(ctx: Context)(p: N.Program): (S.Program, SymbolTable) = {
    import ctx.reporter._

    // Step 0: Initialize symbol table
    val table = new SymbolTable

    // Step 1: Add modules to table 
    val modNames = p.modules.groupBy(_.name)
    modNames.foreach { case (name, modules) =>
      if (modules.size > 1) {
        fatal(s"Two modules named $name in program", modules.head.position)
      }
    }

    modNames.keys.toList foreach table.addModule



    // Helper method: will transform a nominal type 'tt' to a symbolic type,
    // given that we are within module 'inModule'.
    def transformType(tt: N.TypeTree, inModule: String): S.Type = {
      tt.tpe match {
        case N.IntType => S.IntType
        case N.BooleanType => S.BooleanType
        case N.StringType => S.StringType
        case N.UnitType => S.UnitType
        case N.ClassType(qn@N.QualifiedName(module, name)) =>
          table.getType(module getOrElse inModule, name) match {
            case Some(symbol) =>
              S.ClassType(symbol)
            case None =>
              fatal(s"Could not find type $qn", tt)
          }
      }
    }


    // Step 2: Check name uniqueness of definitions in each module
    val mods = p.modules
    mods.foreach( m =>{
      val moddefs = m.defs.groupBy(_.name)
      moddefs.foreach{
        case(name, defs) => if(defs.size > 1){
          fatal(s"Two modules named $name in program")
        }
      }
    }
    )


    // Step 3: Discover types and add them to symbol table
    val modsname = mods.map{
      case N.ModuleDef(name, defs, _) => (name, defs)
    }

    modsname.foreach{
      case(name, defs) =>
        defs.foreach(d => d match{
          case N.AbstractClassDef(aname) =>
            table.addType(name, aname)
          case _ =>
        })
    }

    // Step 4: Discover type constructors, add them to table
    modsname.foreach{
      case(name, defs) =>
        defs.foreach(d => d match{
          case N.CaseClassDef(cname, fields, parent)=>
            table.addConstructor(name, cname,
              fields.map(transformType(_, name)),
              table.getType(name, parent).
                getOrElse(fatal("This class doesn't exist")))
          case _ =>
        })
    }

    // Step 5: Discover functions signatures, add them to table
    modsname.foreach{
      case(name, defs) => defs.foreach(d => d match{
        case N.FunDef(fname, params, retType, body) =>
          table.addFunction(name, fname, params.
            map(x => transformType(x.tt, name)),
            transformType(retType, name))
        case _ =>
      })
    }



    // Step 6: We now know all definitions in the program.
    //         Reconstruct modules and analyse function bodies/ expressions
    
    // This part is split into three transfrom functions,
    // for definitions, FunDefs, and expressions.
    // Keep in mind that we transform constructs of the NominalTreeModule 'N' to respective constructs of the SymbolicTreeModule 'S'.
    // transformFunDef is given as an example, as well as some code for the other ones

    def transformDef(df: N.ClassOrFunDef, module: String): S.ClassOrFunDef = { df match {
      case N.AbstractClassDef(name) =>
        val Some(id)= table.getType(module, name)
        S.AbstractClassDef(id)
      case N.CaseClassDef(name, _, _) =>
        val idsig = table.getConstructor(module, name).get
        val f = idsig._2.argTypes.map(x => S.TypeTree(x))
        val parent = idsig._2.parent
        S.CaseClassDef(idsig._1, f, parent)
      case fd: N.FunDef =>
        transformFunDef(fd, module)
    }}.setPos(df)

    def transformFunDef(fd: N.FunDef, module: String): S.FunDef = {
      val N.FunDef(name, params, retType, body) = fd
      val Some((sym, sig)) = table.getFunction(module, name)

      params.groupBy(_.name).foreach { case (name, ps) =>
        if (ps.size > 1) {
          fatal(s"Two parameters named $name in function ${fd.name}", fd)
        }
      }

      val paramNames = params.map(_.name)

      val newParams = params zip sig.argTypes map { case (pd@N.ParamDef(name, tt), tpe) =>
        val s = Identifier.fresh(name)
        S.ParamDef(s, S.TypeTree(tpe).setPos(tt)).setPos(pd)
      }

      val paramsMap = paramNames.zip(newParams.map(_.name)).toMap

      S.FunDef(
        sym,
        newParams,
        S.TypeTree(sig.retType).setPos(retType),
        transformExpr(body)(module, (paramsMap, Map()))
      ).setPos(fd)
    }

    // This function takes as implicit a pair of two maps:
    // The first is a map from names of parameters to their unique identifiers,
    // the second is similar for local variables.
    // Make sure to update them correctly if needed given the scoping rules of Amy
    def transformExpr(expr: N.Expr)
                     (implicit module: String, names: (Map[String, Identifier], Map[String, Identifier])): S.Expr = {
      val (params, locals) = names
      val res = expr match {
        case N.Match(scrut, cases) =>
          // Returns a transformed pattern along with all bindings
          // from strings to unique identifiers for names bound in the pattern.
          // Also, calls 'fatal' if a new name violates the Amy naming rules.
          def transformPattern(pat: N.Pattern): (S.Pattern, List[(String, Identifier)]) = {
            pat match{
              case N.WildcardPattern() => (S.WildcardPattern(), List())
                //case class IdPattern(name: Name) extends Pattern // x
              case N.IdPattern(name) =>
                val newId = Identifier.fresh(name)
                if(locals.contains(name)) {
                  fatal("this name already exists")
                }
                (S.IdPattern(newId), List((name, newId)))

              //case class LiteralPattern[+T](lit: Literal[T]) extends Pattern // 42, true
              case N.LiteralPattern(lit) =>
                val l = transformExpr(lit).asInstanceOf[S.Literal[_]]
                (S.LiteralPattern(l), List())

              //case class CaseClassPattern(constr: QualifiedName, args: List[Pattern]) extends Pattern
              case N.CaseClassPattern(constr, args) =>

                val idSig = table.getConstructor(module, constr.name)

                if(idSig==None){
                  fatal("constructor doesn't exist")
                }

                if(idSig.get._2.argTypes.size != args.size){
                  fatal("Not the good number of arguments")
                }

                args.filter(a=> a.isInstanceOf[N.IdPattern]).
                  groupBy(a => a.asInstanceOf[N.IdPattern].name).foreach({
                  case(name, l) => if(l.size > 1) {
                    fatal("Duplicate match")
                  }
                })

                val transargs = args.map(x => transformPattern(x))
                (S.CaseClassPattern(idSig.get._1, transargs.map(_._1)), transargs.flatMap(_._2))
            }
          }

          def transformCase(cse: N.MatchCase) = {
            val N.MatchCase(pat, rhs) = cse
            val (newPat, moreLocals) = transformPattern(pat)
            val expr = transformExpr(rhs)(module, (params, locals++moreLocals))
            S.MatchCase(newPat, expr)
          }

          S.Match(transformExpr(scrut), cases.map(transformCase))


        //case class Variable(name: Name) extends Expr
        case N.Variable(name) => {
          val localname = locals.get(name)
          val paramname = params.get(name)

          if(localname.isEmpty){
            if(paramname.isEmpty){
              fatal("This variable doesn't exist")
            }
            else S.Variable(paramname.get)
          } else{
            S.Variable(localname.get)
          }

        }


        //  case class IntLiteral(value: Int) extends Literal[Int]
        case N.IntLiteral(i) =>
          S.IntLiteral(i)

        //  case class BooleanLiteral(value: Boolean) extends Literal[Boolean]
        case N.BooleanLiteral(value) =>
          S.BooleanLiteral(value)

        //  case class StringLiteral(value: String) extends Literal[String]
        case N.StringLiteral(value) =>
          S.StringLiteral(value)

        //  case class UnitLiteral() extends Literal[Unit] { val value: Unit = () }
        case N.UnitLiteral() =>
          S.UnitLiteral()

        //  case class Plus(lhs: Expr, rhs: Expr) extends Expr
        case N.Plus(lhs, rhs) =>
          S.Plus(transformExpr(lhs), transformExpr(rhs))

        //  case class Minus(lhs: Expr, rhs: Expr) extends Expr
        case N.Minus(lhs, rhs) =>
          S.Minus(transformExpr(lhs), transformExpr(rhs))

        //  case class Times(lhs: Expr, rhs: Expr) extends Expr
        case N.Times(lhs, rhs) =>
          S.Times(transformExpr(lhs), transformExpr(rhs))

        //  case class Div(lhs: Expr, rhs: Expr) extends Expr
        case N.Div(lhs, rhs) =>
          S.Div(transformExpr(lhs), transformExpr(rhs))

        //  case class Mod(lhs: Expr, rhs: Expr) extends Expr
        case N.Mod(lhs, rhs) =>
          S.Mod(transformExpr(lhs), transformExpr(rhs))

        //  case class LessThan(lhs: Expr, rhs: Expr) extends Expr
        case N.LessThan(lhs, rhs) =>
          S.LessThan(transformExpr(lhs), transformExpr(rhs))

        //  case class LessEquals(lhs: Expr, rhs: Expr) extends Expr
        case N.LessEquals(lhs, rhs) =>
          S.LessEquals(transformExpr(lhs), transformExpr(rhs))

        //  case class And(lhs: Expr, rhs: Expr) extends Expr
        case N.And(lhs, rhs) =>
          S.And(transformExpr(lhs), transformExpr(rhs))

        //  case class Or(lhs: Expr, rhs: Expr) extends Expr
        case N.Or(lhs, rhs) =>
          S.Or(transformExpr(lhs), transformExpr(rhs))

        //  case class Equals(lhs: Expr, rhs: Expr) extends Expr
        case N.Equals(lhs, rhs) =>
          S.Equals(transformExpr(lhs), transformExpr(rhs))

        //  case class Concat(lhs: Expr, rhs: Expr) extends Expr
        case N.Concat(lhs, rhs) =>
          S.Concat(transformExpr(lhs), transformExpr(rhs))

        //  case class Not(e: Expr) extends Expr
        case N.Not(e) =>
          S.Not(transformExpr(e))

        //  case class Neg(e: Expr) extends Expr
        case N.Neg(e) =>
          S.Neg(transformExpr(e))

        //  case class Call(qname: QualifiedName, args: List[Expr]) extends Expr
        case N.Call(qname, args) =>{
          //call peut appeler une fonction ou un constructeur
          val f = table.getFunction(qname.module.getOrElse(module), qname.name)
          val cons = table.getConstructor(qname.module.getOrElse(module), qname.name)
          val sargs= args.map(a => transformExpr(a))

          //cas constructeur
          if(f.isEmpty){
            if(cons.isEmpty){
              fatal("This doesn't exist")
            }else {
              if (cons.get._2.argTypes.size != args.size) {
                fatal("Not the good number of params")
              }
              S.Call(cons.get._1, sargs)
            }
            //cas fonction
          } else {

            if(f.get._2.argTypes.size != args.size){
              fatal("Not the good number of params")
            }
            S.Call(f.get._1, sargs)
          }
        }

        //  case class Sequence(e1: Expr, e2: Expr) extends Expr
        case N.Sequence(e1, e2) =>
          S.Sequence(transformExpr(e1), transformExpr(e2))

        //  case class Let(df: ParamDef, value: Expr, body: Expr) extends Expr

        case N.Let(df, value, body) =>{

          if(locals.get(df.name) != None){
            fatal("This variable is already in the table.")
          }

          val sName = Identifier.fresh(df.name)
          val sp = S.ParamDef(sName, S.TypeTree(transformType(df.tt, module)))
          val se = transformExpr(value)
          val sb = transformExpr(body)(module, (params, locals+(df.name -> sName)))

          S.Let(sp, se, sb)
        }

        //  case class Ite(cond: Expr, thenn: Expr, elze: Expr) extends Expr
        case N.Ite(cond, thenn, elze) =>
          S.Ite(transformExpr(cond), transformExpr(thenn), transformExpr(elze))

        // case class Error(msg: Expr) extends Expr
        case N.Error(msg) =>
          S.Error(transformExpr(msg))
      }
      res.setPos(expr)
    }

    // Putting it all together to construct the final program for step 6.
    val newProgram = S.Program(
      p.modules map { case mod@N.ModuleDef(name, defs, optExpr) =>
        S.ModuleDef(
          table.getModule(name).get,
          defs map (transformDef(_, name)),
          optExpr map (transformExpr(_)(name, (Map(), Map())))
        ).setPos(mod)
      }
    ).setPos(p)

    (newProgram, table)

  }
}
