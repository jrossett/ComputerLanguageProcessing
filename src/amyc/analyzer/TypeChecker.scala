package amyc
package analyzer

import utils._
import ast.SymbolicTreeModule._
import ast.Identifier

// The type checker for Amy
// Takes a symbolic program and rejects it if it does not follow the Amy typing rules.
object TypeChecker extends Pipeline[(Program, SymbolTable), (Program, SymbolTable)] {

  def run(ctx: Context)(v: (Program, SymbolTable)): (Program, SymbolTable) = {
    import ctx.reporter._

    val (program, table) = v

    case class Constraint(found: Type, expected: Type, pos: Position)

    // Represents a type variable.
    // It extends Type, but it is meant only for internal type checker use,
    //  since no Amy value can have such type.
    case class TypeVariable private (id: Int) extends Type
    object TypeVariable {
      private val c = new UniqueCounter[Unit]
      def fresh(): TypeVariable = TypeVariable(c.next(()))
    }

    // Generates typing constraints for an expression `e` with a given expected type.
    // The environment `env` contains all currently available bindings (you will have to
    //  extend these, e.g., to account for local variables).
    // Returns a list of constraints among types. These will later be solved via unification.
    def genConstraints(e: Expr, expected: Type)(implicit env: Map[Identifier, Type]): List[Constraint] = {
      
      // This helper returns a list of a single constraint recording the type
      //  that we found (or generated) for the current expression `e`
      def topLevelConstraint(found: Type): List[Constraint] =
        List(Constraint(found, expected, e.position))
      
      e match {
        case IntLiteral(_) =>
          topLevelConstraint(IntType)
        case BooleanLiteral(_) =>
          topLevelConstraint(BooleanType)
        case StringLiteral(_)=>
          topLevelConstraint(StringType)
        case UnitLiteral() =>
          topLevelConstraint(UnitType)
        
        case Equals(lhs, rhs) =>
          val T = TypeVariable.fresh()
          val l = genConstraints(lhs, T)
          val r = genConstraints(rhs, T)
          l++r++topLevelConstraint(BooleanType)
        
        case Match(scrut, cases) =>
          // Returns additional constraints from within the pattern with all bindings
          // from identifiers to types for names bound in the pattern.
          // (This is analogous to `transformPattern` in NameAnalyzer.)
          def handlePattern(pat: Pattern, scrutExpected: Type):
            (List[Constraint], Map[Identifier, Type]) =
          {
            pat match{
              //WildcardPattern()
              case WildcardPattern() => (List(), Map())
              //IdPattern(name: Name)
              case IdPattern(name) =>
                (List(), Map(name -> scrutExpected))
              //LiteralPattern[+T](lit: Literal[T])
              case LiteralPattern(lit) =>
                (genConstraints(lit, scrutExpected), Map())
              //CaseClassPattern(constr: QualifiedName, args: List[Pattern])
              case CaseClassPattern(constr, args) =>
                val classConstr = table.getConstructor(constr).get
                val ziparg = args.zip(classConstr.argTypes)
                val handled = for{x <- ziparg} yield handlePattern(x._1, x._2)
                val constrs = handled.map(_._1).flatten
                val mapidtype = handled.map(_._2).flatten.toMap
                (Constraint(classConstr.retType, scrutExpected, pat.position)::constrs, mapidtype)
            }
          }

          def handleCase(cse: MatchCase, scrutExpected: Type): List[Constraint] = {
            val (patConstraints, moreEnv) = handlePattern(cse.pat, scrutExpected)
            patConstraints ::: genConstraints(cse.expr, expected)(env ++ moreEnv)
          }

          val st = TypeVariable.fresh()
          genConstraints(scrut, st) ++ cases.flatMap(cse => handleCase(cse, st))

        case Variable(name) => topLevelConstraint(env(name))
        //  case class Plus(lhs: Expr, rhs: Expr) extends Expr
        case Plus(lhs, rhs) =>
          genConstraints(lhs, IntType):::genConstraints(rhs, IntType):::topLevelConstraint(IntType)
        //  case class Minus(lhs: Expr, rhs: Expr) extends Expr
        case Minus(lhs, rhs) =>
          genConstraints(lhs, IntType):::genConstraints(rhs, IntType):::topLevelConstraint(IntType)
        //  case class Times(lhs: Expr, rhs: Expr) extends Expr
        case Times(lhs, rhs) =>
          genConstraints(lhs, IntType):::genConstraints(rhs, IntType):::topLevelConstraint(IntType)
        //  case class Div(lhs: Expr, rhs: Expr) extends Expr
        case Div(lhs, rhs) =>
          genConstraints(lhs, IntType):::genConstraints(rhs, IntType):::topLevelConstraint(IntType)
        //  case class Mod(lhs: Expr, rhs: Expr) extends Expr
        case Mod(lhs, rhs) =>
          genConstraints(lhs, IntType):::genConstraints(rhs, IntType):::topLevelConstraint(IntType)
        //  case class LessThan(lhs: Expr, rhs: Expr) extends Expr
        case LessThan(lhs, rhs) =>
          genConstraints(lhs, IntType):::genConstraints(rhs, IntType):::topLevelConstraint(BooleanType)
        //  case class LessEquals(lhs: Expr, rhs: Expr) extends Expr
        case LessEquals(lhs, rhs) =>
          genConstraints(lhs, IntType):::genConstraints(rhs, IntType):::topLevelConstraint(BooleanType)
        //  case class And(lhs: Expr, rhs: Expr) extends Expr
        case And(lhs, rhs) =>
          genConstraints(lhs, BooleanType):::genConstraints(rhs, BooleanType):::topLevelConstraint(BooleanType)
        //  case class Or(lhs: Expr, rhs: Expr) extends Expr
        case Or(lhs, rhs) =>
          genConstraints(lhs, BooleanType):::genConstraints(rhs, BooleanType):::topLevelConstraint(BooleanType)
        //  case class Concat(lhs: Expr, rhs: Expr) extends Expr
        case Concat(lhs, rhs) =>
          genConstraints(lhs, StringType):::genConstraints(rhs, StringType):::topLevelConstraint(StringType)
        //  case class Not(e: Expr) extends Expr
        case Not(e) =>
          genConstraints(e, BooleanType):::topLevelConstraint(BooleanType)
        //  case class Neg(e: Expr) extends Expr
        case Neg(e) =>
          genConstraints(e, IntType):::topLevelConstraint(IntType)
        //  case class Call(qname: QualifiedName, args: List[Expr]) extends Expr
        case Call(qname, args) =>
          val types = args.zip(table.getFunction(qname).getOrElse(table.getConstructor(qname).get).argTypes)
          types.map(x => genConstraints(x._1, x._2)).flatten :::
            topLevelConstraint(table.getFunction(qname).getOrElse(table.getConstructor(qname).get).retType)
        //  case class Sequence(e1: Expr, e2: Expr) extends Expr
        case Sequence(e1, e2) =>
          val T1 = TypeVariable.fresh()
          val ex1 = genConstraints(e1, T1)
          val ex2 = genConstraints(e2, expected)
          ex1 ::: ex2 ::: topLevelConstraint(expected)

        //  case class Let(df: ParamDef, value: Expr, body: Expr) extends Expr
        case Let(df, value, body) =>
          val T1 = df.tt.tpe
          val e1 = genConstraints(value, T1)
          e1 ::: genConstraints(body, expected)(env+(df.name -> T1))

        //  case class Ite(cond: Expr, thenn: Expr, elze: Expr) extends Expr
        case Ite(cond, thenn, elze) =>
          val T = TypeVariable.fresh()
          val e1 = genConstraints(thenn, expected)
          val e2 = genConstraints(elze, expected)
          genConstraints(cond, BooleanType) ::: e1 ::: e2
        //  case class Error(msg: Expr) extends Expr
        case Error(msg) =>
          val T = TypeVariable.fresh()
          genConstraints(msg, StringType) ++ topLevelConstraint(expected)
      }
    }


    // Given a list of constraints `constraints`, replace every occurence of type variable
    //  with id `from` by type `to`.
    def subst_*(constraints: List[Constraint], from: Int, to: Type): List[Constraint] = {
      // Do a single substitution.
      def subst(tpe: Type, from: Int, to: Type): Type = {
        tpe match {
          case TypeVariable(`from`) => to
          case other => other
        }
      }

      constraints map { case Constraint(found, expected, pos) =>
        Constraint(subst(found, from, to), subst(expected, from, to), pos)
      }
    }

    // Solve the given set of typing constraints and
    //  call `typeError` if they are not satisfiable.
    // We consider a set of constraints to be satisfiable exactly if they unify.
    def solveConstraints(constraints: List[Constraint]): Unit = {
      constraints match {
        case Nil => ()
        case Constraint(found, expected, pos) :: more =>
          // HINT: You can use the `subst_*` helper above to replace a type variable
          //       by another type in your current set of constraints.
          found match {
            case TypeVariable(id) => expected match{
              case TypeVariable(idExp) if(idExp == id)=> solveConstraints(more)
              case _ => solveConstraints(subst_*(more, id, expected))}

            case IntType => expected match{
              case IntType => solveConstraints(more)
              case TypeVariable(id) => solveConstraints(subst_*(more, id, IntType))
              case _ => error("typeError", pos)
            }
            case BooleanType => expected match{
              case BooleanType => solveConstraints(more)
              case TypeVariable(id) => solveConstraints(subst_*(more, id, BooleanType))
              case _ => error("typeError", pos)
            }

            case StringType => expected match{
              case StringType => solveConstraints(more)
              case TypeVariable(id) => solveConstraints(subst_*(more, id, StringType))
              case _ => error("typeError", pos)
            }

            case UnitType => expected match{
              case UnitType => solveConstraints(more)
              case TypeVariable(id) => solveConstraints(subst_*(more, id, UnitType))
              case _ => error("typeError", pos)
            }

            case ClassType(x) => expected match{
              case ClassType(y) if (x==y)=> solveConstraints(more)
              case TypeVariable(id) => solveConstraints(subst_*(more, id, ClassType(x)))
              case _ => error("typeError", pos)
            }
          }
      }
    }

    // Putting it all together to type-check each module's functions and main expression.
    program.modules.foreach { mod =>
      // Put function parameters to the symbol table, then typecheck them against the return type
      mod.defs.collect { case FunDef(_, params, retType, body) =>
        val env = params.map{ case ParamDef(name, tt) => name -> tt.tpe }.toMap
        solveConstraints(genConstraints(body, retType.tpe)(env))
      }

      // Type-check expression if present. We allow the result to be of an arbitrary type by
      // passing a fresh (and therefore unconstrained) type variable as the expected type.
      val tv = TypeVariable.fresh()
      mod.optExpr.foreach(e => solveConstraints(genConstraints(e, tv)(Map())))
    }

    v


  }


}
