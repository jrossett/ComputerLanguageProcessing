package amyc
package parsing

import grammarcomp.parsing._
import utils.Positioned
import ast.NominalTreeModule._
import Tokens._

// Implements the translation from parse trees to ASTs for the LL1 grammar,
// that is, this should correspond to Parser.amyGrammarLL1.
// We extend the plain ASTConstructor as some things will be the same -- you should
// override whatever has changed. You can look into ASTConstructor as an example.
class ASTConstructorLL1 extends ASTConstructor {


  @Override
  override def constructQname(pTree: NodeOrLeaf[Token]): (QualifiedName, Positioned) = {
    pTree match {
      case Node('QName ::= _, List(id, Node('QNameS ::= _, List()))) =>
        val (name, pos) = constructName(id)
        (QualifiedName(None, name), pos)
      case Node('QName ::= _, List(mod, Node('QNameS
        ::= _, List(_, nm)))) =>
        val (module, pos) = constructName(mod)
        val (name, _) = constructName(nm)
        (QualifiedName(Some(module), name), pos)
    }
  }

//'Pattern ::= UNDERSCORE() |
//             'Literal |
//              'Id ~ 'PatternS,
// 'PatternS ::= LPAREN() ~ 'Patterns ~ RPAREN() |
//         DOT() ~ 'Id ~ LPAREN() ~ 'Patterns ~ RPAREN() |
//        epsilon(),
  @Override
  override  def constructPattern(pTree: NodeOrLeaf[Token]): Pattern = {
    pTree match {
      case Node('Pattern ::= List(UNDERSCORE()), List(Leaf(ut))) =>
        WildcardPattern().setPos(ut)
      case Node('Pattern ::= List('Literal), List(lit)) =>
        val literal = constructLiteral(lit)
        LiteralPattern(literal).setPos(literal)

//CAS ID
      case Node('Pattern ::= ('Id::_), List(id, Node('PatternS ::=_, List())))=>
        val (name, pos) = constructName(id)
        IdPattern(name).setPos(pos)

//CAS ID LPAR PATTERNS RPAR
      case Node('Pattern ::= ('Id :: _), List(id, Node('PatternS::=_, List(_, patts, _))))=>
        val (name, pos) = constructName(id)
        val qname= QualifiedName(None, name)
        val patterns = constructList(patts, constructPattern, hasComma = true)
        CaseClassPattern(qname, patterns).setPos(pos)

//CAS ID DOT ID LPAR PATTERNS RPAR
      case Node('Pattern ::= ('Id::_), List(id1, Node('PatternS::=_, List(_, id2, _, patts, _))))=>
        val (name1, pos) = constructName(id1)
        val (name2, _) = constructName(id2)
        val qname= QualifiedName(Some(name1), name2)
        val patterns = constructList(patts, constructPattern, hasComma = true)
        CaseClassPattern(qname, patterns).setPos(pos)
    }
  }




//  'Expr ::= VAL() ~ 'Param ~ EQSIGN() ~ 'Exprime ~ SEMICOLON() ~ 'Expr | 'Exprime ~ 'Tsem,
//    'Exprime ::= 'Tnivor ~ 'Tmatch,
//    'Tsem ::= SEMICOLON() ~ 'Tsemprime | epsilon(),
//    'Tsemprime ::= 'Expr | epsilon(),
//    'Tmatch ::= MATCH() ~ LBRACE() ~ 'Cases ~ RBRACE() | epsilon(),
@Override
override def constructExpr(ptree: NodeOrLeaf[Token]): Expr = {
  ptree match{
    case Node('Expr ::= (VAL() :: _), List(Leaf(vt), param, _, value, _, body)) =>
      Let(constructParam(param), constructExprime(value), constructExpr(body)).setPos(vt)
    case Node('Expr ::= List('Exprime, 'Tsem), List(ex, tsem)) => tsem match{
      case Node('Tsem::=_, List()) =>
        val x = constructExprime(ex)
        val y = x.setPos(x)
        y.setPos(y)
      case Node('Tsem::=(SEMICOLON()::_), List(_, expr)) =>
        val x = constructExprime(ex)
        val y = Sequence(x, constructExpr(expr)).setPos(x)
        y.setPos(y)
    }

  }
}


  def constructExprime(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match{
      case Node('Exprime::=List('Tnivor, 'Tmatch), List(l, r)) => r match{

        case Node('Tmatch::=(MATCH()::_), List(_, _, cases, _))=>
          val x = constructTnivor(l)
            Match(x, constructList1(cases, constructCase)).setPos(x)
        case Node('Tmatch::=_, List()) =>
          val x = constructTnivor(l)
          x.setPos(x)
    }
    }
  }


  // 'Tnivor ::= 'Tnivand ~ 'Tor,
  // 'Tor ::= OR() ~ 'Tnivand | epsilon()
  def constructTnivor(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match{
      case Node('Tnivor::=List('Tnivand, 'Tor), List(l, r)) =>
        val x = constructTnivand(l)
        constructOpExpr(x, r).setPos(x)
    }
  }

  // 'Tnivand ::= 'Tniveq ~ 'Tand,
  // 'Tand ::= AND() ~ 'Tniveq | epsilon(),
  def constructTnivand(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match{
      case Node('Tnivand::=List('Tniveq, 'Tand), List(l, r)) =>
        val x = constructTniveq(l)
        constructOpExpr(x, r).setPos(x)
    }
  }


  // 'Tniveq ::= 'Tnivless ~ 'Tequals,
  // 'Tequals ::= EQUALS() ~ 'Tnivless | epsilon(),
  def constructTniveq(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match{
      case Node('Tniveq::=List('Tnivless, 'Tequals), List(l, r))=>
        val x = constructTnivless(l)
        constructOpExpr(x, r).setPos(x)
    }
  }


  // 'Tnivless ::= 'Tnivplus ~ 'Tless,
  // 'Tless ::= LESSTHAN() ~ 'Tnivplus | LESSEQUALS() ~ 'Tnivplus | epsilon(),
  def constructTnivless(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match{
      case Node('Tnivless::=List('Tnivplus, 'Tless), List(l, r))=>
        val x = constructTnivplus(l)
        constructOpExpr(x, r).setPos(x)
    }
  }


  // 'Tnivplus ::= 'Tnivdiv ~ 'TplusMinusConcat,
  // 'TplusMinusConcat ::= PLUS() ~ 'Tnivplus | MINUS() ~ 'Tnivplus | epsilon(),
  def constructTnivplus(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match{
      case Node('Tnivplus::=List('Tnivdiv, 'TplusMinusConcat), List(l, r)) =>
        val x= constructnivdiv(l)
        constructOpExpr(x, r).setPos(x)
    }
  }


  // 'Tnivdiv ::= 'Tprime ~ 'TdivTimesMod,
  // 'TdivTimesMod ::= TIMES() ~ 'Tprime | MOD() ~ 'Tprime | DIV() ~ 'Tprime | epsilon(),
  def constructnivdiv(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match{
      case Node('Tnivdiv::=List('Tprime, 'TdivTimesMod), List(f,rightexpr)) => {
        val x = constructtprime(f)
        constructOpExpr(x, rightexpr).setPos(x)
      }
    }
  }

  // 'Tprime ::= BANG() ~'F | MINUS() ~ 'F | 'F,
  def constructtprime(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match{
      case Node(_::=List(BANG(), 'F), List(Leaf(bt), f)) =>
        val e = constructF(f)
        Not(e).setPos(bt)
      case Node(_::=List(MINUS(), 'F), List(Leaf(mt), f)) =>
        Neg(constructF(f)).setPos(mt)
      case Node(_::=List('F), List(f)) =>
        val x = constructF(f)
        x.setPos(x)
    }
  }

  /*
  * 'F ::= LPAREN() ~ 'Expr ~ RPAREN() |
           'QName ~ 'FS |
           TRUE() |
           FALSE() |
           INTLITSENT |
           STRINGLITSENT |
           ERROR() ~ LPAREN() ~ 'Expr ~ RPAREN() |
           IF() ~ LPAREN() ~ 'Expr ~ RPAREN() ~ LBRACE() ~ 'Expr ~ RBRACE() ~ ELSE() ~ LBRACE() ~ 'Expr ~ RBRACE(),
  * */
  def constructF(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match{
      case Node('F ::= List(LPAREN(), 'Exprourien, RPAREN()), List(Leaf(lp), expr, _)) => expr match{
        case Node('Exprourien::=_, List()) =>
          UnitLiteral().setPos(lp)
        case Node('Exproiurien::=('Expr::_), List(expr))=>
          constructExpr(expr).setPos(lp)
      }


      case Node('F ::= ('Id::_), List(id, fs))=>fs match{
        case Node('FS::=_, List()) =>
          val (name, pos) = constructName(id)
          Variable(name).setPos(pos)
        case Node('FS::=(DOT()::_), List(_, idfs, _, args, _)) =>
          val qName = constructList(args, constructExpr, hasComma=true)
          val (module, p) = constructName(id)
          val (name, _) = constructName(idfs)
          val (x, pos) = (QualifiedName(Some(module), name), p)
          Call(x, qName).setPos(pos)
        case Node('FS::=(LPAREN()::_), List(_, args, _))=>
          val qNameCons = constructList(args, constructExpr, hasComma = true)
          val (name, p) = constructName(id)
          val x = QualifiedName(None, name)
          Call(x, qNameCons).setPos(p)

      }

      case Node('F ::= List(TRUE()), List(Leaf(tt@TRUE()))) =>
        BooleanLiteral(true).setPos(tt)
      case Node('F ::= List(FALSE()), List(Leaf(tf@FALSE()))) =>
        BooleanLiteral(false).setPos(tf)
      case Node('F ::= (List(INTLITSENT)), List(Leaf(it@INTLIT(i)))) =>
        IntLiteral(i).setPos(it)
      case Node('F ::= List(STRINGLITSENT), List(Leaf(st@STRINGLIT(s)))) =>
        StringLiteral(s).setPos(st)
      case Node('F ::= (ERROR()::_), List(Leaf(ert), _, msg, _)) =>
        Error(constructExpr(msg)).setPos(ert)
      case Node('F ::= (IF() :: _), List(Leaf(it), _, cond, _, _, thenn, _, _, _, elze, _)) =>
        cond match{
         case Node('F::=_, _)=>
           Ite(
             constructF(cond),
             constructExpr(thenn),
             constructExpr(elze)
           ).setPos(it)
         case Node('Tnivdiv::=_, _)=>
           Ite(
             constructnivdiv(cond),
             constructExpr(thenn),
             constructExpr(elze)
           ).setPos(it)
         case Node('Tnivplus::=_, _) =>
           Ite(
             constructTnivplus(cond),
             constructExpr(thenn),
             constructExpr(elze)
           ).setPos(it)
         case Node('Tnivless::=_, _) =>
           Ite(
             constructTnivless(cond),
             constructExpr(thenn),
             constructExpr(elze)
           ).setPos(it)
         case Node('Tniveq::=_, _) =>
           Ite(
             constructTniveq(cond),
             constructExpr(thenn),
             constructExpr(elze)
           ).setPos(it)
         case Node('Tnivand::=_, _) =>
           Ite(
             constructTnivand(cond),
             constructExpr(thenn),
             constructExpr(elze)
           ).setPos(it)
         case Node('Tnivor::=_, _ )=>
           Ite(
             constructTnivor(cond),
             constructExpr(thenn),
             constructExpr(elze)
           ).setPos(it)
         case _ =>
           Ite(
             constructExpr(cond),
             constructExpr(thenn),
             constructExpr(elze)
           ).setPos(it)
       }
    }
  }


  // Important helper method:
  // Because LL1 grammar is not helpful in implementing left associativity,
  // we give you this method to reconstruct it.
  // This method takes the left operand of an operator (leftopd)
  // as well as the tree that corresponds to the operator plus the right operand (ptree)
  // It parses the right hand side and then reconstruct the operator expression
  // with correct associativity.
  // If ptree is empty, it means we have no more operators and the leftopd is returned.
  // Note: You may have to override constructOp also, depending on your implementation
  def constructOpExpr2(leftopd: Expr, ptree: NodeOrLeaf[Token]): Expr = {
    ptree match {
      case Node(_, List()) => //epsilon rule of the nonterminals
        leftopd
      case Node(sym ::= _, List(op, rightNode))
        if Set('OrExpr, 'AndExpr, 'EqExpr, 'CompExpr, 'AddExpr, 'MultExpr) contains sym =>
        rightNode match {
          case Node(_, List(nextOpd, suf)) => // 'Expr? ::= Expr? ~ 'OpExpr,
            val nextAtom = constructExpr(nextOpd)
            constructOpExpr(constructOp(op)(leftopd, nextAtom).setPos(leftopd), suf) // captures left associativity
        }
    }
  }

  def constructOpExpr(leftopd: Expr, ptree: NodeOrLeaf[Token]): Expr = {
    ptree match {
      case Node(_, List()) => //epsilon rule of the nonterminals
        leftopd
      case Node(sym ::= _, List(op, rightNode))
         if Set('Tor, 'Tand, 'Tequals, 'Tless, 'TplusMinusConcat, 'TdivTimesMod) contains sym =>
         rightNode match {
           case Node(_, List(nextOpd, suf)) =>
             nextOpd match{
               case Node('Tprime::=_, _) =>
                 val nextAtom= constructtprime(nextOpd)
                 constructOpExpr(constructOp(op)(leftopd, nextAtom).setPos(leftopd), suf)
               case Node('Tnivdiv::=_, _) =>
                 val nextAtom = constructnivdiv(nextOpd)
                 constructOpExpr(constructOp(op)(leftopd, nextAtom).setPos(leftopd), suf)
               case Node('Tnivplus::=_, _) =>
                 val nextAtom = constructTnivplus(nextOpd)
                 constructOpExpr(constructOp(op)(leftopd, nextAtom).setPos(leftopd), suf)
               case Node('Tnivless ::=_, _) =>
                 val nextAtom = constructTnivless(nextOpd)
                 constructOpExpr(constructOp(op)(leftopd, nextAtom).setPos(leftopd), suf)
               case Node('Tniveq::=_, _) =>
                 val nextAtom =constructTniveq(nextOpd)
                 constructOpExpr(constructOp(op)(leftopd, nextAtom).setPos(leftopd), suf)
               case Node('Tnivand::=_, _)=>
                 val nextAtom= constructTnivand(nextOpd)
                 constructOpExpr(constructOp(op)(leftopd, nextAtom).setPos(leftopd), suf)
               case Node('Tnivor::=_, _)=>
                 val nextAtom= constructTnivor(nextOpd)
                 constructOpExpr(constructOp(op)(leftopd, nextAtom).setPos(leftopd), suf)

             }
           case Node('Tprime::=_, _) =>
             val nextAtom = constructtprime(rightNode)
             constructOp(op)(leftopd, nextAtom).setPos(leftopd)
        }

    }

  }

  @Override
  override def constructOp(ptree: NodeOrLeaf[Token]): (Expr, Expr) => Expr = {
    ptree match {
      case Leaf(t) =>
        tokenToExpr(t)
      case Node(_, List(Leaf(t))) =>
        tokenToExpr(t)
    }
  }

  @Override
  override def constructList1[A](ptree: NodeOrLeaf[Token], constructor: NodeOrLeaf[Token] => A, hasComma: Boolean): List[A] =
    ptree match {
      case Node(_, List(t)) => List(constructor(t))
      case Node(_, List(t, ts)) =>
        constructor(t) :: constructList1(ts, constructor, hasComma)
      case Node(_, List(t, Leaf(COMMA()), ts)) if hasComma =>
        constructor(t) :: constructList1(ts, constructor, hasComma)
      case _ => Nil
    }




}

