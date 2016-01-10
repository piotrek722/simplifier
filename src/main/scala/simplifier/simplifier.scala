package simplifier

import AST._

// to implement
// avoid one huge match of cases
// take into account non-greedy strategies to resolve cases with power laws
//Od szczególnych do ogólnych
object Simplifier {

  def simplify(node: Node): Node = node match{

    case list@NodeList(_) => simplifyNodeList(list)
    case unary@Unary(_,_) => simplifyUnary(unary)
    case bin@BinExpr(_,_,_) => simplifyBinary(bin)
    case _ => node
  }

  def simplifyNodeList(mylist: NodeList): Node = {
    mylist.list match{
      case List(node@NodeList(_)) => simplify(node)
      case _ => new NodeList(mylist.list.map(x => simplify(x)).filter(_ != null))
    }
  }

  def simplifyUnary(unary: Unary): Node = (simplify(unary.expr), unary.op) match {

    case (TrueConst(), "not") => FalseConst()
    case (FalseConst(), "not") => TrueConst()
    case (u@Unary("not",_), "not" ) => u.expr
    case (u@Unary("+",_), "+" ) => u.expr
    case (u@Unary("-",_), "-" ) => u.expr
    case (b@BinExpr(_,_,_),"not") if b.op == "==" => simplify(BinExpr("!=",b.left,b.right))
    case (b@BinExpr(_,_,_),"not") if b.op == "!=" => simplify(BinExpr("==",b.left,b.right))
    case (b@BinExpr(_,_,_),"not") if b.op == "<=" => simplify(BinExpr(">",b.left,b.right))
    case (b@BinExpr(_,_,_),"not") if b.op == ">=" => simplify(BinExpr("<",b.left,b.right))
    case (b@BinExpr(_,_,_),"not") if b.op == "<" => simplify(BinExpr(">=",b.left,b.right))
    case (b@BinExpr(_,_,_),"not") if b.op == ">" => simplify(BinExpr("<=",b.left,b.right))
    case _ => Unary(unary.op, simplify(unary.expr))
  }

  /*
    val unary = Map("not"->4,
                  "+"->12,  "-"->12)
 */

  def simplifyBinary(bin: BinExpr): Node =  (simplify(bin.left), simplify(bin.right), bin.op)  match {

    case (n@IntNum(_), m@IntNum(_), "+") => IntNum(n.value + m.value)
    case (n@IntNum(_), m@IntNum(_), "-") => IntNum(n.value - m.value)
    case (n@IntNum(_), m@IntNum(_), "*") => IntNum(n.value * m.value)
    case (n@IntNum(_), m@IntNum(_), "/") if m.value != 0 => FloatNum(n.value / m.value)
    case (n@IntNum(_), m@IntNum(_), "%") => IntNum(n.value % m.value)

    case (n@FloatNum(_), m@FloatNum(_), "+") => FloatNum(n.value + m.value)
    case (n@FloatNum(_), m@FloatNum(_), "-") => FloatNum(n.value - m.value)
    case (n@FloatNum(_), m@FloatNum(_), "*") => FloatNum(n.value * m.value)
    case (n@FloatNum(_), m@FloatNum(_), "/")  if m.value != 0 => FloatNum(n.value / m.value)
    case (n@FloatNum(_), m@FloatNum(_), "%") => FloatNum(n.value % m.value)

    case (n@IntNum(_), m@FloatNum(_), "+") => FloatNum(n.value + m.value)
    case (n@IntNum(_), m@FloatNum(_), "-") => FloatNum(n.value - m.value)
    case (n@IntNum(_), m@FloatNum(_), "*") => FloatNum(n.value * m.value)
    case (n@IntNum(_), m@FloatNum(_), "/")  if m.value != 0 => FloatNum(n.value / m.value)
    case (n@IntNum(_), m@FloatNum(_), "%") => FloatNum(n.value % m.value)

    case (n@FloatNum(_), m@FloatNum(_), "+") => FloatNum(n.value + m.value)
    case (n@FloatNum(_), m@FloatNum(_), "-") => FloatNum(n.value - m.value)
    case (n@FloatNum(_), m@FloatNum(_), "*") => FloatNum(n.value * m.value)
    case (n@FloatNum(_), m@FloatNum(_), "/")  if m.value != 0 => FloatNum(n.value / m.value)
    case (n@FloatNum(_), m@FloatNum(_), "%") => FloatNum(n.value % m.value)

    case (v@Variable(_),x@Variable(_),"=="|">="|"<=") if v.name == x.name => TrueConst()
    case (v@Variable(_),x@Variable(_),"!="|"<"|">") if v.name == x.name => FalseConst()

    case (v@Variable(_),x@Variable(_),"-") if v.name == x.name => IntNum(0)

    case (v@Variable(_),n@IntNum(_),"+" | "-") if n.value == 0 => v
    case (n@IntNum(_),v@Variable(_),"+" | "-") if n.value == 0 => v

    case (v@Variable(_),n@IntNum(_),"*") if n.value == 1 => v
    case (n@IntNum(_),v@Variable(_),"*") if n.value == 1 => v

    case (v@Variable(_),n@IntNum(_),"*") if n.value == 0 => IntNum(0)
    case (n@IntNum(_),v@Variable(_),"*") if n.value == 0 => IntNum(0)

    case (v@Variable(_),x@Variable(_),"/") if v.name == x.name => IntNum(1)

    case (v@Variable(_),x@Variable(_),"or") if v.name == x.name => x
    case (v@Variable(_),x@Variable(_),"and") if v.name == x.name => x

    case (v@Variable(_),FalseConst(),"or") => v
    case (FalseConst(),v@Variable(_),"or") => v
    case (v@Variable(_),TrueConst(),"or") => TrueConst()
    case (TrueConst(),v@Variable(_),"or") => TrueConst()

    case (v@Variable(_),FalseConst(),"and") => FalseConst()
    case (FalseConst(),v@Variable(_),"and") => FalseConst()
    case (v@Variable(_),TrueConst(),"and") => v
    case (TrueConst(),v@Variable(_),"and") => v


    case (u@Unary("-",_),v@_,"+") => simplify(BinExpr("-",v,u.expr))

    case (a@Tuple(_),b@Tuple(_),"+") => Tuple(a.list ++ b.list)
    case (a@ElemList(_),b@ElemList(_),"+") => ElemList(a.list ++ b.list)

    case (v@_,u@_,o@_) => BinExpr(o, v, u)

  }




}


/*
Przykłady optymalizacji:

Ewaluacja wyrażeń stałych:
2+3*5 ⇒ 18
Optymalizacje wykorzystujące prawa matematyczne:
x+0 ⇒ x
x and False ⇒ False
x>x ⇒ False
not x==y ⇒ x!=y
Wykrywanie zduplikowanych kluczy w słowniku:
{ "a": 1, "b": 2, "a": 3 } ⇒ { "a": 3, "b": 2 }
Konkatenacja list:
[a,b,c]+[x,y] ⇒ [a,b,c,x,y]
Konkatenacja krotek:
(a,b,c)+(x,y) ⇒ (a,b,c,x,y)
Eliminacja zbędnych instrukcji:
x=x =>
'Peephole optimization':
x=a; x=b => x=b
 */