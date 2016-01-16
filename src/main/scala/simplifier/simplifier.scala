package simplifier

import AST._
import scala.math.pow

// to implement
// avoid one huge match of cases
// take into account non-greedy strategies to resolve cases with power laws
//Od szczególnych do ogólnych
object Simplifier {

  def simplify(node: Node): Node = node match{

    case list@NodeList(_) => simplifyNodeList(list)
    case unary@Unary(_,_) => simplifyUnary(unary)
    case bin@BinExpr(_,_,_) => simplifyBinary(bin)
    case assign@Assignment(_,_) => simplifyAssignment(assign)
    case wh@WhileInstr(_,_) => simplifyWhile(wh)
    case singleIf@IfInstr(_,_) => simplifySingleIf(singleIf)
    case ifElifElse@IfElifElseInstr(_,_,_,_) => simplifyIfElifElse(ifElifElse)
    case ifElse@IfElseInstr(_,_,_) => simplifyIfElse(ifElse)
    case ifElif@IfElifInstr(_,_,_) => simplifIfElif(ifElif)
    case ifExpr@IfElseExpr(_,_,_) => simplifyIfExpr(ifExpr)
    case dic@KeyDatumList(_) => simplifyDictionary(dic)
    case _ => node
  }

  def simplifyNodeList(mylist: NodeList): Node = mylist.list match{

    case List(Assignment(x1,a),Assignment(x2,b)) if x1 == x2 => simplify(NodeList(List(Assignment(x2,b))))

    case List(node@NodeList(_)) => simplify(node)
    case _ => NodeList(mylist.list.map(x => simplify(x)).filter(_ != null))
  }


  def simplifyUnary(unary: Unary): Node = (simplify(unary.expr), unary.op) match {

    case (TrueConst(), "not") => FalseConst()
    case (FalseConst(), "not") => TrueConst()

      // "cancel double unary ops"
    case (u@Unary("not",_), "not" ) => u.expr
    case (u@Unary("+",_), "+" ) => u.expr
    case (u@Unary("-",_), "-" ) => u.expr

      //"get rid of not before comparisons"
    case (b@BinExpr("==",_,_),"not") => simplify(BinExpr("!=",b.left,b.right))
    case (b@BinExpr("!=",_,_),"not") => simplify(BinExpr("==",b.left,b.right))
    case (b@BinExpr("<=",_,_),"not") => simplify(BinExpr(">",b.left,b.right))
    case (b@BinExpr(">=",_,_),"not") => simplify(BinExpr("<",b.left,b.right))
    case (b@BinExpr("<",_,_),"not") => simplify(BinExpr(">=",b.left,b.right))
    case (b@BinExpr(">",_,_),"not") => simplify(BinExpr("<=",b.left,b.right))

    case _ => Unary(unary.op, simplify(unary.expr))
  }

  def simplifyBinary(bin: BinExpr): Node =  (simplify(bin.left), simplify(bin.right), bin.op)  match {

      //"simplify expressions"
    case (n@IntNum(_), m@IntNum(_), "+") => IntNum(n.value + m.value)
    case (n@IntNum(_), m@IntNum(_), "-") => IntNum(n.value - m.value)
    case (n@IntNum(_), m@IntNum(_), "*") => IntNum(n.value * m.value)
    case (n@IntNum(_), m@IntNum(_), "/") if m.value != 0 => FloatNum(n.value / m.value)
    case (n@IntNum(_), m@IntNum(_), "%") if m.value != 0 => IntNum(n.value % m.value)

    case (n@FloatNum(_), m@FloatNum(_), "+") => FloatNum(n.value + m.value)
    case (n@FloatNum(_), m@FloatNum(_), "-") => FloatNum(n.value - m.value)
    case (n@FloatNum(_), m@FloatNum(_), "*") => FloatNum(n.value * m.value)
    case (n@FloatNum(_), m@FloatNum(_), "/") if m.value != 0 => FloatNum(n.value / m.value)
    case (n@FloatNum(_), m@FloatNum(_), "%") if m.value != 0 => FloatNum(n.value % m.value)

    case (n@IntNum(_), m@FloatNum(_), "+") => FloatNum(n.value + m.value)
    case (n@IntNum(_), m@FloatNum(_), "-") => FloatNum(n.value - m.value)
    case (n@IntNum(_), m@FloatNum(_), "*") => FloatNum(n.value * m.value)
    case (n@IntNum(_), m@FloatNum(_), "/") if m.value != 0 => FloatNum(n.value / m.value)
    case (n@IntNum(_), m@FloatNum(_), "%") if m.value != 0 => FloatNum(n.value % m.value)

    case (n@FloatNum(_),  m@IntNum(_), "+") => FloatNum(n.value + m.value)
    case (n@FloatNum(_),  m@IntNum(_), "-") => FloatNum(n.value - m.value)
    case (n@FloatNum(_),  m@IntNum(_), "*") => FloatNum(n.value * m.value)
    case (n@FloatNum(_),  m@IntNum(_), "/") if m.value != 0 => FloatNum(n.value / m.value)
    case (n@FloatNum(_),  m@IntNum(_), "%") if m.value != 0 => FloatNum(n.value % m.value)

    case (v@Variable(_),x@Variable(_),"=="|">="|"<=") if v.name == x.name => TrueConst()
    case (v@Variable(_),x@Variable(_),"!="|"<"|">") if v.name == x.name => FalseConst()

    case (v@Variable(_),x@Variable(_),"-") if v.name == x.name => IntNum(0)

    case (v@Variable(_),n@IntNum(_),"+" | "-") if n.value == 0 => v
    case (n@IntNum(_),v@Variable(_),"+" | "-") if n.value == 0 => v

    case (v@Variable(_),n@IntNum(_),"*") if n.value == 1 => v
    case (n@IntNum(_),v@Variable(_),"*") if n.value == 1 => v

    case (v@Variable(_),n@IntNum(_),"*") if n.value == 0 => IntNum(0)
    case (n@IntNum(_),v@Variable(_),"*") if n.value == 0 => IntNum(0)


    // x*2 + x = x*(2 + 1)
    case (BinExpr("*",l@Variable(_),r@IntNum(_)),x@Variable(_),"+" | "-") if l.name == x.name =>
      simplify(BinExpr("*",l,BinExpr(bin.op,r,IntNum(1))))

    case (BinExpr("*",l@IntNum(_),r@Variable(_)),x@Variable(_),"+" | "-") if r.name == x.name =>
      simplify(BinExpr("*",x,BinExpr(bin.op,l,IntNum(1))))

    case (BinExpr("*",x,z1),BinExpr("*",y,z2),"+" | "-") if z1 == z2 =>
      simplify(BinExpr("*",BinExpr(bin.op,x,y),z1))

    case (BinExpr("*",x1,y),BinExpr("*",x2,z),"+" | "-") if x1 == x2 =>
      simplify(BinExpr("*",x1,BinExpr(bin.op,y,z)))

    case (BinExpr("+",BinExpr("*",x1,BinExpr("+",y1,z1)),BinExpr("*",v1,y2)),BinExpr("*",v2,z2),"+") =>
      simplify(BinExpr("*",BinExpr("+",x1,v1),BinExpr("+",y1,z1)))

  //  case (x@Variable(_),y@Variable(_),"/") if x.name == y.name => IntNum(1)

    /*
  "simplify division"
    */

    case (BinExpr("+",x1,BinExpr("*",y1,z1)),BinExpr("+",x2,BinExpr("*",y2,z2)),"/")
      if x1 == x1 && y1==y2 && z1==z2 => IntNum(1)

    case (BinExpr("+",x1,y1),BinExpr("+",y2,x2),"/") if x1 == x2 && y1 == y2 => IntNum(1)

    case (n@IntNum(_),BinExpr("/",v@IntNum(_),x),"/") if n.value == 1 && v.value == 1 => simplify(x)

    case (n@IntNum(_),BinExpr("/",v@IntNum(_),BinExpr("-",x,y)),"/") if n.value == 1 && v.value == 1 =>
      simplify(BinExpr("-",x,y))

    case (x@Variable(_),BinExpr("/",v@IntNum(_),y),"*") if v.value == 1 => simplify(BinExpr("/",x,y))

    case (v@Variable(_),x@Variable(_),"/") if v.name == x.name => IntNum(1)

      // "understand commutativity"

    case (BinExpr("+",x,n@IntNum(_)),v@Variable(_),"-") if x == v => simplify(BinExpr("+",n,BinExpr("-",x,v)))

    case (BinExpr("or",a1,b1),BinExpr("or",b2,a2),"and") if a1 == a2 && b1 == b2 =>
      simplify(BinExpr("or",a1,b1))

    case (BinExpr("and",a1,b1),BinExpr("and",b2,a2),"or") if a1 == a2 && b1 == b2 =>
      simplify(BinExpr("and",a1,b1))

  //power laws
    case (BinExpr("**",x1,y),BinExpr("**",x2,z),"*") if x1 == x2 => simplify(BinExpr("**",x1,BinExpr("+",y,z)))

    case (BinExpr("**",a@IntNum(_),b@IntNum(_)),c@IntNum(_),"**") => simplify(BinExpr("**",a,simplify(BinExpr("**",b,c))))

    case (x@Variable(_),z@IntNum(_),"**") if z.value == 0 => IntNum(1)

    case (x@Variable(_),z@IntNum(_),"**") if z.value == 1 => simplify(x)

    case (BinExpr("**",x,n),m@Variable(_),"**") => simplify(BinExpr("**",x,BinExpr("*",n,m)))

    case (BinExpr("+",BinExpr("**",x1,a@IntNum(_)),BinExpr("*",BinExpr("*",b@IntNum(_),x2),y1)),BinExpr("**",y2,c@IntNum(_)),"+")
      if x1==x2 && y1==y2 && a.value==2 && b.value==2 && c.value==2 =>
      simplify(BinExpr("**",BinExpr("+",x1,y1),a))

    case (BinExpr("-",BinExpr("**",BinExpr("+",x1,y1),a@IntNum(_)),BinExpr("**",x2,b@IntNum(_))),BinExpr("*",BinExpr("*",c@IntNum(_),x3),y2),"-")
      if x1==x2 && x2==x3 && y1==y2 && a.value==2 && b.value==2 && c.value==2
    => simplify(BinExpr("**",y1,a))

    case (BinExpr("**",BinExpr("+",x1,y1),a@IntNum(_)),BinExpr("**",BinExpr("-",x2,y2),b@IntNum(_)),"-")
      if x1 == x2 && y1 == y2 => simplify(BinExpr("*",BinExpr("*", IntNum(a.value * b.value), x1),y1))

    case (a@IntNum(_),b@IntNum(_),"**") => IntNum(pow(b.value.toDouble,a.value.toDouble).intValue)

      
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

    case (l@_,r@_,o@_) => BinExpr(o, simplify(l), simplify(r) )

  }

  def simplifyAssignment(assign: Assignment): Node = (simplify(assign.left), simplify(assign.right)) match {

    case (x@_,y@_) if x == y => null
    case (x@_,y@_) => Assignment(simplify(x),simplify(y))

  }

  def simplifyWhile(wh: WhileInstr): Node = simplify(wh.cond) match {

    case FalseConst() => null;
    case _ => WhileInstr(simplify(wh.cond), simplify(wh.body))

  }

  def simplifySingleIf(singleIf: IfInstr): Node = simplify(singleIf.cond) match{

    case FalseConst() => null
    case _ => IfInstr(simplify(singleIf.cond), simplify(singleIf.left))

  }

  def simplifyIfElse(ifElse: IfElseInstr): Node =  simplify(ifElse.cond) match{

    case TrueConst() => simplify(ifElse.left)
    case FalseConst() => simplify(ifElse.right)
    case _ => IfElseInstr(simplify(ifElse.cond),simplify(ifElse.left), simplify(ifElse.right))

  }

  def simplifIfElif(ifElif: IfElifInstr): Node = simplify(ifElif.cond) match {

    case TrueConst() => simplify(ifElif.left)

    case FalseConst() if ifElif.elifs.size == 1 =>
      simplify(IfInstr(ifElif.elifs.head.cond, ifElif.elifs.head.left))

    case FalseConst() if ifElif.elifs.size > 1 =>
      simplify(IfElifInstr(ifElif.elifs.head.cond, ifElif.elifs.head.left, ifElif.elifs.drop(1)))

    case _ => IfElifInstr(simplify(ifElif.cond),simplify(ifElif.left), ifElif.elifs)

  }

  def simplifyIfElifElse(ifElifElse: IfElifElseInstr): Node = simplify(ifElifElse.cond) match {

    case TrueConst() => simplify(ifElifElse.left)

    case FalseConst() if ifElifElse.elifs.size == 1 =>
      simplify(IfInstr(ifElifElse.elifs.head.cond,ifElifElse.elifs.head.left))

    case FalseConst() if ifElifElse.elifs.size > 1 =>
      simplify(IfElifElseInstr(
        ifElifElse.elifs.head.cond,
        ifElifElse.elifs.head.left,
        ifElifElse.elifs.drop(1),
        ifElifElse.right))


    case _ => IfElifElseInstr(simplify(ifElifElse.cond), simplify(ifElifElse.left), ifElifElse.elifs, simplify(ifElifElse.right))

  }

  def simplifyIfExpr(ifExpr: IfElseExpr): Node = simplify(ifExpr.cond) match {

    case FalseConst() => simplify(ifExpr.right)
    case TrueConst() => simplify(ifExpr.left)
    case _ => IfElseExpr(simplify(ifExpr.cond), simplify(ifExpr.left), simplify(ifExpr.right))

  }

  def simplifyDictionary(dic: KeyDatumList): Node = dic match {
    case KeyDatumList(list) => KeyDatumList(list.foldLeft(Map.empty[Node, KeyDatum])(
      (map, kd) => map + (kd.key -> kd) // map[kd.key] = kd so we elemmiate duplicated
    ).toList.map(p => p._2))
    case _ => dic
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