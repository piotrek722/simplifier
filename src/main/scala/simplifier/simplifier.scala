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
    case assign@Assignment(_,_) => simplifyAssignment(assign)
    case wh@WhileInstr(_,_) => simplifyWhile(wh)
    case singleIf@IfInstr(_,_) => simplifySingleIf(singleIf)
    case ifElifElse@IfElifElseInstr(_,_,_,_) => simplifyIfElifElse(ifElifElse)
    case ifElse@IfElseInstr(_,_,_) => simplifyIfElse(ifElse)
    case ifElif@IfElifInstr(_,_,_) => simplifIfElif(ifElif)
    case ifExpr@IfElseExpr(_,_,_) => simplifyIfExpr(ifExpr)
    case dic@KeyDatumList(_) => simplifyDictiorany(dic)
    case _ => node
  }

  def simplifyNodeList(mylist: NodeList): Node = mylist.list match{

    case List(node@NodeList(_)) => simplify(node)
    case _ => NodeList(mylist.list.map(x => simplify(x)).filter(_ != null))
  }


  def simplifyUnary(unary: Unary): Node = (simplify(unary.expr), unary.op) match {

    case (TrueConst(), "not") => FalseConst()
    case (FalseConst(), "not") => TrueConst()

    case (u@Unary("not",_), "not" ) => u.expr
    case (u@Unary("+",_), "+" ) => u.expr
    case (u@Unary("-",_), "-" ) => u.expr

    case (b@BinExpr("==",_,_),"not") => simplify(BinExpr("!=",b.left,b.right))
    case (b@BinExpr("!=",_,_),"not") => simplify(BinExpr("==",b.left,b.right))
    case (b@BinExpr("<=",_,_),"not") => simplify(BinExpr(">",b.left,b.right))
    case (b@BinExpr(">=",_,_),"not") => simplify(BinExpr("<",b.left,b.right))
    case (b@BinExpr("<",_,_),"not") => simplify(BinExpr(">=",b.left,b.right))
    case (b@BinExpr(">",_,_),"not") => simplify(BinExpr("<=",b.left,b.right))

    case _ => Unary(unary.op, simplify(unary.expr))
  }

  def simplifyBinary(bin: BinExpr): Node =  (simplify(bin.left), simplify(bin.right), bin.op)  match {

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


    case (BinExpr("*",l@Variable(_),r@IntNum(_)),x@Variable(_),"+" | "-") if l.name == x.name =>
      simplify(BinExpr("*",l,BinExpr(bin.op,r,IntNum(1))))

    case (BinExpr("*",l@IntNum(_),r@Variable(_)),x@Variable(_),"+" | "-") if r.name == x.name =>
      simplify(BinExpr("*",x,BinExpr(bin.op,l,IntNum(1))))

    case (BinExpr("*",x,z1),BinExpr("*",y,z2),"+" | "-") if z1 == z2 =>
      simplify(BinExpr("*",BinExpr(bin.op,x,y),z1))

    case (BinExpr("*",x1,y),BinExpr("*",x2,z),"+" | "-") if x1 == x2 =>
      simplify(BinExpr("*",x1,BinExpr(bin.op,y,z)))

    case (BinExpr("+" ,BinExpr("*",x1,y1),BinExpr("*",x2,z1)),BinExpr("+" ,BinExpr("*",v1,y2),BinExpr("*",v2,z2)), "+") =>
      simplify(BinExpr("*",BinExpr("+",x1,v1),BinExpr("+",y1,z1)))

      /*
      "understand distributive property of multiplication" in {
      parseString("2*x-x") mustEqual parseString("x")
      parseString("x*z+y*z") mustEqual parseString("(x+y)*z")
      parseString("x*y+x*z") mustEqual parseString("x*(y+z)")
      parseString("x*y+x*z+v*y+v*z") mustEqual parseString("(x+v)*(y+z)")
    }
       */



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

  def simplifyDictiorany(dic: KeyDatumList): Node = dic match {
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