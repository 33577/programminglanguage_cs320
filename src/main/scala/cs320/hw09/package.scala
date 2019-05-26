package cs320

package object hw09 extends Homework09 {
  trait CORELValue
  case class NumV(n: Int) extends CORELValue
  case class BoolV(b: Boolean) extends CORELValue
  case class CloV(param: String, body: COREL, var env: Env) extends CORELValue
  case class VariantV(name: String, value: CORELValue) extends CORELValue
  case class ConstructorV(name: String) extends CORELValue

  type Env = Map[String, CORELValue]
  type Cont = CORELValue => CORELValue
  // type TypeEnv = Map[String, Type]
  case class TypeEnv(
      vars  : Map[String, Type] = Map(),
      tbinds: Map[String, Map[String, Type]] = Map()
  ){
    def addVar(x: String, t: Type): TypeEnv =
        copy(vars = vars + (x -> t))
    def addVarsFromMap(m: Map[String, Type]): TypeEnv =
        copy(vars = vars ++ m)
    def addTBind(x: String, cs: Map[String, Type]): TypeEnv =
      copy(tbinds = tbinds + (x -> cs))
  }


  def notype(msg: Any): Nothing = error(s"no type: $msg")
  def mustSameList(l: List[Type]): Type = 
    if (l.length == 0) notype(s"$l is empty")
    else if (l.length == 1) l(0)
    else {
      val f::rest = l
      mustSame(f, rest(0))
      mustSameList(rest)
    }
  def mustSame(left: Type, right: Type): Type =
    if (same(left, right)) left
    else notype(s"$left is not equal to $right")
  def same(left: Type, right: Type): Boolean =
    (left, right) match {
      case (NumT, NumT) => true
      case (BoolT, BoolT) => true
      case (ArrowT(p1, r1), ArrowT(p2, r2)) =>
        same(p1, p2) && same(r1, r2)
      case (IdT(x), IdT(y)) => x==y
      case _ => false
    }
  
  // numOp: ((Int, Int) => Int) => (CORELValue, CORELValue) => CORELValue
  def numOp(op: (Int, Int) => Int): (CORELValue, CORELValue) => CORELValue = (_, _) match {
    case (NumV(x), NumV(y)) => NumV(op(x, y))
    case (x, y) => error(s"not both numbers: $x, $y")
  }
  val numAdd = numOp(_ + _)
  val numSub = numOp(_ - _)

  // find name in env. If there is, imthrow value of name. Else, then raise error.
  def lookup(name: String, env: Env): CORELValue = 
    env.get(name) match {
      case Some(v) => v
      case None => error(s"free identifier: $name")
    }

  def typeCheckwithTyEnv(corel: COREL, tyEnv: TypeEnv): Type = corel match {
    case Num(_) => NumT
    case Bool(_) => BoolT
    case Add(l, r) =>
      mustSame(typeCheckwithTyEnv(l, tyEnv), NumT)
      mustSame(typeCheckwithTyEnv(r, tyEnv), NumT)
      NumT
    case Sub(l, r) =>
      mustSame(typeCheckwithTyEnv(l, tyEnv), NumT)
      mustSame(typeCheckwithTyEnv(r, tyEnv), NumT)
      NumT
    case Equ(l, r) => 
      mustSame(typeCheckwithTyEnv(l, tyEnv), NumT)
      mustSame(typeCheckwithTyEnv(r, tyEnv), NumT)
      BoolT
    case With(name, t, expr, body) => typeCheckwithTyEnv(body, tyEnv.addVar(name, t))
    case Id(x) => tyEnv.vars.getOrElse(x, notype(s"$x is a free identifier")) // tbinds에 x가 있는 경우는 체크 안 해도 되나? 
    case Fun(p, pt, b) => ArrowT(pt, typeCheckwithTyEnv(b, tyEnv.addVar(p, pt)))
    case App(f, a) =>
      val funT = typeCheckwithTyEnv(f, tyEnv)
      val argT = typeCheckwithTyEnv(a, tyEnv)
      funT match {
        case ArrowT(param, result)
          if same(argT, param) => result
        case _ => notype(s"apply $argT to $funT")
      }
    case IfThenElse(ce, te, ee) => 
      mustSame(typeCheckwithTyEnv(ce, tyEnv), BoolT)
      mustSame(typeCheckwithTyEnv(te, tyEnv), typeCheckwithTyEnv(te, tyEnv))
    case Rec(fname, fty, pname, pty, body) =>
      val newTyEnv = TypeEnv(tyEnv.vars + (fname->fty) + (pname->pty), tyEnv.tbinds)
      mustSame(fty, ArrowT(pty, 
                              typeCheckwithTyEnv(body, newTyEnv)))
    case WithType(name, constructors, body) => 
      val tyEnvT = tyEnv.addTBind(name, constructors)
      // val newTyEnv = TypeEnv( tyEnvT.vars ++ constructors map { case (v, t) => (v, ArrowT(t, IdT(name)))}, tyEnvT.tbinds )
      // typeCheckwithTyEnv(body, newTyEnv)
      val tyEnvV = tyEnvT.addVarsFromMap(constructors map { case (v, t) => (v, ArrowT(t, IdT(name))) })
      typeCheckwithTyEnv(body, tyEnvV)
    case Cases(name, dispatchE, cases) =>  
      val cs = tyEnv.tbinds.getOrElse(name, notype(s"[TC/tbinds] $name is a free type"))
      mustSame(typeCheckwithTyEnv(dispatchE, tyEnv), IdT(name))

      val returnTypes: List[Type] = cases.map { 
        case (x, (v, e)) => typeCheckwithTyEnv(e, tyEnv.addVar(v, cs.getOrElse(x, notype(s"[TC] $x is a free type"))))} toList
      // check every returnTypes[i] is same with returnTypes[i-1]
      
      val kkk = 2 // 의미없는 거 근데 이 줄이 없으면 에러 남  왜?
      mustSameList(returnTypes)
      
  }

  def e2v(corel: COREL, env: Env): CORELValue = corel match {
    case Num(num) => NumV(num)
    case Bool(b) => BoolV(b)
    case Add(left, right) => numAdd(e2v(left, env), e2v(right, env))
    case Sub(left, right) => numSub(e2v(left, env), e2v(right, env))
    case Equ(left, right) => BoolV(e2v(left, env) == e2v(right, env))
    case With(name, _, expr, body) => e2v(body, env + (name -> e2v(expr, env)))
    case Id(name) => lookup(name, env)
    case Fun(param, _, body) => CloV(param, body, env)
    case App(f, a) => 
      val fv = e2v(f, env)
      fv match {
        case CloV(param, body, fenv) => e2v(body, fenv + (param -> e2v(a, env)))
        case ConstructorV(name) => VariantV(name, e2v(a, env))
        case v => error(s"not a closure or constructor: $v")
      }
    case IfThenElse(ce, te, ee) => 
      val cond = e2v(ce, env)
      if (cond == BoolV(true)) e2v(te, env)
      else e2v(ee, env)
    case Rec(fname, _, pname, _, body) => 
      val cloV = CloV(pname, body, env)
      cloV.env = env + (fname -> cloV)
      cloV
    case WithType(name, constructors, body) => 
      val newEnv = env ++ constructors map { case (v, t) => (v, ConstructorV(v)) }
      e2v(body, newEnv)
    case Cases(c, dispatchE, cases) => // cases: Map(x, (v, e))
      e2v(dispatchE, env) match {
        case VariantV(name, av) => 
          val (y, e) = cases(name)
          e2v(e, env + (y->av))
        case v => error(s"not a variant: $v")      
      }
  }

  def typeCheck(str: String): Type = typeCheckwithTyEnv(COREL(str), TypeEnv())
  def interp(str: String): String = {
    e2v(COREL(str), Map()) match {
      case NumV(n) => n.toString
      case BoolV(b) => b.toString
      case CloV(param, body, env) => "function"
    }
  }
  




  def tests: Unit = {
    test(run("42"), "42")
    test(run("true"), "true")
    test(run("{+ 1 2}"), "3")
    test(run("{- 2 1}"), "1")
    test(run("{= 1 0}"), "false")
    testExc(run("{= true 0}"), "no type")
    test(run("{with {x : num 1} x}"), "1")
    test(run("{{fun {x : num} {+ x 1}} 2}"), "3")
    test(run("""
      {{recfun {f: {num -> num} x: num}
               {if {= x 0} 0 {+ {f {- x 1}} x}}}
       10}"""), "55")
    testExc(run("{if 1 2 3}"), "no type")
    test(run("""
      {withtype
        {fruit {apple num}
               {banana num}}
        {cases fruit {apple 1}
               {apple {x} x}
               {banana {y} y}}}"""), "1")
    testExc(run("""
      {withtype
        {fruit {apple num}
               {banana num}}
        {cases fruit {apple 1}
               {apple {x} x}}}"""), "not all cases")

    /* Write your own tests */
    test(run("""
      {withtype
        {fruit {apple num}
               {banana num}}
        {cases fruit {apple 1}
               {apple {x} {+ x 1}}
               {banana {y} y}}}"""), "1")
  }
}
