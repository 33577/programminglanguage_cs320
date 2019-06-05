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

  def validType(ty: Type, tyEnv: TypeEnv): Type = ty match {
    case NumT => ty
    case BoolT => ty
    case ArrowT(p, r) =>
      ArrowT(validType(p, tyEnv), validType(r, tyEnv))
    case IdT(x) =>
      if (tyEnv.tbinds.contains(x)) ty
      else notype(s"$x is a free type")
  }

  def occurs(t1: IdT, t2: Type): Boolean = 
    t2 match {
      case NumT => false
      case BoolT => false
      case ArrowT(l, r) => occurs(t1, l) || occurs(t1, r)
      case IdT(ty) => t1.name == ty
  }

  // 순서를 고려하지 않고 ele가 같은지 검사 
  def sameSet(l1: List[String], l2: List[String]): Boolean = 
    if (l1.size!=l2.size) false
    else if (l1.size == 1) l1(0) == l2(0) 
    else l1 match {
      case f::rest => l2.contains(f) && sameSet(rest, l2 diff List(f))
      case _ => error(s"error on sameSet")
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
    case With(name, t, expr, body) => 
      validType(t, tyEnv)
      typeCheckwithTyEnv(body, tyEnv.addVar(name, t))
    case Id(x) => tyEnv.vars.getOrElse(x, notype(s"$x is a free identifier"))
    case Fun(p, pt, b) => 
      validType(pt, tyEnv)
      ArrowT(pt, typeCheckwithTyEnv(b, tyEnv.addVar(p, pt)))
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
      mustSame(typeCheckwithTyEnv(te, tyEnv), typeCheckwithTyEnv(ee, tyEnv))
    case Rec(fname, fty, pname, pty, body) =>
      validType(fty, tyEnv)
      validType(pty, tyEnv)
      val newTyEnv = TypeEnv(tyEnv.addVar(fname, fty).addVar(pname, pty).vars, tyEnv.tbinds)
      mustSame(fty, ArrowT(pty, 
                              typeCheckwithTyEnv(body, newTyEnv)))
    case WithType(name, constructors, body) =>  
      val tyEnvT = tyEnv.addTBind(name, constructors)
      val tyEnvV = tyEnvT.addVarsFromMap(constructors map { case (v, t) => 
        validType(t, tyEnvT);
        (v, ArrowT(t, IdT(name))) 
      })
      val bodyT = typeCheckwithTyEnv(body, tyEnvV)

      // Soundness check
      if (!occurs(IdT(name), bodyT)) bodyT
      else error(s"[TC/WithType] No new type in body type")

    case Cases(name, dispatchE, cases) =>  
      val cs = tyEnv.tbinds.getOrElse(name, notype(s"[TC/Cases/tbinds] $name is a free type"))
      mustSame(typeCheckwithTyEnv(dispatchE, tyEnv), IdT(name))

      val returnTypes: List[Type] = cases.map { // (x, (v, e)) (variant, (param, body))
        case (x, (v, e)) => typeCheckwithTyEnv(e, tyEnv.addVar(v, cs.getOrElse(x, notype(s"[TC] $x is a free type"))))} toList
      
      // not all cases  위에서 tbinds에 있는 것만 나오는게 확정 되었으므로 갯수만 체크해도 된다.
      if (cs.size != cases.size) error(s"not all cases")

      // check every returnTypes[i] is same with returnTypes[i-1]
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
          // val (y, e) = cases(name)
          val (y, e) = cases.getOrElse(name, error(s"[Intp] no such case")) 
          e2v(e, env + (y->av))
        case v => error(s"not a variant: $v")      
      }
  }

  def typeCheck(str: String): Type = typeCheckwithTyEnv(COREL(str), TypeEnv())
  def interp(str: String): String = {
    e2v(COREL(str), Map()) match {
      case NumV(n) => n.toString
      case BoolV(b) => b.toString
      case CloV(_,_,_) => "function"
      case VariantV(_, _) => "variant"
      case ConstructorV(_) => "constructor"
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
               {banana {y} y}}}"""), "2")
    testExc(run("""
      {withtype
        {fruit {apple num}
               {banana num}}
        {cases fruit {gam 1}
               {apple {x} {+ x 1}}
               {banana {y} y}}}"""), "no type") // gam is free identifier
    test(run("""
      {withtype
        {fruit {apple num}
               {banana num}
               {gam bool}}
        {cases fruit {gam true}
               {apple {x} false}
               {banana {y} false}
               {gam {x} x}
               }}"""), "true")
    testExc(run("""
      {withtype
        {fruit {apple num}
               {banana num}
               {gam bool}}
        {cases fruit {gam true}
               {apple {x} {+ x 1}}
               {banana {y} y}
               {gam {x} x}
               }}"""), "no type")
    testExc(run("{fun {x: a} x}"), "no type")
    testExc(run("{if true 1 false}"), "no type")
    // test(run("{withtype {fruit {apple num}} apple}"), "constructor")
    testExc(run("{withtype {fruit {apple num}} apple}"), "[TC/WithType] No new type in body type")
    test(run("{withtype {fruit {apple num}} 1}"), "1")
    testExc(run("{withtype {fruit {apple num}} fruit}"), "no type") // error

    test(run("{{recfun {f: {num -> num} x: num} {if {= x 0} 0 {+ x {f {- x 1}}}}} 10}"), "55")
    
    testExc(run("""
      {{withtype {foo {a num} {b num}}
           {fun {x : foo}
                {cases foo x
                   {a {n} {+ n 3}}
                   {b {n} {+ n 4}}}}}
          {withtype {foo {c num} {d num}}
           {c 1}}}"""), "[TC/WithType] No new type in body type")
    testExc(run("""
      {{withtype {foo {a num} {b num}}
           {fun {x : foo}
                {cases foo x
                   {a {n} {+ n 3}}
                   {b {n} {+ n 4}}}}}
          {withtype {foo {c {num -> num}} {d num}}
           {c {fun {y : num} y}}}}"""), "[TC/WithType] No new type in body type")

    testExc(run("""
      {withtype
        {fruit {apple num}
               {banana num}
               {gam bool}}
        {cases fruit {gam true}
               {apple {x} 1}
               {banana {x} true}
               {gam {x} 1}
               }}"""), "no type")

    test(run("""
      {withtype
        {fruit {apple bool}
               {banana num}
               }
        {
          withtype
          {fruit {gam num}
                 {apple num} }
          {cases fruit {gam 1}
                 {gam {x} x}
                 {apple {x} x}}
          }
        }"""), "1")

    testExc(run("""
      {withtype
        {fruit {apple num}
               {banana num}}
        {cases fruit {apple 1}
               {apple {x} x}
               {appl {x} {+ x 1}}
               }}"""), "no type")
    testExc(run("""
      {withtype
        {fruit {apple num}
               {banana num}}
        {cases fruit {apple 1}
               {apple {x} x}
               {apple {x} {+ x 1}}
               }}"""), "not all cases")
    test(run("{with {x : num 1} x}"), "1")

    test(run("{with {podo : {num -> num} {fun {x: num} 3}} 1}"), "1")
    testExc(run(
        """{ with {podo : {num -> num} {fun {x: num} 3}} 
          {withtype {fruit {apple num} {banana num}}
            {cases fruit {apple 1}
                   {apple {x} 1}
                   {podo {x} 2}
            }
        }}
    """), "no type") // 개수는 같은데 not all cases 오류 내야 하는 경우를 만들 수 있을까? 없는거 같아

    //piazza
    testExc(run("""
    {withtype {fruit {apple num}
                          {banana num}}
    {withtype{food {apple num}
                            {banana bool}}
    {+
    {cases fruit {banana 4}
                      {apple {x} {+ x 4}}
                      {banana {x} {+ x 0}}}
    {cases food {banana true}
                      {apple {x} {+ x 10}}
                      {banana {x} {if x 10 0}}
    }}}}"""), "no type")

    // test functions
    test(occurs(IdT("t1"), IdT("t1")), true)

    test(sameSet(List("a", "b", "c"), List("a", "b", "c")), true)
    test(sameSet(List("a", "b", "c"), List("b", "c", "a")), true)

    test(sameSet(List("a", "b", "c"), List("a", "b", "b")), false)
    test(sameSet(List("a", "b"), List("a", "b", "c")), false)
    test(sameSet(List("a", "b", "c"), List("a", "b", "d")), false)

  }
}
