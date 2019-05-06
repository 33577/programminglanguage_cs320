package cs320

package object hw07 extends Homework07 {
  trait KXCFAEValue
  case class NumV(n: Int) extends KXCFAEValue
  case class CloV(params: List[String], body: KXCFAE, env: Env) extends KXCFAEValue
  case class ContV(proc: Cont) extends KXCFAEValue

  type Env = Map[String, KXCFAEValue]
  type Cont = KXCFAEValue => KXCFAEValue
  
  // numOp: ((Int, Int) => Int) => (KXCFAEValue, KXCFAEValue) => KXCFAEValue
  def numOp(op: (Int, Int) => Int): (KXCFAEValue, KXCFAEValue) => KXCFAEValue = (_, _) match {
    case (NumV(x), NumV(y)) => NumV(op(x, y))
    case (x, y) => error(s"not both numbers: $x, $y")
  }
  val numAdd = numOp(_ + _)
  val numSub = numOp(_ - _)

  // find name in env. If there is, return value of name. Else, then raise error.
  def lookup(name: String, env: Env): KXCFAEValue = 
    env.get(name) match {
      case Some(v) => v
      case None => error(s"free identifier: $name")
    }

  def interp(KXCFAE: KXCFAE, env: Env, k: Cont): KXCFAEValue = KXCFAE match {
    case Num(num) => k(NumV(num))
    case Add(l, r) => 
      interp(l, env, lv => 
                        interp(r, env, rv => 
                                          k(numAdd(lv, rv))))
    case Sub(l, r) =>
      interp(l, env, lv => 
                        interp(r, env, rv => 
                                          k(numSub(lv, rv))))
    case Id(name) => k(lookup(name, env))
    case Fun(params, body) => k(CloV(params, body, env))
    case App(f, args) =>                                   
      interp(f, env, fv => 
                        help(List(), args, env, fv, k)
      )
    case Withcc(name, body) => interp(body, env+(name->ContV(k)), k)

  }

  def help(previousValueList: List[KXCFAEValue], remainExprList: List[KXCFAE], env: Env, fv: KXCFAEValue, k: Cont): KXCFAEValue = remainExprList match {
    case e::rest => interp(e, env, ev => {
                                      val newPVL = previousValueList :+ ev   // list 끝에 ev 넣기
                                      help(newPVL, rest, env, fv, k)
    })
    case Nil => fv match {
          case CloV(params, body, fenv) => 
            if (params.size != previousValueList.size ) error(s"wrong arity")
            interp(body, fenv ++ (params zip previousValueList toMap ), k)
          case ContV(kv) => kv(previousValueList(0))                                  // 아 이거 어카냐 ㅋㅋ
          case v => error(s"Not a closure or Continuation: $v")
    }
  }

  // KXCFAEValue => String
  def eval(kValue: KXCFAEValue): String = {
    kValue match {
      case NumV(n) => n.toString
      case CloV(param, body, env) => "function"
      case ContV(proc) => "continuation"
    }
  }

  def run(str: String): String = eval(interp(KXCFAE(str), Map(), x=>x))

  def tests: Unit = {
    test(run("{{fun {x y} {- y x}} 10 12}"), "2")
    test(run("{fun {} 12}"), "function")
    testExc(run("{{fun {x y} 1} 2}"), "wrong arity")
    test(run("{withcc esc {{fun {x y} x} 1 {esc 3}}}"), "3")

    // test(run("{try 1 catch 2}"), "1")
    // test(run("{try {throw} catch 2}"), "2")
    // test(run("{try {+ 1 {throw}} catch 2}"), "2")
    // test(run("{{fun {f} {try {f} catch 1}} {fun {} {throw}}}"), 1) testExc(run("{throw}"), "no enclosing try-catch")
    /* Write your own tests */
    test(run("{withcc esc {{fun {x y} x} 1 {esc 3 5}}}"), "3 5")
    test(run("{+ 1 {withcc k {{fun {x y} {+ x y}} {k 2} 4}}}"), "3")
  }
}
