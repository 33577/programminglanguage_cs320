package cs320

package object hw03 extends Homework03 {
  trait MRFWAEValue
  case class NumV(n: Int) extends MRFWAEValue
  case class CloV(params: List[String], body: MRFWAE, env: Env) extends MRFWAEValue
  case class RecV(rec: Map[String, MRFWAEValue]) extends MRFWAEValue

  type Env = Map[String, MRFWAEValue]

  // numOp: ((Int, Int) => Int) => (MRFWAEValue, MRFWAEValue) => MRFWAEValue
  def numOp(op: (Int, Int) => Int): (MRFWAEValue, MRFWAEValue) => MRFWAEValue = (_, _) match {
    case (NumV(x), NumV(y)) => NumV(op(x, y))
    case (x, y) => error(s"not both numbers: $x, $y")
  }
  val numAdd = numOp(_ + _)
  val numSub = numOp(_ - _)
  
  // find name in env. If there is, return value of name. Else, then raise error.
  def lookup(name: String, env: Env): MRFWAEValue = 
    env.get(name) match {
      case Some(v) => v
      case None => error(s"free identifier: $name")
    }

  def lookupRec(name: String, rec: Map[String, MRFWAEValue]): MRFWAEValue = 
    rec.get(name) match {
      case Some(v) => v
      case None => error(s"no such field")
    }

  def interp(mrfwae: MRFWAE, env: Env): MRFWAEValue = mrfwae match {
    case Num(num) => NumV(num)
    case Add(left, right) => numAdd(interp(left, env), interp(right, env))
    case Sub(left, right) => numSub(interp(left, env), interp(right, env))
    case With(name, value, body) => interp(body, env + (name -> interp(value, env)))
    case Id(name) => lookup(name, env)
    case Fun(params, body) => CloV(params, body, env)
    case App(func, args) => interp(func, env) match {
      case CloV(params, body, fenv) => 
        if (params.size != args.size ) error(s"wrong arity")
        interp(body, fenv ++ (params zip args.map(interp(_, env)) toMap ))
      case v => error(s"not a closure: $v")
    }
    case Rec(rec) => RecV(rec.map{ case (k, v) => (k, interp(v, env))})
    case Acc(expr: MRFWAE, name: String) => interp(expr, env) match {
      case RecV(rec) => lookupRec(name, rec)
      case v => error(s"not a record: $v")
    }
  }   

  // MRFWAEValue => String
  def eval(mrfwaeV: MRFWAEValue): String = mrfwaeV match {
    case NumV(n: Int) => n.toString
    case CloV(param, body, env) => "function"
    case RecV(rec) => "record"
  }

  def run(str: String): String = eval(interp(MRFWAE(str), Map()))


  def tests: Unit = {
    test(run("{{fun {x y} {+ x y}} 1 2}"), "3")
    test(run("{{fun {} {+ 3 4}}}"), "7")
    testExc(run("{{fun {x y} {+ x y}} 1}"), "wrong arity")
    test(run("{access {record {x 1} {y 2}} x}"), "1")
    testExc(run("{access {record {x 1} {y 2}} z}"), "no such field")
    testExc(run("{record {x {access {record {y 1}} z}}}"), "no such field")   // 지금 이게 안 돼  RecV를 Value 와의 map 으로 바꾸고 lookupRec 도 바꿔보자 -> 됐네 ㅎㅎ
    test(run("42"), "42")
    test(run("{fun {x} x}"), "function")
    test(run("{record {x 1}}"), "record")

    /* Write your own tests */
    test(run("2"), "2")
    test(interp(MRFWAE("3"), Map()), NumV(3))
    test(eval(NumV(1)), "1")
    test(run("{+ 1 2 }"), "3")
    test(run("{with {x 5} {+ x 1}}"), "6")
    test(interp(MRFWAE("{with {x 1} x}"), Map("x" -> NumV(10))), NumV(1))

    test(interp(MRFWAE("{ fun { x } {+ x 1} }"), Map()), CloV(List("x"), MRFWAE("{+ x 1}"), Map()))
    test(run("{ { fun { x } {+ x 1}} 10 }"), "11")
    test((List("b", "c") zip List(NumV(1), NumV(2))) toMap, Map("b"->NumV(1), "c"-> NumV(2)))
    test(interp(MRFWAE("{ {fun {x y} {+ x y}} 3 a }"), Map("a"->NumV(1))), NumV(4))
    testExc(run("{access {record {y 1}} z}"), "no such field")

    testExc(interp(MRFWAE("x"), Map("a"->NumV(1))), "free identifier: x")
    testExc(run("{+ 7 {record {y 1}}}"), "not both numbers: NumV(7), RecV(Map(y -> NumV(1)))")

    test(run("{access { record {x 1} } x}"), "1")
    testExc(run("{access {record {x 1}} 1}"), "free identifier: access")
    testExc(run("{ + 1 { record { x 1 } }"), "bad syntax: { + 1 { record { x 1 } }")
  }
}

