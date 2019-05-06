package cs320

package object hw05 extends Homework05 {
  trait SRBFAEValue
  case class NumV(n: Int) extends SRBFAEValue
  case class CloV(param: String, body: SRBFAE, env: Env) extends SRBFAEValue
  case class BoxV(addr: Addr) extends SRBFAEValue
  case class RecV(rec: Map[String, (SRBFAEValue, Sto)]) extends SRBFAEValue

  type Env = Map[String, Addr]
  type Addr = Int
  type Sto = Map[Addr, SRBFAEValue]

  // numOp: ((Int, Int) => Int) => (SRBFAEValue, SRBFAEValue) => SRBFAEValue
  def numOp(op: (Int, Int) => Int): (SRBFAEValue, SRBFAEValue) => SRBFAEValue = (_, _) match {
    case (NumV(x), NumV(y)) => NumV(op(x, y))
    case (x, y) => error(s"not both numbers: $x, $y")
  }
  val numAdd = numOp(_ + _)
  val numSub = numOp(_ - _)

  // find name in env. If there is, return value of name. Else, then raise error.
  def lookup(name: String, env: Env): Addr = 
    env.get(name) match {
      case Some(v) => v
      case None => error(s"free identifier: $name")
    }

  def lookupRec(name: String, rec: Map[String, (SRBFAEValue, Sto)]): (SRBFAEValue, Sto) = 
    rec.get(name) match {
      case Some(tuple) => {
        tuple
      }
      case None => error(s"no such field")
    }

  def lookupStore(addr: Addr, sto: Sto): SRBFAEValue =
    sto.get(addr) match {
      case Some(v) => v
      case None => error(s"Nothing at $addr in $sto")
    }

  // malloc : Sto => Addr
  def malloc(sto: Sto): Addr =
    sto.foldLeft(0) {
      case (max, (addr, _)) => math.max(max, addr)
  }+1

  def interp(SRBFAE: SRBFAE, env: Env, sto: Sto): (SRBFAEValue, Sto) = SRBFAE match {
    case Num(num) => (NumV(num), sto)
    case Add(left, right) => 
      val (rv, rs) = interp(right, env, sto)
      val (lv, ls) = interp(left, env, rs)
      (numAdd(lv, rv), ls)
    case Sub(left, right) =>
      val (rv, rs) = interp(right, env, sto)
      val (lv, ls) = interp(left, env, rs)
      (numSub(lv, rv), ls)
    case Id(name) => (lookupStore(lookup(name, env), sto), sto)
    case Fun(param, body) => (CloV(param, body, env), sto)
    case App(fun, arg) =>                                   // store check 하기 test case 로
      val (fv, fs) = interp(fun, env, sto)
      val (av, as) = interp(arg, env, fs)
      fv match {
        case CloV(x, b, fenv) =>
          val addr = malloc(as)
          interp(b, fenv + (x -> addr), as + (addr -> av))
        case _ => error(s"not a closure: $fv")
      }
    case NewBox(expr) => 
      val (v,s) = interp(expr, env, sto)
      val addr = malloc(s)
      (BoxV(addr), s+(addr->v))
    case SetBox(box, expr) =>
      val (bv, bs) = interp(box, env, sto)
      bv match {
        case BoxV(addr) =>
          val (ev, es) = interp(expr, env, bs)
          (ev, es+(addr->ev))
        case _ => error(s"not a box: $bv")
      }
    case OpenBox(expr) => 
      val (bv, bs) = interp(expr, env, sto)
      bv match {
        case BoxV(addr) =>
          (lookupStore(addr, bs), bs)
        case _ => error(s"not a box: $bv")
      }
    case Seqn(left, right) => 
      val (lv, ls) = interp(left, env, sto)
      right match {
        case Nil => (lv, ls)
        case r :: rest => {
          interp(Seqn(r, rest), env, ls)
        }
      }
    case Rec(fields) => ( RecV(fields.map{ case (s, e) => (s, interp(e, env, sto))}), sto)
    case Get(record, field) => {
      val (rv, rs) = interp(record, env, sto)
      rv match {
            case RecV(rec) => lookupRec(field, rec)
            case _ =>  error(s"not a record: $rv")
      }
    }
    case Set(record, field, expr) => {
      record match {
        case Id(name) => {
          val addr = lookup(name, env)
          val recV = lookupStore(addr, sto)
          recV match {
            case RecV(rec) => {
              val (ev, es) = interp(expr, env, sto)
              val (originalV, originalS) = lookupRec(field, rec) // to produce error I don't use result .. I need more fancy way
              val newRecV = RecV(rec+(field -> (ev, es)))
              (ev, es + (addr -> newRecV))
            }
            case _ => error(s"not a record: $recV")
          }
        }
        case _ => {
          val (rv, rs) = interp(record, env, sto)
          rv match {
            case RecV(rec) => {
              val (ev, es) = interp(expr, env, rs)
              val (originalV, originalS) = lookupRec(field, rec) // to produce error I don't use result 
              (ev, es)
            }
            case _ =>  error(s"not a record: $rv")
          }
        }
      }
    }

  }   

  // SRBFAEValue => String
  def eval(tup: (SRBFAEValue, Sto)): String = {
    val (srbfaeV, sto) = tup
    srbfaeV match {
      case NumV(n: Int) => n.toString
      case CloV(param, body, env) => "function"
      case RecV(rec) => "record"
      case BoxV(addr) => "box"
    }
  }

  def run(str: String): String = eval(interp(SRBFAE(str), Map(), Map()))

  def tests: Unit = {
    test(run("""{{fun {b} {seqn {setbox b {+ 2 {openbox b}}}
                          {setbox b {+ 3 {openbox b}}}
                          {setbox b {+ 4 {openbox b}}}
                          {openbox b}}}
                {newbox 1}}"""), "10")
    testExc(run("{get {rec {x 1}} y}"), "no such field")
    test(run("{{fun {r} {seqn {set r x 5} {get r x}}} {rec {x 1}}}"), "5")
    test(run("42"), "42")
    test(run("{fun {x} x}"), "function")
    test(run("{newbox 1}"), "box")
    test(run("{rec}"), "record")

    /* Write your own tests */
    test(run("{openbox {newbox 2}}"), "2")
    test(run("{openbox {newbox {+ 1 1}}}"), "2")
    test(run("{setbox {newbox 2} 5}"), "5")
    test(run("""{ { fun {b} {seqn { setbox b {+ 1 {openbox b}} } 
                              {openbox b} } } 
                {newbox 1} }"""), "2")
    test(run("{get {rec { x 1 }} x}"), "1")
    test(run("{get {rec { x {+ 1 1 } }} x}"), "2")
    test(run("{{fun {r} {get r x}} {rec {x 1}}}"), "1")
    test(run("{{fun {r} {set r x 5}} {rec {x 1}}}"), "5")
    test(run("{ set {rec {x 1}} x 5 } "), "5")
    testExc(run("{{fun {r} {get s x}} {rec {x 1}}}"), "free identifier: s")
    testExc(run("{{fun {r} {get r y}} {rec {x 1}}}"), "no such field")
    testExc(run("{ set {rec {x 1}} y 5 }"), "no such field")
    testExc(run("{{fun {r} {set r y 5}} {rec {x 1}}}"), "no such field")

    /* piazza */
    test(run("{openbox {get {rec {x {newbox 12}}} x}}"), "12")
    test(run("{{fun {r} {seqn {set r x {newbox 8}} {get r x}}} {rec {x {newbox 7}}} }"), "box")
    test(run(" { openbox {{  fun {b} { get { rec { x {setbox b 3} } {y b}  }  y } }  {newbox 1}} } "), "3") // 아.. 
    test(run("{{fun {x} {get {rec {x 1} {y 2} {z 3}} x}} {newbox 8}}"), "1")


  }
}
