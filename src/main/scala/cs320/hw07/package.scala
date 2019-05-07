package cs320

package object hw07 extends Homework07 {
  trait KXCFAEValue
  case class NumV(n: Int) extends KXCFAEValue
  case class CloV(params: List[String], body: KXCFAE, env: Env) extends KXCFAEValue
  case class ContV(proc: Cont) extends KXCFAEValue
  case class ThrowV() extends KXCFAEValue

  type Env = Map[String, KXCFAEValue]
  type Cont = KXCFAEValue => KXCFAEValue
  
  // numOp: ((Int, Int) => Int) => (KXCFAEValue, KXCFAEValue) => KXCFAEValue
  def numOp(op: (Int, Int) => Int): (KXCFAEValue, KXCFAEValue) => KXCFAEValue = (_, _) match {
    case (NumV(x), NumV(y)) => NumV(op(x, y))
    case (x, y) => error(s"not both numbers: $x, $y")
  }
  val numAdd = numOp(_ + _)
  val numSub = numOp(_ - _)

  // find name in env. If there is, imthrow value of name. Else, then raise error.
  def lookup(name: String, env: Env): KXCFAEValue = 
    env.get(name) match {
      case Some(v) => v
      case None => {
        if(name=="imthrow") error(s"no enclosing try-catch")
        error(s"free identifier: $name")
      }
    }

  def interp(KXCFAE: KXCFAE, env: Env, k: Cont): KXCFAEValue = KXCFAE match {
    case Num(num) => k(NumV(num))
    case Add(l, r) => 
      interp(l, env, lv => {
                        if (lv==ThrowV()) k(ThrowV())
                        else interp(r, env, rv => {
                                          if (rv==ThrowV()) k(ThrowV())
                                          else k(numAdd(lv, rv))
                        })
      })
    case Sub(l, r) =>
      interp(l, env, lv => {
                        if (lv==ThrowV()) k(ThrowV())
                        else interp(r, env, rv => {
                                          if (rv==ThrowV()) k(ThrowV())
                                          else k(numSub(lv, rv))
                        })
      })
    case Id(name) => k(lookup(name, env))
    case Fun(params, body) => k(CloV(params, body, env))
    case App(f, args) =>                                   
      interp(f, env, fv => {
                        if(fv==ThrowV()) k(ThrowV())
                        else help(List(), args, env, fv, k)
      })
    case Withcc(name, body) => interp(body, env+(name->ContV(k)), k)
    case Try(tryE, catchE) => 
      interp(tryE, env, tryV => {
        if(tryV==ThrowV()) interp(catchE, env, catchV => k(catchV))         
        else k(tryV)  
      })
    case Throw => k(ThrowV())
    case If0(cond, thenE, elseE) => 
      interp(cond, env, condV => 
                              if(condV==ThrowV()) k(ThrowV())
                              else if(condV==NumV(0)) interp(thenE, env, k)
                              else interp(elseE, env, k)
      )
      
  }

  def help(previousValueList: List[KXCFAEValue], remainExprList: List[KXCFAE], env: Env, fv: KXCFAEValue, k: Cont): KXCFAEValue = remainExprList match {
    case e::rest => interp(e, env, ev => {
                                      if (ev==ThrowV()) k(ThrowV())
                                      else {
                                        val newPVL = previousValueList :+ ev   // list 끝에 ev 넣기
                                        help(newPVL, rest, env, fv, k)
                                      }
    })
    case Nil => fv match {
          case CloV(params, body, fenv) => 
            if (params.size != previousValueList.size ) error(s"wrong arity")
            interp(body, fenv ++ (params zip previousValueList toMap ), k)
          case ContV(kv) => 
            if (previousValueList.size != 1 ) error(s"wrong arity")
            kv(previousValueList(0))         
          case v => error(s"Not a closure or Continuation: $v")
    }
  }

  // KXCFAEValue => String
  def eval(kValue: KXCFAEValue): String = {
    kValue match {
      case NumV(n) => n.toString
      case CloV(param, body, env) => "function"
      case ContV(proc) => "continuation"
      case ThrowV() => error(s"no enclosing try-catch") 
    }
  }

  def run(str: String): String = eval(interp(KXCFAE(str), Map(), x=>x))

  def tests: Unit = {
    test(run("{{fun {x y} {- y x}} 10 12}"), "2")
    test(run("{fun {} 12}"), "function")
    testExc(run("{{fun {x y} 1} 2}"), "wrong arity")
    test(run("{withcc esc {{fun {x y} x} 1 {esc 3}}}"), "3")

    test(run("{try 1 catch 2}"), "1")
    test(run("{try {throw} catch 2}"), "2")         // Try(Throw, Num(2))
    test(run("{try {+ 1 {throw}} catch 2}"), "2")   // Try(Add(Num(1), Throw), Num(2))
    test(run("{{fun {f} {try {f} catch 1}} {fun {} {throw}}}"), "1") 
    testExc(run("{throw}"), "no enclosing try-catch")

    /* Write your own tests */
    testExc(run("{withcc esc {esc 3 5}}"), "wrong arity")
    test(run("{+ 1 {withcc k {{fun {x y} {+ x y}} {k 2} 4}}}"), "3")
    test(run("{withcc esc { try 1 catch 2 }}"), "1")
    test(run("{withcc esc { try {esc 10} catch 2 }}"), "10")
    test(run("{withcc esc { try 1 catch {esc 10} }}"), "1")
    test(run("{withcc esc { try {throw} catch {esc 10} }}"), "10")
    test(run("{try { withcc esc {esc {throw}} } catch 2 }"), "2")
    test(run("{{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} 1 {+ y {g g {- y 1}}}}} 10}"), "55")
    test(run("{try {if0 {throw} 1 2} catch 5}"), "5")


    /* 지난학기 */
    test(run("{{fun {x y} {- y x}} 10 12}"), "2")
    test(run("{fun {} 12}"), "function")
    test(run("{fun {x} {fun {} x}}"), "function")
    test(run("{{{fun {x} {fun {} x}} 13}}"), "13")
    test(run("{withcc esc {{fun {x y} x} 1 {esc 3}}}"), "3")
    test(run("{+ {withcc k {k 5}} 4}"), "9")
    test(run("{withcc k {k {- 0 100}}}"), "-100")
    test(run("{withcc k {k {+ 100 11}}}"), "111")
    test(run("{{fun {a b c} {- {+ {withcc k {+ {k 100} a}} b} c}} 100 200 300}"), "0")
    test(run("{withcc esc {{fun {x y} x} 1 {esc 3}}}"), "3")
    test(run("{{withcc esc {{fun {x y} {fun {z} {+ z y}}} 1 {withcc k {esc k}}}} 10}"), "20")
    test(run("{try {{fun {x y z} {a b c}} 1 2 {throw}} catch 0}"), "0")
    test(run("{{fun {f} {try {f 3} catch 8}} {fun {x} {throw}}}"), "8")
    test(run("{try {- 0 {withcc k {+ 3 {k {throw}}}}} catch 89}"), "89")
    test(run("{try {+ 3 {withcc k {+ 1000 {k {throw}}}}} catch 11}"), "11")
    test(run("{{fun {x y z} {try {+ 1 {+ x {throw}}} catch {+ y z}}} 1 2 3}"), "5")
    test(run("{+ {try {- 10 {throw}} catch 3} 10}"), "13")
    test(run("{try {if0 0 {throw} {+ 1 2}} catch {if0 10 1 {try {throw} catch 54}}}"), "54")
    test(run("{try {withcc a {+ 1 {withcc b {throw}}}} catch 10}"), "10")
    test(run("{try {{fun {x y} {try x catch y}} {throw} 0} catch -1}"), "-1")
    test(run("{try {try {throw} catch {throw}} catch 9}"), "9")
    test(run("{{withcc esc {try {{withcc k {esc k}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}"), "8")
    test(run("{{withcc esc {try {{withcc k {try {esc k} catch {fun {x} {fun {y} 9}}}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}"), "8")
    test(run("{withcc foo {{fun {x y} {y x}} {+ 2 3} {withcc bar {+ 1 {bar foo}}}}}"), "5")
    test(run("{try {withcc zzz {{fun {x y z w} {+ {+ x y} {+ z w}}} 1 2 {zzz 10} {throw}}} catch 42}"), "10")
    test(run("{try {withcc zzz {{fun {x y z w} {+ {+ x y} {+ z w}}} 1 2 {throw} {zzz 10}}} catch 42}"), "42")
    test(run("{try {withcc zzz {{fun {x y z w} {+ {w {+ x y}} {+ {throw} z}}} 1 2 3 zzz}} catch 42}"), "3")
    test(run("{withcc esc {try {+ {throw} {esc 3}} catch 4}}"), "4")
    test(run("{withcc esc {{fun {x y} {+ {+ x 3} y}} {withcc k {try {k {esc {throw}}} catch {k 5}}} 7}}"), "15")
    test(run("{try {withcc x {+ {x 1} {throw}}} catch 0}"), "1")
    test(run("{+ 12 {withcc k {+ 1 {k {{fun {} 7}}}}}}"), "19")

    test(run("{{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} 1 {+ y {g g {- y 1}}}}} 10}"), "55") // recursive function
    test(run("{withcc done {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {done 100} {+ y {g g {- y 1}}}}} 10}}"), "100") // exit from recursive function using continuation
    test(run("{try {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {+ y {g g {- y 1}}}}} 10} catch 110}"), "110") // exit from recursive function using try-catch
    test(run("{{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch y}}} 10}"), "54") // equal? for multiple recursive try-catch
    test(run("{withcc done {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch {done y}}}} 10}}"), "2")
    test(run("{try {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch {throw}}}} 10} catch 20110464}"), "20110464") // recursive try-catch throwing ("1")
    
    test(run("{+ 999 {withcc done {{fun {f x} {f f x done}} {fun {g y z} {if0 {- y 1} {z 100} {+ y {g g {- y 1} z}}}} 10}}}"), "1099")
    test(run("{+ 999 {withcc done {{fun {f x} {f f x {fun {x} {if0 x {done {- 0 999}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 100} {+ y {g g {- y 1} z}}}} 10}}}"), "11053")
    test(run("{+ 999 {withcc done {{fun {f x} {f f x {fun {x} {if0 x {done {- 0 999}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {+ y {g g {- y 1} z}}}} 10}}}"), "0")
    test(run("{withcc done {{fun {f x} {f f x {fun {x} {if0 x {fun {y} {fun {x} {+ x y}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 3}}"), "64")
    test(run("{{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 3}} 5}"), "continuation")
    test(run("{{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 4}} {fun {y} {fun {y} {fun {y} {fun {x} 42}}}}}"), "42")
    test(run("{{fun {mk-list} {{fun {list} {if0 {list 0} {list 1} {0 {{list 2} {{{mk-list {- {list 0} 1}} {+ {list 1} 2}} {list 2}}}}}} {withcc k {{{mk-list 11} 0} k}}}} {fun {a} {fun {b} {fun {c} {fun {sel} {if0 sel a {if0 {- sel 1} b c}}}}}}}"), "22")
    test(run("{{fun {mk-list} {{fun {list} {if0 {list 0} {list 1} {0 {{list 2} {{{mk-list {- {list 0} 1}} {+ {list 1} {list 1}}} {list 2}}}}}} {withcc k {{{mk-list 10} 1} k}}}} {fun {a} {fun {b} {fun {c} {fun {sel} {if0 sel a {if0 {- sel 1} b c}}}}}}}"), "1024")

    test(run("{try {if0 {throw} 3 4} catch 5}"), "5")
    test(run("{try {{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} {throw}}}}} {fun {g y z} {if0 {- y 1} {z 1} {{g g {- y 1} z} 32}}} 4}} {fun {y} {fun {y} {fun {y} {fun {x} 42}}}}} catch 4242}"), "4242")
    test(run("{withcc esc {{try {withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} {throw}}}}} {fun {g y z} {if0 {- y 1} {z 1} {{g g {- y 1} z} 32}}} 4}} catch esc} 33}}"), "33")
    test(run("{try {{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 4}} {fun {y} {fun {y} {fun {y} {throw}}}}} catch 4242}"), "4242")
    
  }
}
