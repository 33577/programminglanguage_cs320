package cs320

import cs320._

package object hw02 extends Homework02 {
  // applies a binary numeric function on all combinations of numbers from
  // the two input lists, and return the list of all of the results

  // add two integer
  def add(l: Int, r: Int): Int = l + r
  // subtract two integer
  def sub(l: Int, r: Int): Int = l - r
  
  type Env = Map[String, List[Int]]

  // add or sub with two List[Int]
  def binOp(
    op: (Int, Int) => Int,
    ls: List[Int],
    rs: List[Int]
  ): List[Int] = ls match {
    case Nil => Nil
    case l :: rest =>
      def f(r: Int): Int = op match {
        case add => add(l, r)
        case sub => sub(l, r)
      }
      rs.map(f) ++ binOp(op, rest, rs)
  }


  // find name in env. If there is, return value of name. Else, then raise error.
  def lookup(name: String, env: Env): List[Int] = 
    env.get(name) match {
      case Some(v) => v
      case None => error(s"free identifier: $name")
    }

  // interprete MUWAE 
  def interp(muwae: MUWAE, env: Env): List[Int] = muwae match {
    case Num(nums) => nums
    case Add(left, right) => binOp(add, interp(left, env), interp(right, env))
    case Sub(left, right) => binOp(sub, interp(left, env), interp(right, env))
    case With(name, expr, body) => interp(body, env + (name -> interp(expr, env)))
    case Id(id) => lookup(id, env)
    case Min(left, mid, right) => {
      interp(left, env) match {
        case Nil => Nil
        case l :: restLeft =>
          interp(mid, env) match {
            case Nil => Nil
            case m :: restMid =>
              def f(r: Int): Int = {
                if (l<=m && l<=r) l
                else if (m<=l && m<=r) m
                else r
              }
              // right, mid, left 순으로 spread
              // right.map(f) ++ Min(l, restMid, right) ++ Min(resLeft, Mid, right)
              interp(right, env).map(f) ++ interp(Min(Num(List(l)), Num(restMid), Num(interp(right, env))),env) ++ interp(Min(Num(restLeft), Num(interp(mid, env)), Num(interp(right, env))), env)
          }
      }
    } 
    case Max(left, mid, right) => {
      interp(left, env) match {
        case Nil => Nil
        case l :: restLeft =>
          interp(mid, env) match {
            case Nil => Nil
            case m :: restMid =>
              def f(r: Int): Int = {
                if (l>=m && l>=r) l
                else if (m>=l && m>=r) m
                else r
              }
              interp(right, env).map(f) ++ interp(Max(Num(List(l)), Num(restMid), Num(interp(right, env))),env) ++ interp(Max(Num(restLeft), Num(interp(mid, env)), Num(interp(right, env))), env)
          }
      }
    } 
  }

  def run(str: String): List[Int] = interp(MUWAE(str), Map())

  def tests: Unit = {
    test(run("{+ 3 7}"), List(10))
    test(run("{- 10 {3 5}}"), List(7, 5))
    test(run("{with {x {+ 5 5}} {+ x x}}"), List(20))
    test(run("{min 3 4 5}"), List(3))
    test(run("{max {+ 1 2} 4 5}"), List(5))
    test(run("{min {1 4} {2 9} 3}"), List(1, 1, 2, 3))
    test(run("{max {1 6} {2 5} {3 4}}"), List(3, 4, 5, 5, 6, 6, 6, 6))

    /* Write your own tests */ //  
    // test that using with to bind a name to a multi-valued expression works as expected.
    // add sub binOp lookup interp run
    test(add(1, 2), 3)
    test(add(1, 3), 4)
    test(add(2, 3), 5)
    test(add(-1, 100), 99)
    test(add(123123123, 123123123), 246246246)

    test(sub(1, 2), -1)
    test(sub(1, 3), -2)
    test(sub(2, 2), 0)
    test(sub(-1, 100), -101)
    test(sub(123123123, 123123123), 0)

    test(binOp(add, List(0), List(1)), List(1))
    test(binOp(add, List(0), List(2, 3)), List(2, 3))
    test(binOp(add, List(0, 1), List(3, 10)), List(3, 10, 4, 11))
    test(binOp(sub, List(0), List(1)), List(-1))
    test(binOp(sub, List(0, 1), List(3, 10)), List(-3, -10, -2, -9))

    test(lookup("x", Map("x"->List(0))), List(0))
    test(lookup("x", Map("x"->List(0), "y"->List(0))), List(0))
    test(lookup("a", Map("a"->List(1))), List(1))
    test(lookup("x", Map("x"->List(3, 4))), List(3, 4))
    test(lookup("y", Map("x"->List(5), "y"->List(3, 4))), List(3, 4))
    
    test(interp(Num(List(3)), Map()), List(3))
    test(interp(Add(Num(List(1, 3)), Num(List(5, 6))), Map()), List(6, 7, 8, 9))
    test(interp(With("x", Num(List(3, 4)), Add(Id("x"), Num(List(1)))), Map("x"->List(5))), List(4, 5))
    test(interp(Id("x"), Map("x"->List(3))), List(3))
    test(interp(Min(Num(List(3, 5)), Id("x"), Add(Num(List(2)), Num(List(7)))), Map("x"->List(4))), List(3, 4))

    test(run("{+ {1 5} {3 4}}"), List(4, 5, 8, 9))
    test(run("{with {x {2 3}} { + x 1 } }"), List(3, 4))
    test(run("{min { with {x {1 3}} { + x 1 } } 3 5}"), List(2, 3))
    test(run("{max { with {x {1 11}} { + x 1 } } 5 9}"), List(9, 12))
    test(run("{max {min 1 1 2} -1 -1 }"), List(1))

    test(run("{+ {1 5 7} {3 4 9}}"), List(4, 5, 10, 8, 9, 14, 10, 11, 16))
    test(run("{min {1 2 5 6} {3 4} 9}"), List(1, 1, 2, 2, 3, 4, 3, 4))


  }
}
