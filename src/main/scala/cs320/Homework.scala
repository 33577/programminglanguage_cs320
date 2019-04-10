package cs320

import scala.reflect.ClassTag

trait Homework {
  // Get callsite info
  private def getCSInfo: String = try { throw new Error("") } catch {
    case e: Throwable =>
      val pp = e.getStackTrace()(5)
      s"${pp.getFileName}:${pp.getLineNumber}"
  }

  // pass/fail
  var alertOnlyFail: Boolean = false
  
  private def pass: Unit = if (!alertOnlyFail)
    println(s"PASS [$getCSInfo]")
  private def fail(msg: String): Unit =
    println(s"FAIL [$getCSInfo]: $msg")


  // Tests
  def test[T](input: =>T, output: =>T): Unit = try {
    if (input == output) pass
    else fail(s"$input is not equal to $output")
  } catch {
    case e: Throwable => fail(e.getMessage)
  }

  // Define errors
  case class PLError(msg: String) extends Error(s"[ERROR] $msg")
  def error[T](msg: String): T = throw PLError(msg)

  // Tests for exceptions
  def testExc[T](input: =>T, msg: String): Unit = try {
    fail(s"it should throw an error but result is $input")
  } catch {
    case e: Throwable =>
      val eMsg = e.getMessage
      if (eMsg.contains(msg)) pass
      else fail(s""""$eMsg" does not contain "$msg"""")
  }

  // Cast types with error messages for failure cases
  def cast[T](
    v: Any,
    msg: => String
  )(implicit tag: ClassTag[T]): T = v match {
    case v: T => v
    case v => error(msg)
  }

  // Tests
  def tests: Unit
}
