package cs320

trait Homework01 extends Homework {
  // Problem 1
  def dollar2won(dollar: Int): Int
  def volumeOfCuboid(a: Int, b: Int, c: Int): Int
  def isEven(num: Int): Boolean
  def isOdd(num: Int): Boolean
  def gcd(a: Int, b: Int): Int
  def lcm(a: Int, b: Int): Int

  // Problem 2
  trait COURSE
  case class CS320(quiz: Int, homework: Int) extends COURSE
  case class CS311(homework: Int) extends COURSE
  case class CS330(projects: Int, homework: Int) extends COURSE

  def numOfHomework(course: COURSE): Int
  def hasProjects(course: COURSE): Boolean

  // Problem 3
  def namePets(pets: List[String]): List[String]
  def giveName(oldName: String, newName: String): List[String] => List[String]

  // Tests
  def tests: Unit
}
