package cs320

package object hw01 extends Homework01 {
  // Problem 1
  def dollar2won(dollar: Int): Int = dollar * 1100
  def volumeOfCuboid(a: Int, b: Int, c: Int): Int = a * b * c
  def isEven(num: Int): Boolean = num % 2 == 0
  def isOdd(num: Int): Boolean = num % 2 != 0
  def gcd(a: Int, b: Int): Int = {
    if (a==0) b
    else if (b==0) a
    else if (a>b) {
      gcd(a%b, b)
    }
    else {
      gcd(a, b%a)
    }
  }
  def lcm(a: Int, b: Int): Int = {
    a * b / gcd(a, b)
  }

  // Problem 2
  def numOfHomework(course: COURSE): Int = course match {
    case CS320(quiz, homework) => homework
    case CS311(homework) => homework
    case CS330(projects, homework) => homework
  }
  def hasProjects(course: COURSE): Boolean = course match {
    case CS320(quiz, homework) => false
    case CS311(homework) => false
    case CS330(projects, homework) => projects >= 2
  }

  // Problem 3
  def namePets(pets: List[String]): List[String] = {
    pets.map((p: String) => {
      if (p=="dog") "happy"
      else if (p=="cat") "smart"
      else if (p=="pig") "pinky"
      else p
    })
  }
  def giveName(oldName: String, newName: String): List[String] => List[String] = {
    (pets: List[String]) => {
      pets.map((p: String) => {
        if (p==oldName) newName
        else p
      })
    }
  }

  def tests: Unit = {
    test(dollar2won(1), 1100)
    test(volumeOfCuboid(1, 2, 3), 6)
    test(isEven(10), true)
    test(isOdd(10), false)
    test(gcd(123, 245), 1)
    test(lcm(123, 245), 30135)
    test(numOfHomework(CS320(quiz = 4, homework = 3)), 3)
    test(hasProjects(CS320(quiz = 3, homework = 9)), false)
    test(namePets(List("dog", "cat", "pig")), List("happy", "smart", "pinky"))
    test(giveName("bear", "pooh")(List("pig", "cat", "bear")), List("pig", "cat", "pooh"))

    /* Write your own tests */
    test(dollar2won(4), 4400)
    test(volumeOfCuboid(4, 1, 2), 8)
    test(isEven(2), true)
    test(isOdd(3), true)
    test(gcd(10, 24), 2)
    test(gcd(50, 10), 10)
    test(lcm(10, 24), 120)
    test(lcm(50, 10), 50)
    test(numOfHomework(CS330(projects = 1, homework = 10)), 10)
    test(hasProjects(CS330(projects = 1, homework = 0)), false)
    test(hasProjects(CS330(projects = 2, homework = 0)), true)
    test(namePets(List("dog", "hippo")), List("happy", "hippo"))
    test(giveName("dog", "morae")(List("dog", "cat")), List("morae", "cat"))
  }
}