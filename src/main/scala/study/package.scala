object study {
    def hello() =
        println("hello")
    
    def fib_tail(n: Int, a: Int, b: Int): Int = 
        if (n==2) a+b
        else fib_tail(n-1, a+b, a)
    
    def fib(n: Int): Int = 
        if (n==1) 1
        else if (n==2) 1
        else fib_tail(n-1, 1, 1)

}