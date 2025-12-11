// #Sireum #Logika

import org.sireum._

def mult(x: Z, y: Z): Z = {
    Contract(
        Requires(y >= 0),
        Ensures(Res[Z] == x*y)
    )

    var sum: Z = 0
    var count: Z = 0

    //measure of work? (how many more iterations left?)
    //initially? y
    //after 1 iteration? y-1

    //in general? y-count

    while (count < y) {
        Invariant(
            Modifies(sum, count),
            count <= y,
            sum == x*count
        )

        //get measure of work: y-count

        sum = sum + x
        count = count + 1

        //get measure of work: y-count


        //measure should decrease with each iteration
            //does it? yes, since count increases with each iteration

        //when I have no work left, then my loop should be done
            //is it? yes

        //y-count == 0, y == count, then my loop condition is false
    }

    return sum
}


//We claim that multRec(x, y) will terminate for all
//nonnegative y

//Base case. multRec(x, 0) goes to my base case (the if)
//and doesn't make a recursive call. It terminates.

//Inductive step. We assume the inductive hypothesis -- that
//multRec(x, k) terminates for some nonnegative integer k.
//We must prove that multRec(x, k+1) terminates. We know
//k+1 is at least 1, so we would go into the else and make
//the recursive call multRec(x, k+1-1) which is multRec(x, k)
//which terminates by our inductive hypothesis. Thus
//multRec(x, k+1) will also terminate

def multRec(x: Z, y: Z): Z = {
    Contract(
        Requires(y >= 0),
        Ensures(Res[Z] == x*y)
    )

    var answer: Z = 0

    if (y == 0) {
        answer = 0
    } else {
        var temp: Z = mult(x, y-1)
        answer = x + temp
    }

    return answer
}

def collatz(n: Z): Z = {
    Contract(
        Requires(n > 0),
        Ensures(Res[Z] == 1)
    )

    //what if n is 52?
    //cur = 52, 26, 13, 40, 20, 10, 5, 16, 8, 4, 2, 1

    var cur: Z = n
    while (cur > 1) {
        Invariant(
            Modifies(cur),
            cur >= 1        //what else could we say?
        )

        if (cur % 2 == 0) {
            cur = cur / 2
        } else {
            cur = 3 * cur + 1
        }
    }

    return cur
}