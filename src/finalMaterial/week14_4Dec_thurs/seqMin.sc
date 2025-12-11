// #Sireum #Logika

//∀ ∃

import org.sireum._

//return the smallest element in list
def min(list: ZS): Z = {
    //contract?
    Contract(
        Requires(list.size >= 1),
        //nothing is modified
        Ensures(
            //describe the return value
            //what we are returning is <= all elements in the sequence
            ∀ (0 until list.size) (k => Res[Z] <= list(k)),

            //whatever I'm returning IS a sequence element
            ∃ (0 until list.size) (k => Res[Z] == list(k))
        )
    )

    var small: Z = list(0)
    var i: Z = 1
    
    while (i < list.size) {
        //invariant?
        Invariant(
            Modifies(i, small),

            //bound the loop counter
            i >= 1, i <= list.size,

            ∀ (0 until i) (k => small <= list(k)),

            ∃ (0 until i) (k => small == list(k))
        )

        if (list(i) < small) {
            small = list(i)
        }
        i = i + 1
    }

    return small
}

////////////// Calling code ///////////////////

var test: ZS = ZS(8,1,0,10,9,2,0)
var testMin: Z = min(test)

//what should testMin be?
assert(testMin == 0)