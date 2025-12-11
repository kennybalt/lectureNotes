// #Sireum #Logika

//∀ ∃

import org.sireum._

//returns whether an element is in a sequence
//returns true/false (B is bool)
//can either write true or T, same with false
def containsElem(nums: ZS, elem: Z): B = {
    //contract?

    var i: Z = 0
    var found: B = false
    while (i < nums.size) {
        //invariant?

        if (nums(i) == elem) {
            found = true
        }
        i = i + 1
    }

    return found
}

////////////// Calling code ///////////////////

var test: ZS = ZS(8,1,0,10,9,2,0)
var testFound: B = containsElem(test, 0)

//what should testFound be?


testFound = containsElem(test, 4)

//what should testFound be?
