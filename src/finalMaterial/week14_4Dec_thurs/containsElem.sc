// #Sireum #Logika

//∀ ∃

import org.sireum._

//returns whether an element is in a sequence
//returns true/false (B is bool)
//can either write true or T, same with false
def containsElem(nums: ZS, elem: Z): B = {
    //contract?
    Contract(
        //nothing to require
        //not changing the sequence
        Ensures(
            //need to describe what is being returned

            //returning true
            //IF I return true, THEN one of the sequence elements equals elem
            Res[B] == true __>: ∃ (0 until nums.size) (k => nums(k) == elem),

            //IF I return false, THEN none of the sequence elements equal elem
            Res[B] == false __>: !(∃ (0 until nums.size) (k => nums(k) == elem))

            //OR, could have said for second postcondition:
            //Res[B] == false __>: ∀ (0 until nums.size) (k => nums(k) != elem))
        )
    )

    var i: Z = 0
    var found: B = false
    while (i < nums.size) {
        //invariant?
        Invariant(
            Modifies(i, found),

            //bound loop counter
            i>= 0, i <= nums.size,

            found == true __>: ∃ (0 until i) (k => nums(k) == elem),

            found == false __>: !(∃ (0 until i) (k => nums(k) == elem))
        )

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
assert(testFound == true)


testFound = containsElem(test, 4)

//what should testFound be?
assert(testFound == false)
