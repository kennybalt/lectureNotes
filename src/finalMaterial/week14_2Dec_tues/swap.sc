// #Sireum #Logika

import org.sireum._

//want to write a swap function
def swap(nums: ZS, pos1: Z, pos2: Z): Unit = {
  //how to write?
  Contract(
    Requires(pos1 >= 0, pos1 < nums.size, pos2 >= 0, pos2 < nums.size),
    Modifies(nums),
    Ensures(
      nums(pos1) == In(nums)(pos2),
      nums(pos2) == In(nums)(pos1),
      ∀ (0 until nums.size) (k => k != pos1 & k != pos2 __>: (nums(k) == In(nums)(k)))
    )
  )

  //how to write contract?

  var temp: Z = nums(pos1)
  nums(pos1) = nums(pos2)
  nums(pos2) = temp
}

///////////////////////////

var test: ZS = ZS(4,1,3,8,10,2)

swap(test, 2, 4)


//what do we want to assert?
assert(test == ZS(4,1,10,8,3,2))