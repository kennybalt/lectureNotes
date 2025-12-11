// #Sireum #Logika

import org.sireum._

//"Unit" is like a void return type
def makePosZero(seq: ZS, pos: Z): Unit = {
  //how would we write the function contract?
  //what do we want to require of seq?
  //how can we describe how seq will change?
  Contract(
    Requires(pos >= 0, pos < seq.size),
    Modifies(seq),
    Ensures(
      seq(pos) == 0,
      ∀ (0 until seq.size) (k => k != pos __>: (seq(k) == In(seq)(k)))
    )
  )

  seq(pos) = 0
}

///// Test code ///////////

var nums: ZS = ZS(1,2,3)
makePosZero(nums, 2)

//---> what should we assert?
assert(nums == ZS(1,2,0))