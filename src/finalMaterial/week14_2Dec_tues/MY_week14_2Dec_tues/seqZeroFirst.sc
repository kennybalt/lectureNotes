// #Sireum #Logika

import org.sireum._

//"Unit" is like a void return type
def makeFirstZero(seq: ZS): Unit = {
  //how would we write the function contract?
  //what do we want to require of seq?
  //how can we describe how seq will change?
}

///// Test code ///////////

var nums: ZS = ZS(1,2,3)
makeFirstZero(nums)

//---> what should we assert?