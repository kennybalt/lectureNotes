// #Sireum #Logika

import org.sireum._

//set all elements to 10
def all10(nums: ZS): Unit = {
  //function contract?

  var i: Z = 0
  while (i < nums.size) {
    //loop invariant block?

    nums(i) = 10
    i = i + 1
  }
}

///////////////////////////

var test: ZS = ZS(4,1,3,8,10,2)

all10(test)

//what do we want to assert?