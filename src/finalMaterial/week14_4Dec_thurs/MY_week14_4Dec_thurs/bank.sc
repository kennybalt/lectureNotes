// #Sireum #Logika

//∀ ∃

import org.sireum._

var balance: Z = 0
var elite: B = F
val eliteMin: Z = 1000000 // $1M is the minimum balance for elite members

//these are the global invariants
@spec def inv = Invariant(
  balance >= 0,
  elite == (balance >= eliteMin)
)

def deposit(amount: Z): Unit = {
    //what is an unwritten precondition about the global invariants?
    //what is an unwritten postcondition about the global invariants?

    balance = balance + amount

    if (balance >= eliteMin) {
        elite = true
    }
}

def withdraw(amount: Z): Unit = {
    //what is an unwritten precondition about the global invariants?
    //what is an unwritten postcondition about the global invariants?

    balance = balance - amount

    if (balance >= eliteMin) {
        elite = true
    } else {
        elite = false
    }
}

//////////////// Test code /////////////////////

deposit(500000)
assert(balance == 500000 & !elite)
deposit(600000)
assert(balance == 1100000 & elite)
withdraw(150000)
assert(balance == 950000 & !elite)
deposit(200000)
assert(balance == 1150000 & elite)