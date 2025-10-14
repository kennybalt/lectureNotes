// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._



@pure def allBig[T](P: T=>B @pure, Q: T=>B @pure, R: T=>B @pure, B: T=>B @pure, C: T=>B @pure): Unit = {
  Deduce(
    (
        ∀((x: T) => (P(x) __>: B(x)  )),
        ∀((x: T) => (Q(x) __>: C(x)  )),
        ∀((x: T) => (R(x) __>: !B(x) & !C(x)  ))
    )
      |-
    (
      ∀((x: T) => (P(x) | Q(x) __>: !R(x)  ))
    )
    Proof(
      1 ( ∀((x: T) => (P(x) __>: B(x)  )) ) by Premise,
      2 ( ∀((x: T) => (Q(x) __>: C(x)  )) ) by Premise,
      3 ( ∀((x: T) => (R(x) __>: !B(x) & !C(x)  )) ) by Premise,

      //goal: for all statement, use AllI

      4 Let ((a: T) => SubProof(
        5 SubProof(
          6 Assume (P(a) | Q(a)),

          7 SubProof(
            8 Assume (R(a)),

            //Plug a into all my premises
            9 (P(x) __>: B(x)) by AllE[T](1),
            10 (Q(x) __>: C(x)) by AllE[T](2),
            11 (R(x) __>: !B(x) & !C(x)) by AllE[T](3),
            12 (!B(a) & !C(a)) by ImplyE(11, 8),
            13 (!B(a)) by AndE1(12),
            14 (!C(a)) by AndE2(12),

            //goal: F  
          ),
          //use NegI
          //goal: !R(a)
        ),
        //use ImplyI
        //goal: P(x) | Q(x) __>: !R(x)
      ),
      //use AllI
    )
  )
}
