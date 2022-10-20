Module[
        {
                f = Mod[#,2]&,
                X = {0,1,2,3,4},
                Y = {0,2,4},
                Z = {}
        },
        VerificationTest[
                distinctValues[f][X],
                2,
TestID->"distinctValues returns the size of the image of an invariant."];
        VerificationTest[
                distinctValues[f][Y],
                1,
TestID->"distinctValues returns 1 on a fibre."];
        VerificationTest[
                distinctValues[f][Z],
                0,
TestID->"distinctValues returns the size of an empty image."]
]

Module[
        {
                mod4 = Mod[#,4]&,
                mod2 = Mod[#,2]&,
                X = {0,1,2,3,4},
                Y = {0,4}
        },
        VerificationTest[
                subinvariantQ[mod2][mod4][X],
                True,
TestID->"subinvariantQ compares a weaker invariant to a stronger one."];
        VerificationTest[
                subinvariantQ[mod2][mod4][Y],
                True,
TestID->"subinvariantQ compares equivalent invariants on a small domain."];
        VerificationTest[
                subinvariantQ[mod4][mod2][X],
                False,
TestID->"subinvariantQ compares a stronger invariant to a weaker one."];
        VerificationTest[
                subinvariantQ[mod4][mod2][Y],
                True,
TestID->"subinvariantQ does not distinguish invariants on a small domain."]
]
