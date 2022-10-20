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
                f = 2&,
                g = Mod[#,2]&,
                X = {0,1,2,3,4}
        },
        VerificationTest[
                getFibres[g][{}],
                {},
TestID->"getFibres returns the empty set for an empty domain."];
        VerificationTest[
                getFibres[f][X],
                {X},
TestID->"getFibres returns a singleton for a constant function."];
        VerificationTest[
                Union@Flatten[#,1]&@getFibres[g][X],
                Union@X,
TestID->"The list of fibres from getFibres unites to the domain."];
        VerificationTest[
                getFibres[g][X],
                {{0,2,4},{1,3}},
TestID->"getFibres returns mulitple fibres for a nonconstant function."]
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
