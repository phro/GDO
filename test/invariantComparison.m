Module[
        {
                f = Mod[#,2]&,
                X = {0,1,2,3,4},
                Y = {0,2,4},
                Z = {},
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
