Module[
        {i, j},
        VerificationTest[
                GDO[{i}->{j}][
                        α[i]a[j]+ β[i]b[j] + τ[i]t[j], ξ[i] x[j] + η[i]y[j], 1
                ],
                Subscript[sσ,i ->j],
TestID->"GDO-notation returns \[DoubleStruckCapitalE]-notation."]]

Module[
        {i, j},
        VerificationTest[
                coinv[i][a[j] y[i] x[i]],
                a[j] t[i],
TestID->"coinv[i] reduces xy to t"]]

Module[
        {i, j},
        VerificationTest[
                coinv[i][a[j] a[i] y[i]^5 x[i]^5],
                5! a[j] a[i] t[i]^5,
TestID->"coinv[i] reduces a(xy)^5 to at^5"]]

Module[
        {i, j},
        VerificationTest[
                coinv[i][3 x[i]^2 y[i]^2 + a[j] a[i] y[i]^5 x[i]^5],
                3*2! t[i]^2 + 5! a[j] a[i] t[i]^5,
TestID->"coinv[i] reduces functions on sums of monomials."]]

Module[
        {i},
        VerificationTest[
                trGenFunc[3][i],
                η[i]α[i]ξ[i](a[i]t[i]) + 1/2β[i]α[i]^2(2a[i]t[i] - t[i])
                        + 1/6 α[i]^3 a[i]^3 +
                η[i] ξ[i] (t[i]) + β[i] α[i] (t[i]) + 1/2 α[i]^2 (a[i]^2) +
                α[i] a[i] +
                1,
TestID->"trGenFunc[i] is correct up to degree 3."]]

Module[
        {i},
        VerificationTest[
                trDeg[4][i][[3]],
                trGenFunc[4][i]//ExpandAll,
TestID->"trDeg produces trGenFunc's output."]]

Module[
        {i, j, λ},
        VerificationTest[
                GDO[{i}->{j}][α[i] b[j], 0, 1] //
                        ScaleBy[λ][j],
                GDO[{i}->{j}][λ α[i] b[j], 0, 1],
TestID -> "ScaleBy[λ] scales b by the weight-tracker."]]

Module[
        {i, j, λ},
        VerificationTest[
                GDO[{i}->{j}][β[i] a[j] , 0, 1] //
                        ScaleBy[λ][j],
                GDO[{i}->{j}][λ β[i] a[j], 0, 1],
TestID -> "ScaleBy[λ] scales a by the weight-tracker."]]

Module[
        {i, j,λ},
        VerificationTest[
                GDO[{i}->{j}][0, ξ[i] y[j], 1] //
                        ScaleBy[λ][j],
                GDO[{i}->{j}][0, λ ξ[i] y[j], 1],
TestID -> "ScaleBy[λ] scales y by the weight-tracker."]]

Module[
        {i, j, λ},
        VerificationTest[
                GDO[{i}->{j}][0, β[i] x[j], 1] //
                        ScaleBy[λ][j],
                GDO[{i}->{j}][0, λ β[i] x[j], 1],
TestID -> "ScaleBy[λ] scales x by the weight-tracker."]]

Module[
        {f, λ, n=5},
        VerificationTest[
                TruncateToDegree[n][λ][f],
                f,
TestID->"TruncateToDegree is the identity on constants."]]

Module[
        {λ, x},
        VerificationTest[
                TruncateToDegree[2][λ][x[0]+x[1]λ+x[2]λ^2+x[3]λ^3],
                x[0]+x[1]λ+x[2]λ^2,
TestID->"TruncateToDegree restricts polynomials appropriately."]]

Module[
        {λ, x},
        VerificationTest[
                TruncateToDegree[2][λ][1/(1-x λ)],
                1 + x λ + x^2 λ^2,
TestID->"TruncateToDogree restricts Taylor-expandable series."]]

Module[
        {i, id},
        id = GDO[{i}->{i}][α[i] a[i] + β[i] b[i], ξ[i] x[i] + η[i] y[i], 1];
        VerificationTest[
                GDOTruncateToDegree[2][id],
                GDO[{i}->{i}][0,0,
                        1 +
                        (α[i] a[i] + β[i] b[i] + ξ[i] x[i] + η[i] y[i]) +
                        1/2 (α[i] a[i] + β[i] b[i] + ξ[i] x[i] + η[i] y[i])^2
                ]//ExpandAll,
TestID->"GDOTruncateToDegree truncates the identity appropriately"]]

Module[
        {i, id},
        as = GDO[{i}->{i}][α[i] a[i] , 0, 1];
        VerificationTest[
                GDOTruncateToDegree[2][as],
                GDO[{i}->{i}][0,0, 1 + α[i] a[i] + 1/2 (α[i] a[i])^2]//ExpandAll,
TestID->"GDOTruncateToDegree truncates Exp[a] appropriately."]]

Module[
        {i, id},
        as = GDO[{i}->{i}][α[i] a[i] , 0, 1];
        VerificationTest[
                GDOTruncateToDegree[2][as],
                GDO[{i}->{i}][0,0, 1 + α[i] a[i] + 1/2 (α[i] a[i])^2]//ExpandAll,
TestID->"GDOTruncateToDegree truncates Exp[a] appropriately."]]

Module[
        {i, id},
        id = GDO[{i}->{i}][
                0,0, Exp[α[i] a[i] + β[i] b[i] + η[i] y[i] + ξ[i] x[i]]
        ];
        VerificationTest[
                GDOTruncateToDegree[2][id],
                GDO[{i}->{i}][0,0,
                        1 +
                        (α[i] a[i] + β[i] b[i] + ξ[i] x[i] + η[i] y[i]) +
                        1/2 (α[i] a[i] + β[i] b[i] + ξ[i] x[i] + η[i] y[i])^2
                ]//ExpandAll,
TestID->"GDOTruncateToDegree truncates an exponent appropriately"]]

Module[
        {
                n = 2,
                gdo = Subscript[cm, 1,2->3]
        },
        VerificationTest[
                GDOTruncateToDegree[n]@GDOTruncateToDegree[n]@gdo,
                GDOTruncateToDegree[n]@gdo,
TestID->"GDOTruncateToDegree is idempotent."]]

Module[
        {i, n=4},
        VerificationTest[
                GDOTruncateToDegree[n]@trGuess[i]//ExpandAll,
                trDeg[n][i]//ExpandAll,
TestID->"trGuess matches trDeg[" <> ToString[n] <> "] up to degree"
        <> ToString[n] <> "."]]

Module[
        {i="i", j="j", k="k"},
        VerificationTest[
                cR[i,j]//Subscript[cm, j, i -> k] // trGuess[k],
                cR[i,j]//Subscript[cm, i, j -> k] // trGuess[k],
TestID->"trGuess is dyslexic on a tangle."]]

Module[
        {
                i, j,
                η, β, α, ξ,
                gdo
        },
        gdo = cR[i,j];
        VerificationTest[
                getyCoef[i][gdo][b[i]],
                -((-1 + E^(-ℏ b[i])) x[j])/b[i],
TestID->"getyCoef obtains the linear y-term of an R-matrix."];
        VerificationTest[
                getbCoef[i][gdo],
                ℏ a[j],
TestID->"getbCoef obtains the linear b-term of an R-matrix."];
        VerificationTest[
                getaCoef[j][gdo],
                ℏ b[i],
TestID->"getaCoef obtains the linear a-term of an R-matrix."];
        VerificationTest[
                getxCoef[j][gdo][b[i]],
                ((1 - E^(-ℏ b[i])) y[i])/b[i],
TestID->"getxCoef obtains the linear x-term of an R-matrix."]
        VerificationTest[
                getxyCoef[i][gdo][b[i]],
                0,
TestID->"getxyCoef obtains the xy-term of an R-matrix."]
        VerificationTest[
                getabCoef[i][gdo][b[i]],
                0,
TestID->"getabCoef obtains the linear ab-term of an R-matrix."]
]

Module[
        {
                i,
                ηi, βi, αi, ξi,
                ci,
                gdo
        },
        gdo = GDO[{}->{i}][
                ci + ηi [b[i]]y[i] + βi b[i] + αi a[i] + ξi [b[i]]x[i] +
                σi a[i]b[i] + λi[b[i]] x[i]y[i]
        ];
        VerificationTest[
                getyCoef[i][gdo][b[i]],
                ηi[b[i]],
TestID->"getyCoef obtains the linear y-term of a generic GDO expression."];
        VerificationTest[
                getbCoef[i][gdo],
                βi,
TestID->"getbCoef obtains the linear b-term of a generic GDO expression."];
        VerificationTest[
                getaCoef[i][gdo],
                αi,
TestID->"getaCoef obtains the linear a-term of a generic GDO expression."];
        VerificationTest[
                getxCoef[i][gdo][b[i]],
                ξi[b[i]],
TestID->"getxCoef obtains the linear x-term of a generic GDO expression."];
        VerificationTest[
                getxyCoef[i][gdo][b[i]],
                λi[b[i]],
TestID->"getxyCoef obtains the xy-term of a generic GDO expression."];
        VerificationTest[
                getabCoef[i][gdo][b[i]],
                σi[b[i]],
TestID->"getabCoef obtains the ab-term of a generic GDO expression."];
        VerificationTest[
                getConstCoef[i][gdo][b[i]],
                ci,
TestID->"getConstCoef obtains the constant term of a generic GDO expression."];
VerificationTest[
        GDO[{}->{i}][
                getConstCoef[i][gdo]
                + getyCoef[i][gdo][b[i]]  y[i]
                + getbCoef[i][gdo]        b[i]
                + getaCoef[i][gdo]        a[i]
                + getxCoef[i][gdo][b[i]]  x[i]
                + getabCoef[i][gdo]       a[i] b[i]
                + getxyCoef[i][gdo][b[i]] x[i] y[i]
                ],
        gdo,
TestID->"Extracting coefficients then reforming a GDO element is the identity."]
        ]

Module[
        {
                i,
                gdo,
                t1, t2, t3, t4
        },
        gdo = GDO[{}->{i,j}][
                t1[b[i]] x[i] x[j] + t2[b[i]] x[j] x[j] +
                t3[b[i]] x[i] y[j] + t4[b[i]] x[j] y[j]
        ];
        VerificationTest[
                getyCoef[i][gdo][b[i]],
                t1[b[i]] x[j] + t3[b[i]] y[j],
TestID->"getxCoef[i] only extracts values from index-i terms."]]

Module[
        {
                i,
                gdo,
                t1, t2, t3, t4
        },
        gdo = GDO[{}->{i,j}][
                t1[b[i]] y[i] y[j] + t2[b[i]] y[j] y[j] +
                t3[b[i]] y[i] x[j] + t4[b[i]] y[j] x[j]
        ];
        VerificationTest[
                getyCoef[i][gdo][b[i]],
                t1[b[i]] y[j] + t3[b[i]] x[j],
TestID->"getyCoef[i] only extracts values from index-i terms."]]

Module[
        {n = 5, i = "i", j = "j", k = "k"},
        VerificationTest[
                cR[i,j] // Subscript[cm, i, j -> k] // tr[k]
                        //GDOTruncateToDegree[n],
                cR[i,j] // Subscript[cm, i, j -> k] // trGuess[k]
                        //GDOTruncateToDegree[n],
TestID->"tr matches trGuess on their common domain."]]

Module[
        {
                i,
                η, β, α, ξ, λ,
                ta
        },
        ta = (1-Exp[-α]) t[i];
        VerificationTest[
                GDO[{{},{}}->{{i},{}}][
                        α a[i] + η[b[i]] y[i] + β b[i] +
                        ξ[b[i]] x[i] + λ[b[i]] x[i] y[i]
                ] //tr[i],
                GDO[{{},{}}->{{i},{}}][
                        α a[i] + β ta + t[i](η[ta] ξ[ta] + λ[ta])/(1-t[i] λ[ta])
                ],
TestID->"tr acts as expected on generic GDO element"]]

Module[
        {i="i", j="j", k="k"},
        VerificationTest[
                Subscript[cm, j, i -> k] // tr[k],
                Subscript[cm, i, j -> k] // tr[k],
TestID->"tr is dyslexic."]]

Module[
  {i, j, k, n=3},
  VerificationTest[
    (GDOTruncateToDegree[n][Subscript[cm, i, j -> k]]) // trDeg[n][k],
    (GDOTruncateToDegree[n][Subscript[cm, j, i -> k]]) // trDeg[n][k],
TestID -> "trDeg is dyslexic up to degree "<>ToString[n]<>"."]]

Module[
        {
                rvt=RVT[{Strand[1]},{},{{1,0}}]
        },
        VerificationTest[
                Head[ZFramed[rvt]][[1]],
                \[DoubleStruckCapitalE],
TestID->"ZFramed returns a \[DoubleStruckCapitalE]-element."]]

Module[
        { pCW  = RVT[{Strand[1,2]},{Xp[2,1]},{{1,0},{2, 1}}]
        , pCCW = RVT[{Strand[1,2]},{Xp[1,2]},{{1,0},{2,-1}}]
        },
        VerificationTest[
                ZFramed[pCW]//Simplify,
                ZFramed[pCCW]//Simplify,
TestID -> "ZFramed satisfies R1' for positive kinks."]]

Module[
        { mCW  = RVT[{Strand[1,2]},{Xm[1,2]},{{1,0},{2, 1}}]
        , mCCW = RVT[{Strand[1,2]},{Xm[2,1]},{{1,0},{2,-1}}]
        },
        VerificationTest[
                ZFramed[mCW],
                ZFramed[mCCW],
TestID -> "ZFramed satisfies R1' for negative kinks."]]

Module[
        { doubleTwist = RVT[
                {Strand[1,2,3,4]},
                {Xp[1,2], Xm[3,4]},
                {{1,0},{2,-1},{3,0},{4,1}}]
        , doubleSpiral = RVT[{Strand[1]},{},{{1,0}}]
        },
        VerificationTest[
                ZFramed[doubleTwist],
                ZFramed[doubleSpiral],
TestID -> "ZFramed satisfies cancelling kinks."]]

Module[
        { doubleTwist = RVT[
                {Strand[1,2,3,4]},
                {Xp[1,2], Xm[4,3]},
                {{2,-1},{4,-1},{1,0},{3,0}}]
        , doubleSpiral = RVT[{Strand[1]},{},{{1,-2}}]
        },
        VerificationTest[
                ZFramed[doubleTwist],
                ZFramed[doubleSpiral],
TestID -> "ZFramed satisfies R1' with cancelling negative kinks."]]

(*
Module[
        { i, j, k, l,
        testSX = SXForm[{Loop[i,j], Strand[k,l]},{Xp[j, l], Xm[k, i]}]
        },
        VerificationTest[
                Reindex[testSX],
                SXForm[{Loop[1,2], Strand[3,4]},{Xp[2, 4], Xm[3, 1]}],
TestID -> "Reindex replaces SXForm indices with sequentially ordered positive integers. (1)"
]]

VerificationTest[
  Module[
    { ii
    , j
    , k
    , l
    , testSX = SXForm[{Loop[ii,j], Strand[k,l]},{Xp[j, l], Xm[k, ii]}]
    },
    Reindex[testSX]
  ],
  SXForm[{Loop[1,2], Strand[3,4]},{Xp[2, 4], Xm[3, 1]}],
  TestID ->
    "Reindex replaces SXForm indices with sequentially ordered positive
    integers. (2)"
]
VerificationTest[
  Module[
    { i
    , j
    , k
    , l
    , testRVT = RVT[
        {Loop[i,j], Strand[k,l]},
        {Xp[j, l], Xm[k, i]},
        {{i,0},{j,1},{k,-1}, {l,8}}
      ]
    },
    Reindex[testRVT]
  ],
  RVT[
    {Loop[1,2], Strand[3,4]},
    {Xp[2, 4], Xm[3, 1]},
    {{1,0},{2,1},{3,-1}, {4,8}}
  ],
  TestID ->
    "Reindex replaces RVT local variable indices with sequentially ordered
    positive integers."
]
VerificationTest[
   testRVT = RVT[
      {Loop[0,1]},
      {Xp[0, 1]},
      {{0,0},{1,1}}
    ];
    Reindex[testRVT]
  ,
  RVT[
    {Loop[1,2]},
    {Xp[1, 2]},
    {{1,0},{2,1}}
  ],
  TestID ->
    "Reindex replaces RVT integer indices with sequentially ordered
    positive integers."
]
VerificationTest[
   testRVT = RVT[
      {Loop[0,1], Strand[-1,-2]},
      {Xp[0, 1], Xm[-2, -1]},
      {{0,0},{1,1},{-1,-1}, {-2,8}}
    ];
    Reindex[testRVT]
  ,
  RVT[
    {Loop[1,2], Strand[3,4]},
    {Xp[1, 2], Xm[4, 3]},
    {{1,0},{2,1},{3,-1}, {4,8}}
  ],
  TestID ->
    "Reindex replaces RVT integer indices with sequentially ordered
    positive integers."
]
*)
