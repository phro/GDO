Module[
  {i, j},
  VerificationTest[
    coinv[i][Subscript[a, j] Subscript[y, i] Subscript[x, i]],
    Subscript[a, j] Subscript[t, i],
TestID->"coinv[i] reduces xy to t"]]

Module[
  {i, j},
  VerificationTest[
    coinv[i][Subscript[a, j] Subscript[a, i] Subscript[y, i]^5 Subscript[x, i]^5],
    5! Subscript[a, j] Subscript[a, i] Subscript[t, i]^5,
TestID->"coinv[i] reduces a(xy)^5 to at^5"]]

Module[
  {i, j},
  VerificationTest[
    coinv[i][3 Subscript[x, i]^2 Subscript[y, i]^2 + Subscript[a, j] Subscript[a, i] Subscript[y, i]^5 Subscript[x, i]^5],
    3*2! Subscript[t, i]^2 + 5! Subscript[a, j] Subscript[a, i] Subscript[t, i]^5,
TestID->"coinv[i] reduces functions on sums of monomials."]]

Module[
  {i,
  yi, bi, ai, xi,
  ti,
  ηi, βi, αi, ξi
  },
  yi = Subscript[y, i];
  bi = Subscript[b, i];
  ai = Subscript[a, i];
  xi = Subscript[x, i];
  ti = Subscript[t, i];
  ηi = Subscript[η, i];
  βi = Subscript[β, i];
  αi = Subscript[α, i];
  ξi = Subscript[ξ, i];
  VerificationTest[
    trGenFunc[i][3],
    ηi αi ξi (ai ti) + (1/2) βi αi^2 (2 ai ti - ti) + (1/6) αi^3 (ai^3) + 
    ηi ξi (ti) + βi αi (ti) + (1/2) αi^2 (ai^2) + 
    αi ai +
    1,
TestID->"trGenFunc[i] is correct up to degree 3."]]

Module[
        {i},
        VerificationTest[
                trDeg[i][4][[3]],
                trGenFunc[i][4],
TestID->"trDeg produces trGenFunc's output."]]

Module[{i, j},
  VerificationTest[
    Subscript[\[DoubleStruckCapitalE],{i}->{j}][
      Subscript[α, i]Subscript[b,j],
      0,
      1
    ] // ScaleByLambda[j],
    Subscript[\[DoubleStruckCapitalE],{i}->{j}][
      λ Subscript[α, i]Subscript[b,j],
      0,
      1
    ],
    TestID -> "ScaleByLambda scales b by the weight-tracker."
  ]
]

Module[{i, j},
  VerificationTest[
    Subscript[\[DoubleStruckCapitalE],{i}->{j}][
      Subscript[β, i]Subscript[a,j],
      0,
      1
    ] // ScaleByLambda[j],
    Subscript[\[DoubleStruckCapitalE],{i}->{j}][
      λ Subscript[β, i]Subscript[a,j],
      0,
      1
    ],
    TestID -> "ScaleByLambda scales a by the weight-tracker."
  ]
]

Module[{i, j},
  VerificationTest[
    Subscript[\[DoubleStruckCapitalE],{i}->{j}][
      0,
      Subscript[ξ, i]Subscript[y,j],
      1
    ] // ScaleByLambda[j],
    Subscript[\[DoubleStruckCapitalE],{i}->{j}][
      0,
      λ Subscript[ξ, i]Subscript[y,j],
      1
    ],
    TestID -> "ScaleByLambda scales y by the weight-tracker."
  ]
]

Module[{i, j},
  VerificationTest[
    Subscript[\[DoubleStruckCapitalE],{i}->{j}][
      0,
      Subscript[β, i]Subscript[x,j],
      1
    ] // ScaleByLambda[j],
    Subscript[\[DoubleStruckCapitalE],{i}->{j}][
      0,
      λ Subscript[β, i]Subscript[x,j],
      1
    ],
    TestID -> "ScaleByLambda scales x by the weight-tracker."
  ]
]

Module[
  { pCW  = RVT[{Strand[1,2]},{Xp[2,1]},{{1,0},{2,1 }}]
  , pCCW = RVT[{Strand[1,2]},{Xp[1,2]},{{1,0},{2,-1}}]
  },
  VerificationTest[
    ZFramed[pCW]//Simplify,
    ZFramed[pCCW]//Simplify,
  TestID -> "ZFramed satisfies R1' for positive kinks."
  ]
]
Module[
  { mCW  = RVT[{Strand[1,2]},{Xm[1,2]},{{1,0},{2,1 }}]
  , mCCW = RVT[{Strand[1,2]},{Xm[2,1]},{{1,0},{2,-1}}]
  },
  VerificationTest[
    ZFramed[mCW],
    ZFramed[mCCW],
  TestID -> "ZFramed satisfies R1' for negative kinks."
  ]
]
Module[
  { doubleTwist = RVT[
    {Strand[1,2,3,4]},
    {Xp[1,2], Xm[4,3]},
    {{2,-1},{4,-1},{1,0},{3,0}}]
  , straightStrand = RVT[{Strand[1]},{},{{1,0}}]
  },
  VerificationTest[
    Z[doubleTwist],
    Z[straightStrand],
  TestID -> "R1' ZFramed with cancelling negative kinks."
  ]
]

VerificationTest[
  Module[
    { i
    , j
    , k
    , l
    , testSX = SXForm[{Loop[i,j], Strand[k,l]},{Xp[j, l], Xm[k, i]}]
    },
    Reindex[testSX]
  ],
  SXForm[{Loop[1,2], Strand[3,4]},{Xp[2, 4], Xm[3, 1]}],
  TestID ->
    "Reindex replaces SXForm indices with sequentially ordered positive
    integers. (1)"
]
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

Module[
  {i, j, k},
  VerificationTest[
    (TruncateToDegree[4][
      Subscript[S\[HBar], i] Subscript[S\[HBar], j] //
      (Subscript[cm, i, j -> k] /. U2l)] //
      ExpandAll) // trDeg[k][8]
    ,
    (TruncateToDegree[4][
      Subscript[S\[HBar], i] Subscript[S\[HBar], j] //
      (Subscript[cm, j, i -> k] /. U2l)] //
      ExpandAll) // trDeg[k][8]
    ,
    TestID -> "trace is dyslexic up to degree 4."
  ]
]

