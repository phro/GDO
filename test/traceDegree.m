Module[{i, j, k},
  VerificationTest[
      Subscript[\[DoubleStruckCapitalE],{i,j}->{k}][
        Subscript[α, i]Subscript[b,j]+ Subscript[β, i]Subscript[a,j],
        Subscript[η, i]Subscript[x,j]+ Subscript[y, i]Subscript[ξ,j],
        Subscript[\[ScriptCapitalA], i]Subscript[B,j]
      ] // ScaleByLambda[i] // ScaleByLambda[j],
    Subscript[\[DoubleStruckCapitalE],{i,j}->{k}][
      λ Subscript[α, i]Subscript[b,j]+ λ Subscript[β, i]Subscript[a,j],
      λ Subscript[η, i]Subscript[x,j]+ λ Subscript[y, i]Subscript[ξ,j],
      Subscript[\[ScriptCapitalA], i]^λ Subscript[B,j]
    ],
    TestID -> "ScaleByLambda scales each variable by the weight-tracker."
  ]
]

VerificationTest[
  Module[
    { pCW  = SXForm[{Loop[1,2]},{Xp[2,1]}]
    , pCCW = SXForm[{Loop[1,2]},{Xp[1,2]}]
    },
    ZFramed[pCW]==ZFramed[pCCW]
  ],
  TestID -> "ZFramed satisfies R1' for positive kinks."
]
VerificationTest[
  Module[
    { mCW  = SXForm[{Loop[1,2]},{Xm[1,2]}]
    , mCCW = SXForm[{Loop[1,2]},{Xm[2,1]}]
    },
    ZFramed[mCW]==ZFramed[mCCW]
  ],
  TestID ->
    "ZFramed satisfies R1' for negative kinks."
]
VerificationTest[
  Module[
    { doubleTwist = RVT[
      {Strand[1,2,3,4]},
      {Xp[1,2], Xm[4,3]},
      {{2,-1},{4,-1},{1,0},{3,0}}]
    , straightStrand = RVT[{Strand[1]},{},{{1,0}}]
    },
    Z[doubleTwist] == Z[straightStrand]
  ],
  TestID ->
    "R1' ZFramed with cancelling negative kinks."
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
      ExpandAll) // tr[k][8]
    ,
    (TruncateToDegree[4][
      Subscript[S\[HBar], i] Subscript[S\[HBar], j] //
      (Subscript[cm, j, i -> k] /. U2l)] //
      ExpandAll) // tr[k][8]
    ,
    TestID -> "trace is dyslexic up to degree 4."
  ]
]

