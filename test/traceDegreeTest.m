Once[
  Get["/home/jesse/ed/k/co/traceDegree.m"]
]

(* testCoinvVanishesOnBrackets := VerificationTest[
    Module[
      {i},
      Table[coinv[i][#]]
] *)

(* On[Assert]; *)

(* testCCnIsPowersOfCC; *)
(* testSℏBehavesWellWithLists; *)
(* testTruncateToDegreeIsIdempotent; *)

(* testTraceIsDyslexic; *)

(* testZFramedSatisfiesRibbonR1; *)
(* testZFramedRespectsWhirling; *)

testSuite =
  { testsZFramedReidemeister
  , testsPDNotation
  , testAddWeight
  }

testAddWeight := VerificationTest[
  inputGDO =
    Subscript[\[DoubleStruckCapitalE],{i,j}->{k}][
      Subscript[α, i]Subscript[b,j]+ Subscript[β, i]Subscript[a,j],
      Subscript[η, i]Subscript[x,j]+ Subscript[y, i]Subscript[ξ,j],
      Subscript[\[ScriptCapitalA], i]Subscript[B,j]
    ];inputGDO // ScaleByLambda[i] // ScaleByLambda[j],
  Subscript[\[DoubleStruckCapitalE],{i,j}->{k}][
    λ Subscript[α, i]Subscript[b,j]+ λ Subscript[β, i]Subscript[a,j],
    λ Subscript[η, i]Subscript[x,j]+ λ Subscript[y, i]Subscript[ξ,j],
    Subscript[\[ScriptCapitalA], i]^λ Subscript[B,j]
  ],
  TestID -> "AddWeight scales each variable by the weight-tracker."
]

testsZFramedReidemeister :=
  { VerificationTest[
      Module[
        { pCW  = SXForm[{Loop[1,2]},{Xp[2,1]}]
        , pCCW = SXForm[{Loop[1,2]},{Xp[1,2]}]
        },
        ZFramed[pCW]==ZFramed[pCCW]
      ],
      TestID -> "ZFramed satisfies R1' for positive kinks."
    ]
  , VerificationTest[
      Module[
        { mCW  = SXForm[{Loop[1,2]},{Xm[1,2]}]
        , mCCW = SXForm[{Loop[1,2]},{Xm[2,1]}]
        },
        ZFramed[mCW]==ZFramed[mCCW]
      ],
      TestID ->
        "ZFramed satisfies R1' for negative kinks."
    ]
  , VerificationTest[
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
  }

testsPDNotation :=
  { VerificationTest[
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
  , VerificationTest[
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
  , VerificationTest[
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
  , VerificationTest[
      Module[
        { testRVT = RVT[
            {Loop[0,1]},
            {Xp[0, 1]},
            {{0,0},{1,1}}
          ]
        },
        Reindex[testRVT]
      ],
      RVT[
        {Loop[1,2]},
        {Xp[1, 2]},
        {{1,0},{2,1}}
      ],
      TestID ->
        "Reindex replaces RVT integer indices with sequentially ordered
        positive integers."
    ]
  , VerificationTest[
      Module[
        { testRVT = RVT[
            {Loop[0,1], Strand[-1,-2]},
            {Xp[0, 1], Xm[-2, -1]},
            {{0,0},{1,1},{-1,-1}, {-2,8}}
          ]
        },
        Reindex[testRVT]
      ],
      RVT[
        {Loop[1,2], Strand[3,4]},
        {Xp[1, 2], Xm[4, 3]},
        {{1,0},{2,1},{3,-1}, {4,8}}
      ],
      TestID ->
        "Reindex replaces RVT integer indices with sequentially ordered
        positive integers."
    ]
  }

testTraceIsDyslexic := Module[
  {i, j, k},
  Echo["testTraceIsDyslexic"];
  Assert[(
    (TruncateToDegree[4][
      Subscript[S\[HBar], i] Subscript[S\[HBar], j] //
        (Subscript[cm, i, j -> k] /. U2l)] //
        ExpandAll) // tr[k][8]
  ) ==
  (
    (TruncateToDegree[4][
      Subscript[S\[HBar], i] Subscript[S\[HBar], j] //
        (Subscript[cm, j, i -> k] /. U2l)] //
        ExpandAll) // tr[k][8]
  )]
]

testSℏBehavesWellWithLists := Module[{i, j},
  Echo["Testing whether Sℏ works on lists..."];
  Assert[Sℏ[{i}] == Sℏ[i]];
  Assert[Sℏ[{i,j}] == Subscript[\[DoubleStruckCapitalE], {i, j} -> {i, j}][
    ℏ(Subscript[α, i] Subscript[a, i] +Subscript[β, i] Subscript[b, i]
     +Subscript[α, j] Subscript[a, j] +Subscript[β, j] Subscript[b, j]),
    ℏ(Subscript[ξ, i] Subscript[x, i] +Subscript[η, i] Subscript[y, i]
     +Subscript[ξ, j] Subscript[x, j] +Subscript[η, j] Subscript[y, j]),
    1
    ]
  ];
]

testTruncateToDegreeIsIdempotent := Module[
  {
    i, j, k,
    n = 3,
    GDO,
    TGDO
  },
  Echo["Testing whether TruncateToDegree is idempotent"];
  GDO = Subscript[cm, i, j -> k];
  TGDO = TruncateToDegree[n][GDO];
  (* Print[TGDO]; *)
  Assert[((TruncateToDegree[n]@TGDO)/.{ℏ->1}) == ((TGDO)/.{ℏ->1})]
];

testCCnIsPowersOfCC := Module[
  {i,j},
  Echo["Testing whether CCn is a power of CC..."]
  Assert[CCn[i][1] == CC[i]];
  Assert[CCn[i][-1] == CCi[i]];
  Assert[CCn[i][2] == (CC[i] CC[j] //Subscript[cm, i,j->i])];
]

(* Convert a ybax word to GDO form *)
Subscript[toE, i_][w_]:= Subscript[\[DoubleStruckCapitalE],{} -> {i}][0,0,w/.(#->Subscript[#, i]&/@{y,b,a,x})];

(* Write sl2-expressions in tensor form *)
Bracket[i_,j_][X_,Y_]:= X Y - ((Y X)/.{i->j,j->i});
Monomial[i_][n1_,n2_,n3_,n4_]:=
  Subscript[y, i]^n1 Subscript[b, i]^n2 Subscript[a, i]^n3 Subscript[x, i]^n4;

Subscript[Bracket, i_,j_][X_,Y_]:=Bracket[i,j][X,Y];
Subscript[Monomial, i_][n1_,n2_,n3_,n4_]:= Monomial[i][n1,n2,n3,n4];

testMonomialMakesMonomials := Module[
  {i},
  Echo["Testing whether Monomial generates degree 0 monomials..."];
  Assert[Monomial[i][0,0,0,0] == 1];
  (* Assert[Monomial[i][0,0,0,0] == 1]; *)
]

testBracketIsAnticommutative := Module[
  {
    i,
    j,
    mi = Monomial[i][1, 2, 3, 4],
    mj = Monomial[j][1, 2, 3, 4]
  },
  Echo["Testing whether the bracket is anticommutative..."];
  Assert[Bracket[i, j][mi, mj] == 0]
]

(* testMonomialMakesMonomials; *)
(* testBracketIsAnticommutative; *)

(* Front-end convenience notation *)
Subscript[Xp, a_,b_]:= Xp[a,b]
Subscript[Xm, a_,b_]:=Xm[a,b]


(* Conversion from SXForm back to PD notation
 * (use case: taking advantage of PD-drawing functions)
 *)
PD[L_SXForm]:=Module[{s,z,is},
  {s,z}=List@@L;
  succ=Flatten@Table[MapThread[RuleDelayed,{i,RotateLeft[i]}],{i,List@@@s}];
  PD@@(z/.{
    Xp[i_,j_]:>X[j,i/.succ,j/.succ,i],
    Xm[i_,j_]:>X[j,i,j/.succ,i/.succ]
  })
]




Subscript[cK, k_]:=Module[{i,j},Subscript[cR, i,j]//Subscript[cm, i,j->k]]




Subscript[\!\(\*OverscriptBox[\(cK\), \(_\)]\), k_]:= Module[
  {i,j},
  Subscript[\!\(\*OverscriptBox[\(cR\), \(_\)]\), i,j]//Subscript[cm, i,j->k]
]


SetCrossing[K_, l_Integer, s_] := Module[
  {pd, n},
  pd = PD[K];
  If[PositiveQ[pd[[l]]],
    If[s == "-", pd[[l]] = RotateRight@pd[[l]]],
    If[s == "+", pd[[l]] = RotateLeft@pd[[l]]]
  ];
  pd];

(*
 * MVA restricted to its type-at-most-k part; takes an optional collection of
 * crossings to convert to double-points.
 * TODO: test this
 *)
MVA[k_Integer,L_] := Series[
  (ℏ MultivariableAlexander[L][t] /.
    t[i_] :> Exp[ℏ x[i]]),
    {ℏ,0,k}]

MVA[k_Integer,L_, {i1_, is___}] :=
  MVA[k, SetCrossing[L, i1, "+"], {is}] -
  MVA[k, SetCrossing[L, i1, "-"], {is}];

MVA[k_Integer, L_, {}] := MVA[k, L]

(*
 * Given a collection of link diagrams and a degree, turn a random collection
 * (for now, let's stick to the first n+1) of the crossings (n+1 for each link)
 * into double points, then evaluate the MVA's (supposed) degree-n component.
 *)
TestMVAVassiliev[Ls_,n_] := Union[Normal@MVA[n, #, Range[n+1]]&/@Ls]

(* True for 6,9,4 and 6,9,5 at least: *)
Test[l_,u_,d_] := TestMVAVassiliev[AllKnots[{l,u}],d]

(*
 * Double points (for use in testing Vassiliev invariance); requires more
 * cooperation from the SXForm to expand linear combinations.
 *)
Xd[n_,m_] := Xp[n,m]-Xm[n,m]

MVARepeats := Map[First, Select[SplitBy[SortBy[Table[L -> MultivariableAlexander[L][t], {L, AllLinks[]}], Last],
Last], Length[#] > 1 &],{2}]

(* What follows is a collection of computations which suggest that where the
trace vanishes (to low degree) where the MVA does not, this is because these
links also vanish to high degree in the finite-type expansion of the MVA *)
MaybeSmallMVA := Select[Flatten[Take[MVARepeats,2]],((trZ[2, #])[[3]])==1&]

traces := trZ[2, #]&/@Flatten[Take[MVARepeats,{3,5}]]

(* Vanishing trace but nonvanishing MVA: *)
L1140 := MVA[7,Link[11, Alternating, 40]]

vanishingtrace := MVA[7,#]&/@Flatten[Take[MVARepeats,{3,5}]]

(*
 * Define the writhe-n unloop:
 *)
UnloopOver[n_] := CompoundExpression[
  Xn[m_]:=If[m>=0,Xp,Xm],
  SXForm[List[Loop@@Range[2 Abs[n]+1]],Table[Xn[n][2 i-1,2 i],{i,Abs[n]}]]
]

UnloopUnder[n_] := CompoundExpression[
  Xn[m_]:=If[m>=0,Xp,Xm],
  SXForm[List[Loop@@Range[2 Abs[n]+1]],Table[Xn[n][2 i,2 i-1],{i,Abs[n]}]]
]


PrePostTrace[deg_, L_] := Table[
  Module[{z},
    z=ZFramed[L];
    {
      z,
      (Times @@ Table[tr[i][deg], {i, #[[0, 2, 2] ]} ])[#]&[
        Simplify[TruncateToDegree[2 deg][z]]
      ]
    }
  ]
]

importantTrace := trZ[1,Link[11,NonAlternating,334]]

c[i_][n_,k_,r_] := coinv[i][Monomial[i][k,n,n+r,k]]

tsub := {t:>Subscript[t, i], a:>Subscript[a, i]}

(* PASSED *)
ctest0 := Union@Flatten@Table[
  c[i][n,k,0]-
  (n! k! t^(n+k)/.tsub),
  {n,0,3}, {k,0,3}]

(* PASSED *)
ctest1 := Union@Flatten@Table[
  c[i][n,k,1]-
  ((n+1)! k! (a-n/2)(t^(n+k))/.tsub)//Simplify,
  {n,0,3}, {k,0,3}]


(*
 * Now to test whether the partial trace is well-defined given an arbitrary
 * choice must be made for where a component is opened.
 *)

(*
 * RotateSXForm[L_SXForm] := L with all indices rotated to the right (1 <- 2 <- 3 <- ...)
 *)

RotateSXForm[L_SXForm, i_Integer, n_Integer] := Module[
  {
    skeleton = L[[1]],
    xings    = L[[2]],
    is,
    isub
  },
  is = List@@@skeleton[[i]];
  isub = (MapThread[#1->#2&,{#,RotateRight[#,n]}]&/@is);
  SXForm[skeleton, xings/.isub]
];
RotateSXForm[L_SXForm] := RotateSXForm[L,1];
RotateSXForm::badargs = "RotateSXForm is defined only for diagrams in SXForm.";
RotateSXForm[___] := Message[RotateSXForm::badargs];
RotateSXForms[L_SXForm, max_Integer] := Module[
  {
    skeleton = L[[1]],
    xings    = L[[2]],
    is,
    isSub,
    rotateVals
  },
  is = List@@@skeleton;
  rotateVals = Tuples[Range[max], Length@is];
  isPair = MapThread[List, is, rotateVals];
  isSub = Join@@(MapThread[#1->#2&,{#[[1]],RotateRight[#[[1]],#[[2]]]}]&/@is);
  SXForm[skeleton, xings/.isSub]
]

testRotationNumbersAreSkeletonIndependent := Module[
  {
    l1 = SXForm[Link[9, Alternating, 3]],
    l2 = Reindex@SXForm[{Loop[1, 2, 3, 4],
  Loop[12, 13, 14, 15, 16, 17, 18, 5, 6, 7, 8, 9, 10, 11]}, {Xm[1, 6],
   Xm[7, 16], Xm[17, 4], Xp[5, 12], Xp[3, 8], Xp[9, 14], Xp[13, 10],
  Xp[11, 18], Xp[15, 2]}]
  },
  Echo["testRotationNumbersAreSkeletonIndependent"];
  Print[RotationNumbers[l1]];
  Print[RotationNumbers[l2]];
  Assert[RotationNumbers[l1] == RotationNumbers[l2]];
]

(* testRotationNumbersAreSkeletonIndependent *)

(* Return all partial traces of the link. *)
ptrZs[deg_, L_] := Module[
  {
    Z = Zdeg[deg, L],
    is,
    comps
  },
  is = Z[[0, 2, 2]];
  comps = Subsets[is,{Length[is]-1}];
  (Times @@ Table[tr[i][deg], {i, #}])[Z]&/@ comps
]
(*
 * NB: This function currently produces a list of values, one for each opened
 * component. How does one compare equality between such lists of GDO elements?
 *)

(* Subsets[#,{?}] *)



(* k[3] = Reindex@SXForm[ *)
  (* {Loop[1, 2], Loop[3, 4]}, *)
  (* {Xp[4, 1], Xm[3,2]} *)
(* ] *)


(* Testing... *)

(* Echo["Begin Testing..."]; *)

(* Echo["Verify the trace coequalizes m and m^op:"]; *)
(* Module[{i, j, k, deg=3}, *)
  (* Print@Series[ *)
      (* Subtract@@ *)
      (* (Normal[ *)
          (* Subscript[Sℏ, i] Subscript[Sℏ, j] // # /. U2l // tr[k][deg] *)
        (* ][[3]]&/@ {Subscript[cm, i, j -> k], Subscript[cm, j, i -> k]}), *)
      (* {ℏ, 0, deg + 1} *)
  (* ] // Simplify *)
(* ]; *)
(* Echo["Done verifying."] *)

(* MyLink := SXForm[Link[4,Alternating,1]] *)
(* MyLink := SXForm[Link[7,Alternating,7]] *)
(* Print@RotateSXForm[MyLink] *)
(* RotateSXForm[banana] *)

(* The following is a good sign: *)
(* Print@#[[3]]&/@(ptrZ[2,MyLink]== ptrZ[2,RotateSXForm[MyLink,2]]) *)

(* Print@ptrZ[2,MyLink] *)
(* Print@ptrZ[2,RotateSXForm[MyLink]] *)
(* Z1 = ptrZs[1, MyLink]; *)
(* Z2 = ptrZs[1, RotateSXForm[MyLink]]; *)

(* FIX: Important: These do not have the same value *)
MyLink1 := SXForm[TorusKnot[4,2]]
MyLink2 := SXForm[TorusKnot[2,4]]
(* MyLink1 := SXForm[TorusKnot[6,2]] *)
(* MyLink2 := SXForm[TorusKnot[2,6]] *)
(* MyLink1 := SXForm[TorusKnot[1,2]] *)
(* MyLink2 := SXForm[TorusKnot[2,1]] *)
pZ1 := ptrZs[1, MyLink1];
pZ2 := ptrZs[1, MyLink2];

(* FIX: Even more important: These do not have the same value: *)
Z1 := Z[MyLink1];
Z2 := Z[MyLink2];
Zd1 := Zdeg[2, MyLink1];
Zd2 := Zdeg[2, MyLink2];

k[1] := Reindex@SXForm[
  {Loop[-1,-2], Loop[1,2]},
  {Xm[-2,1], Xm[2,-1]}
]

k["1.5"] := Reindex@SXForm[
  {Loop[-1,-2], Loop[1,2]},
  {Xm[1,-1], Xm[-2,2]}
]

k[2] := Reindex@SXForm[
  {Loop[-1,-2], Loop[1,2,3,4,5,6]},
  {Xm[-2,1], Xp[5, 2], Xm[4,3], Xm[6,-1]}
]

k[3] := Reindex@SXForm[
  {Loop[-1,-2], Loop[1,2,3,4,5,6]},
  {Xp[6, 1], Xm[-1, 2], Xm[4, 3], Xm[5, -2]}
]

k[4] := Reindex@SXForm[
  {Loop[-1,-2], Loop[1,2,3,4,5,6]},
  {Xp[6, 1], Xm[-1, 2], Xm[3, 4], Xm[5, -2]}
]

k["5,6 pre"] := Reindex@SXForm[
  {Loop[-1,-2], Loop[1,2], Loop[3,4,5,6]},
  {Xm[3, -2], Xm[4, 5], Xp[6, 1], Xm[-1, 2]}
]

k[5] := Reindex@SXForm[
  {Loop[-1,-2], Loop[1,2,3,4,5,6]},
  {Xm[3, -2], Xm[4, 5], Xp[6, 1], Xm[-1, 2]}
]

k["6'"] := Reindex@SXForm[
  {Loop[-1,-2], Loop[3,4,5,6,1,2]},
  {Xm[3, -2], Xm[4, 5], Xp[6, 1], Xm[-1, 2]}
]

k[6] := Reindex@SXForm[
  {Loop[-1,-2], Loop[1,2,3,4,5,6]},
  {Xm[1, -2], Xm[2, 3], Xp[4, 5], Xm[-1, 6]}
]

k[7] := Reindex@SXForm[
  {Loop[-1,-2], Loop[1,2]},
  {Xm[1,-2], Xm[-1,2]}
]

(*
 * Currently this table has _two_ changes in value, presumably each
 * corresponding to some bug in the program. Time to dig deeper.
 *)
hopfLinksTable := Table[
  {i, k[i], DrawMorseLink[k[i]], MultivariableAlexander[k[i]][t]//Simplify, Zdeg[4, k[i]] // tr[3][4]
  (*, ptrZs[4, k[i]]*)},
  {i, {1, "1.5", 2, 3, 4, 5, 6, "5,6 pre", "6'", 7}}] // TableForm

clockwiseAnticlockwiseLoopComparison:= MapThread[List,
  {
    (ZFramed/@Table[UnloopOver[i],{i,-3,3}]),
    (ZFramed/@Table[UnloopUnder[i],{i,-3,3}])
  }
]

testZFramedRespectsWhirling := Module[{},
Echo["Test whether ZFramed respects the Whirling relation."];
Assert[True];  (* TODO: implement when C_i's are non-central. *)
]

(* Off[Assert]; *)
(* Echo[End Testing]; *)
