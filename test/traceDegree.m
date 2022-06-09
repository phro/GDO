Module[
        {i, j,
        ηi, βi, αi, ξi,
        yj, bj, aj, xj
        },
        ηi = Subscript[η, i];
        βi = Subscript[β, i];
        αi = Subscript[α, i];
        ξi = Subscript[ξ, i];
        τi = Subscript[τ, i];
        yj = Subscript[y, j];
        bj = Subscript[b, j];
        aj = Subscript[a, j];
        xj = Subscript[x, j];
        tj = Subscript[t, j];
        VerificationTest[
                GDO[{i}->{j}][αi aj+ βi bj + τi tj,ξi xj + ηi yj, 1],
                Subscript[sσ,i ->j],
TestID->"GDO-notation returns \[DoubleStruckCapitalE]-notation."]]

Module[
        {i, j, yi, xi, ti, aj},
        yi = Subscript[y, i];
        xi = Subscript[x, i];
        ti = Subscript[t, i];
        aj = Subscript[a, j];
        VerificationTest[
                coinv[i][aj yi xi],
                aj ti,
TestID->"coinv[i] reduces xy to t"]]

Module[
        {i, j, yi, ai, xi, ti, aj},
        yi = Subscript[y, i];
        ai = Subscript[a, i];
        xi = Subscript[x, i];
        ti = Subscript[t, i];
        aj = Subscript[a, j];
        VerificationTest[
                coinv[i][aj ai yi^5 xi^5],
                5! aj ai ti^5,
TestID->"coinv[i] reduces a(xy)^5 to at^5"]]

Module[
        {i, j, yi, ai, xi, ti, aj},
        yi = Subscript[y, i];
        ai = Subscript[a, i];
        xi = Subscript[x, i];
        ti = Subscript[t, i];
        aj = Subscript[a, j];
        VerificationTest[
                coinv[i][3 xi^2 yi^2 + aj ai yi^5 xi^5],
                3*2! ti^2 + 5! aj ai ti^5,
TestID->"coinv[i] reduces functions on sums of monomials."]]

Module[
        {i, yi, bi, ai, xi, ti, ηi, βi, αi, ξi},
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
                ηi αi ξi (ai ti) + 1/2 βi αi^2 (2 ai ti - ti) + 1/6 αi^3 ai^3 +
                ηi ξi (ti) + βi αi (ti) + 1/2 αi^2 (ai^2) +
                αi ai +
                1,
TestID->"trGenFunc[i] is correct up to degree 3."]]

Module[
        {i},
        VerificationTest[
                trDeg[i][4][[3]],
                trGenFunc[i][4],
TestID->"trDeg produces trGenFunc's output."]]

Module[
        {i, j, ai, bj},
        ai = Subscript[a, i];
        bj = Subscript[b, j];
        VerificationTest[
                GDO[{i}->{j}][αi bj, 0, 1] //
                        ScaleByLambda[j],
                GDO[{i}->{j}][λ αi bj, 0, 1],
TestID -> "ScaleByLambda scales b by the weight-tracker."]]

Module[
        {i, j, βi, aj},
        βi = Subscript[β, i];
        aj = Subscript[a, j];
        VerificationTest[
                GDO[{i}->{j}][βi aj , 0, 1] //
                        ScaleByLambda[j],
		GDO[{i}->{j}][λ βi aj, 0, 1],
TestID -> "ScaleByLambda scales a by the weight-tracker."]]

Module[
        {i, j, ξi, yj},
        ξi = Subscript[ξ, i];
        yj = Subscript[y, j];
	VerificationTest[
                GDO[{i}->{j}][0, ξi yj, 1] //
                        ScaleByLambda[j],
		GDO[{i}->{j}][0, λ ξi yj, 1],
TestID -> "ScaleByLambda scales y by the weight-tracker."]]

Module[
        {i, j, βi, xj},
        βi = Subscript[ξ, i];
        xj = Subscript[y, j];
	VerificationTest[
                GDO[{i}->{j}][0, βi xj, 1] //
                        ScaleByLambda[j],
		GDO[{i}->{j}][0, λ βi xj, 1],
TestID -> "ScaleByLambda scales x by the weight-tracker."]]

Module[
        {i, id, yi, bi, ai, xi, ti, ηi, βi, αi, ξi},
        yi = Subscript[y, i];
        bi = Subscript[b, i];
        ai = Subscript[a, i];
        xi = Subscript[x, i];
        ti = Subscript[t, i];
        ηi = Subscript[η, i];
        βi = Subscript[β, i];
        αi = Subscript[α, i];
        ξi = Subscript[ξ, i];
        id = GDO[{i}->{i}][αi ai + βi bi, ξi xi + ηi yi, 1];
        VerificationTest[
                TruncateToDegree[2][id],
                GDO[{i}->{i}][0,0,
                        1 +
                        (αi ai + βi bi + ξi xi + ηi yi) +
                        1/2 (αi ai + βi bi + ξi xi + ηi yi)^2
                ]//ExpandAll,
TestID->"TruncateToDegree truncates the identity appropriately"]]

Module[
        {i, id, yi, bi, ai, xi, ti, ηi, βi, αi, ξi},
        yi = Subscript[y, i];
        bi = Subscript[b, i];
        ai = Subscript[a, i];
        xi = Subscript[x, i];
        ti = Subscript[t, i];
        ηi = Subscript[η, i];
        βi = Subscript[β, i];
        αi = Subscript[α, i];
        ξi = Subscript[ξ, i];
        as = GDO[{i}->{i}][αi ai , 0, 1];
        VerificationTest[
                TruncateToDegree[2][as],
                GDO[{i}->{i}][0,0, 1 + αi ai + 1/2 (αi ai)^2]//ExpandAll,
TestID->"TruncateToDegree truncates Exp[a] appropriately."]]

Module[
        {i, id, yi, bi, ai, xi, ti, ηi, βi, αi, ξi},
        yi = Subscript[y, i];
        bi = Subscript[b, i];
        ai = Subscript[a, i];
        xi = Subscript[x, i];
        ti = Subscript[t, i];
        ηi = Subscript[η, i];
        βi = Subscript[β, i];
        αi = Subscript[α, i];
        ξi = Subscript[ξ, i];
        as = GDO[{i}->{i}][αi ai , 0, 1];
        VerificationTest[
                TruncateToDegree[2][as],
                GDO[{i}->{i}][0,0, 1 + αi ai + 1/2 (αi ai)^2]//ExpandAll,
TestID->"TruncateToDegree truncates Exp[a] appropriately."]]

Module[
        {i, id, yi, bi, ai, xi, ti, ηi, βi, αi, ξi},
        yi = Subscript[y, i];
        bi = Subscript[b, i];
        ai = Subscript[a, i];
        xi = Subscript[x, i];
        ti = Subscript[t, i];
        ηi = Subscript[η, i];
        βi = Subscript[β, i];
        αi = Subscript[α, i];
        ξi = Subscript[ξ, i];
        id = GDO[{i}->{i}][
                0,0, Exp[αi ai + βi bi + ηi yi + ξi xi]
        ];
        VerificationTest[
                TruncateToDegree[2][id],
                GDO[{i}->{i}][0,0,
                        1 +
                        (αi ai + βi bi + ξi xi + ηi yi) +
                        1/2 (αi ai + βi bi + ξi xi + ηi yi)^2
                ]//ExpandAll,
TestID->"TruncateToDegree truncates an exponent appropriately"]]

Module[
        {
                n = 2,
                gdo = Subscript[cm, 1,2->3]
        },
        VerificationTest[
                TruncateToDegree[n]@TruncateToDegree[n]@gdo,
                TruncateToDegree[n]@gdo,
TestID->"TruncateToDegree is idempotent."]]

Module[
        {i="i", j="j", k="k"},
        VerificationTest[
                cR[i,j]//Subscript[cm, j, i -> k] // trGuess[k],
                cR[i,j]//Subscript[cm, i, j -> k] // trGuess[k],
TestID->"trGuess is dyslexic on a tangle."]]

Module[
        {i="i", j="j", k="k"},
        VerificationTest[
                Subscript[cm, j, i -> k] // trGuess[k],
                Subscript[cm, i, j -> k] // trGuess[k],
TestID->"trGuess is dyslexic."]]

Module[
  {i, j, k, n=3},
  VerificationTest[
    (TruncateToDegree[n][Subscript[cm, i, j -> k]]) // trDeg[k][n],
    (TruncateToDegree[n][Subscript[cm, j, i -> k]]) // trDeg[k][n],
TestID -> "trDeg is dyslexic up to degree "<>ToString[n]<>"."]]

(*
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
		{Xp[1,2], Xm[4,3]},
		{{2,-1},{4,-1},{1,0},{3,0}}]
	, straightStrand = RVT[{Strand[1]},{},{{1,0}}]
	},
	VerificationTest[
		Z[doubleTwist],
		Z[straightStrand],
TestID -> "R1' ZFramed with cancelling negative kinks."]]

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
