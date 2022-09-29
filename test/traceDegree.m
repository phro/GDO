Block[{ℏ = 1},

Module[
        {
                skeleton = {Strand[1,2], Loop[3,4]},
                xings = {Xp[1,4], Xm[3,2]},
                rotnums = {{1,0},{3,-1},{2,0},{4,1}},
                rvt
        },
        rvt = RVT[skeleton, xings, rotnums];
        VerificationTest[
                getSkeleton[rvt],
                skeleton,
TestID->"getSkeleton retrieves the skeleton of an RVT."];
        VerificationTest[
                getXings[rvt],
                xings,
TestID->"getXings retrieves the xings of an RVT."];
        VerificationTest[
                getRotNums[rvt],
                rotnums,
TestID->"getRotNums retrieves the rotnums of an RVT."]
]

Module[
        {
                c = {Strand[1,2,3,4], Strand[5,6,7,8,9,10]},
                L
        },
        L = RVT[c,
                {Xm[4,1], Xm[2,6], Xm[7,3], Xm[5,8], Xp[9,10]},
                {{2,-1},{8,1},{10,-1}}
        ];
        VerificationTest[
                getWritheOfComponent[L][c[[1]]],
                -1,
TestID->"getWritheOfComponent determines writhes correctly."];
        VerificationTest[
                getWritheOfComponent[L][c[[2]]],
                0,
TestID->"getWritheOfComponent determines cancelling writhes correctly."]
]

Module[
        {
                c = Strand[1,2,3],
                xpIn  = Xp[1,2],
                xpOut = Xp[3,4],
                xmIn  = Xm[2,1],
                xmOut = Xm[4,3]
                },
        VerificationTest[
                (getWritheOfXing@c)@xmIn,
                -1,
TestID->"getWritheOfXing gets writhe of negative xing in component."];
        VerificationTest[
                (getWritheOfXing@c)@xpIn,
                1,
TestID->"getWritheOfXing gets writhe of positive xing in component."];
        VerificationTest[
                (getWritheOfXing@c)@xmOut,
                0,
TestID->"getWritheOfXing gets writhe of negative xing out of component."];
        VerificationTest[
                (getWritheOfXing@c)@xpOut,
                0,
TestID->"getWritheOfXing gets writhe of positive xing out of component."];
]

VerificationTest[
        Writhe[SXForm[Strand[1],{}]],
        Writhe[SXForm[Strand[1],{}]],
        {Writhe::badArg},
TestID->"Writhe is only defined for RVT form."]

Module[
        {
                tangle = RVT[
                        {Strand[1], Loop[2], Loop[3]},
                        {},
                        {{1,0},{2,1},{3,-1}}
                ]
        },
        VerificationTest[
                tangle // Writhe,
                {0,0,0},
TestID->"Writhe computes the writhe of a no-crossing tangle correctly."]]

Module[
        {
                tangle = RVT[
                        {Strand[1,2], Strand[3], Strand[4]},
                        {Xp[1,3], Xm[4,2]},
                        {{1,0},{2,0},{3,0}}
                ]
        },
        VerificationTest[
                tangle // Writhe,
                {0,0,0},
TestID->"Writhe does not factor in inter-strand crossings in computation."]]

Module[
        {
                tangle = RVT[
                        {Strand[1,2,3,4], Strand[5,6,7,8]},
                        {Xm[4,1], Xm[2,6], Xm[7,3], Xm[5,8]},
                        {{2,-1},{8,1}}
                ]
        },
        VerificationTest[
                tangle // Writhe,
                {-1, -1},
TestID->"Writhe computes writhes correctly for multiple interacting strands."]]

Module[
        {
                tangle = RVT[
                        {Strand[1,3,4,5], Strand[2,6,7,8]},
                        {Xp[1,2], Xp[6,3], Xp[4,7], Xp[8,5]},
                        {{1,0},{2,0}}
                ]
        },
        VerificationTest[
                tangle // Unwrithe,
                tangle // Reindex,
TestID->"Unwrithe only reindexes tangles with no writhe."]]

Module[
        {
                tangle = RVT[
                        {Strand[1,2,3,4], Strand[5,6,7,8]},
                        {Xp[1,5], Xp[6,2], Xp[3,7], Xp[8,4]},
                        {{1,0},{5,0}}
                ]
        },
        VerificationTest[
                tangle // Unwrithe,
                tangle,
TestID->"Unwrithe does not change well-indexed knots."]]

Module[
        {
                tangle = toRVT@Link[11,NonAlternating,243],
                tangleUnwrithed
        },
        tangleUnwrithed = tangle // Unwrithe;
        VerificationTest[
                tangleUnwrithed // Unwrithe,
                tangleUnwrithed,
TestID->"Unwrithe is idempotent."]]

Module[
        {i, j},
        VerificationTest[
                GDO[{i}->{j}][
                        α[i]a[j]+ β[i]b[j] + τ[i]t[j], ξ[i] x[j] + η[i]y[j], 1
                ],
                Subscript[sσ,i ->j],
TestID->"GDO-notation returns \[DoubleStruckCapitalE]-notation."]]

VerificationTest[
        cm[{1,2},3],
        Subscript[cm,1,2->3],
TestID->"cm is multiplication when given a 2-element list."]

VerificationTest[
        cm[{1,2,3},4],
        Subscript[cm,1,2->2]//Subscript[cm,2,3->4],
TestID->"cm multiplies three elements in the correct order."]

VerificationTest[
        cm[{1},2],
        Subscript[cσ,1->2],
TestID->"cm is renaming when provided a singleton with differing output."]

VerificationTest[
        cm[{},1],
        Subscript[cη,1],
TestID->"cm is the unit when provided with empty output."]

Module[
        {
                i = "i",
                j = "j",
                n = 10,
                m = -7
        },
        VerificationTest[
                toGDO[Xp[i,j]],
                cR[i,j],
TestID->"toGDO transforms Xp into R-matrix."];
        VerificationTest[
                toGDO[Xm[i,j]],
                cRi[i,j],
TestID->"toGDO transforms Xm into inverse R-matrix."];
        VerificationTest[
                toGDO[{i,n}],
                CCn[i][n],
TestID->"toGDO transforms positive rotation into C-element."];
        VerificationTest[
                toGDO[{i,m}],
                CCn[i][m],
TestID->"toGDO transforms negative rotation into inverse C-element."];
        VerificationTest[
                toGDO[Strand[1,2,3]],
                cm[{1,2,3},1],
TestID->"toGDO transforms strand into multiplications."];
        VerificationTest[
                toGDO[Loop[1,2,3]],
                cm[{1,2,3},1]//tr[1],
TestID->"toGDO transforms loop into multiplications followed by trace."]
]

VerificationTest[
        getIndices@RVT[{Strand[1,2], Loop[3,4], Strand[5], Loop[6,-2]},{},{}],
        {-2,1,2,3,4,5,6},
TestID->"getIndices returns the indices of an RVT."]

VerificationTest[
        toList@RVT[
                {Strand[1,2,3], Loop[4,5], Strand[6]},
                {Xp[1,3], Xm[6,5], Xm[2,4]},
                {{1,0},{4,-3},{7,2}}
        ],
        {cR[1,3], cRi[6,5], cRi[2,4],
        CCn[1][0], CCn[4][-3], CCn[7][2],
        cm[{1,2,3},1], cm[{4,5},4]//tr[4], cm[{6},6]},
TestID->"toList transforms RVT into list of objects."]

Module[
        {
                rvt = RVT[{Strand[1]},{},{{1,1}}]
        },
        VerificationTest[
                toList@rvt,
                {CCn[1][1], cm[{1},1]},
TestID->"toList transforms a xingless tangle correctly."]]

Module[
        {
                rvt = RVT[{Strand[1]},{},{}]
        },
        VerificationTest[
                toList@rvt,
                {cm[{1},1]},
TestID->"toList transforms a rotation-free tangle correctly."]]

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
        {i = "i"},
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
TestID->"TruncateToDegree restricts Taylor-expandable series."]]

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
        {i = "i"},
        VerificationTest[
                GDO[{}->{i}][a[i],0,1]//GDOTruncateToDegree[3],
                GDO[{}->{i}][0,0,1+a[i] + a[i]^2/2 + a[i]^3/6],
TestID->"GDOTruncateToDegree truncates empty-domain exponential correctly."]]

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
TestID->"GDOTruncateToDegree truncates an exponent appropriately."]]

Module[
        {r, gdo},
        gdo = GDO[{1}->{1}][r α[1], (A[1]-1)y[1],1];
        VerificationTest[
                gdo // GDOTruncateToDegree[2],
                GDO[{1}->{1}][0,0,
                        1 +
                        (y[1] + r)α[1] +
                        (r^2/2 + (1/2 + r)y[1] + 1/2 y[1]^2)α[1]^2
                ]//CF,
TestID->"GDOTruncateToDegree truncates capital variables appropriately."]]

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
                -((-1 + E^(-ℏ b[i])) y[i])/b[i],
TestID->"getxCoef obtains the linear x-term of an R-matrix."]
        VerificationTest[
                getxyCoef[i][gdo][b[i]],
                0,
TestID->"getxyCoef obtains the xy-term of an R-matrix."]
        VerificationTest[
                getabCoef[i][gdo],
                0,
TestID->"getabCoef obtains the linear ab-term of an R-matrix."]
]

Module[
        {
                i = "i",
                j = "j",
                k = "k"
        },
        VerificationTest[
                getbCoef[i] @ GDO[{j, k} -> {i}][
                        0, 0, Exp[a[j] x[k] b[i]]
                ],
                a[j] x[k],
TestID->"getbCoef obtains coefficients from P-component."]]

Module[
        {
                i = "i",
                j = "j",
                k = "k"
        },
        VerificationTest[
                getbCoef[i] @ GDO[{j, k} -> {i}][
                        0, (η[j]ξ[k] + η[j] + ξ[k]) b[i], 1
                ],
                η[j]ξ[k] + η[j] + ξ[k],
TestID->"getbCoef obtains coefficients from Q-component."]]

Module[
        {
                i="i",
                ηi="ηi",
                βi="βi",
                αi="αi",
                ξi="ξi",
                ci="ci",
                bb,
                gdo
        },
        gdo = GDO[{}->{i}][
                βi b[i] + αi a[i] + σi a[i]b[i],
                ηi [b[i]]y[i] + ξi [b[i]]x[i] + λi[b[i]] x[i]y[i],
                Exp[ci]
        ];
        VerificationTest[
                getyCoef[i][gdo][bb],
                ηi[bb],
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
                getxCoef[i][gdo][bb],
                ξi[bb],
TestID->"getxCoef obtains the linear x-term of a generic GDO expression."];
        VerificationTest[
                getxyCoef[i][gdo][bb],
                λi[bb],
TestID->"getxyCoef obtains the xy-term of a generic GDO expression."];
        VerificationTest[
                getabCoef[i][gdo],
                σi,
TestID->"getabCoef obtains the ab-term of a generic GDO expression."];
        VerificationTest[
                getConstCoef[i][gdo],
                ci,
TestID->"getConstCoef obtains the constant term of a generic GDO expression."];
VerificationTest[
        GDO[{}->{i}][
                getbCoef[i][gdo]        b[i] +
                getaCoef[i][gdo]        a[i] +
                getabCoef[i][gdo]       a[i] b[i],
                getyCoef[i][gdo][b[i]]  y[i] +
                getxCoef[i][gdo][b[i]]  x[i] +
                getxyCoef[i][gdo][b[i]] x[i] y[i],
                Exp@getConstCoef[i][gdo]
                ],
        gdo,
TestID->"Extracting coefficients then reforming a GDO element is the identity."]
        ]

Module[
        {i, bb, k, r, putIntoL, putIntoQ},
        putIntoL[L_]:= GDO[{}->{i}][L, 0, 1];
        putIntoQ[Q_]:= GDO[{}->{i}][0, Q, 1];
        VerificationTest[
                getyCoef[i][putIntoQ[y[i](k x[i] + 1)(B[i] - 1)/b[i]]][bb],
                (Exp[-ℏ bb]-1)/bb,
TestID->"getyCoef understands capital B variables."];
        VerificationTest[
                getxCoef[i][putIntoQ[x[i](k y[i] + 1)(B[i] - 1)/b[i]]][bb],
                (Exp[-ℏ bb]-1)/bb,
TestID->"getxCoef understands capital B variables."];
        VerificationTest[
                getxyCoef[i][putIntoQ[x[i](k y[i] + 1)(B[i] - 1)/b[i]]][bb],
                k(Exp[-ℏ bb]-1)/bb,
TestID->"getxyCoef understands capital B variables."];
        VerificationTest[
                getbCoef[i][putIntoL[(a[i] + r)((B[i]^k - 1)/b[i])]]/.ℏ->1,
                k^2 r/2,
TestID->"getbCoef understands capital B variables."];
        VerificationTest[
                getaCoef[i][putIntoL[a[i](B[i]^k - 1)/b[i]]]/.ℏ->1,
                -k,
TestID->"getaCoef understands capital B variables."];
        VerificationTest[
                getaCoef[i][putIntoL[(k B[i]^k + r b[i]) a[i]]]/.ℏ->1,
                k,
TestID->"getaCoef understands simple capital B variables."];
        VerificationTest[
                getabCoef[i][putIntoL[(k B[i]^k + r b[i]) a[i]]]/.ℏ->1,
                -k^2 + r,
TestID->"getabCoef understands simple capital B variables."];
        VerificationTest[
                getabCoef[i][putIntoL[a[i](B[i]^k - 1)/b[i]]]/.ℏ->1,
                k^2/2,
TestID->"getabCoef understands capital B variables."];
        VerificationTest[
                getyCoef[1][putIntoQ[
                        ((-1 + B[1]) x[3] y[1])/(b[1] B[1])]][bb]/.ℏ->1,
                ((-1 + Exp[-bb]) x[3])/(bb Exp[-bb]),
TestID->"getyCoef correctly captures pernicuous (b, B)-series."];
        VerificationTest[
                getConstCoef[1][putIntoQ[(1-B[1]^-k) x[3]/(b[1])]]/.ℏ->1,
               -k x[3],
TestID->"getConstCoef correctly captures pernicuous (b, B)-series."]
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
                getxCoef[i][gdo][b[i]],
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
        {a},
        VerificationTest[
                safeEval[Exp[#]&][Exp[a]-1],
                Exp[Exp[a]-1],
TestID->"safeEval evaluates functions with well-defined values."];
        VerificationTest[
                safeEval[((1-Exp[#])/#)&][0],
                -1,
TestID->"safeEval evaluates functions with existant limits."]
        ]

Module[
        {
                gdo,
                gdos,
                i = "i",
                n = 3,
                j
        },
        gdos = {
                GDO[{{i},{}}->{{i},{}}][
                        α[i] a[i] + ξ[i]η[i]x[i]y[i]
                ],
                GDO[{{i},{}}->{{i},{}}][
                        α[i]a[i] + η[i]y[i] + β[i]b[i] + ξ[i]x[i] + ξ[i]η[i]x[i]y[i]
                ],
                GDO[{{i},{}}->{{i},{}}][
                        α[i] a[i] + η[i]β[i] b[i]y[i] + β[i] b[i] +
                        β[i]ξ[i]b[i] x[i] + β[i]ξ[i]η[i] b[i]x[i]y[i]
                ],
                GDO[{{i},{}}->{{i},{}}][
                        α[i] a[i] + β[i] b[i] + β[i]ξ[i]η[i] b[i]x[i]y[i]
                ]
        };
        Table[
                VerificationTest[
                        gdo // tr[i] // GDOTruncateToDegree[n],
                        gdo // trDeg[n][i],
                TestID->"tr agrees with trDeg on GDO\n" <> ToString[gdo]<>"."
                ],
                {gdo, gdos}
        ]
]

Module[
        {i = "i"},
        VerificationTest[
                GDO[{}->{i}][α[i] a[i] + β[i] b[i]]//tr[i],
                GDO[{{},{}}->{{},{i}}][α[i] a[i] + β[i](1-Exp[-α[i]])t[i]],
TestID->"tr behaves as defined on an L-only GDO."]]

Module[
        {
                i = "i",
                ta
        },
        ta = (1-Exp[-α[i]])t[i];
        VerificationTest[
                GDO[{}->{i}][α[i] a[i] + b[i]x[i]y[i]]//tr[i],
                GDO[{{},{}}->{{},{i}}][α[i] a[i] - Log[1-t[i] ta]],
TestID->"tr behaves as defined on an almost Q-only GDO."]]

Module[
        {
                i = "i",
                ta
        },
        ta = (1-1/A[i])t[i];
        VerificationTest[
                GDO[{}->{i}][α[i] a[i] + B[i]x[i]y[i]]//tr[i],
                GDO[{{},{}}->{{},{i}}][α[i] a[i] - Log[1-t[i]Exp[-ta]]],
TestID->"tr behaves as defined on a doubly-nested exponential almost Q-only GDO."]
]

Module[
        {
                i = "i",
                ta,
                tb
        },
        ta = (1-Exp[-α[i]])t[i];
        tb = (Exp[- ta]-1)/ta;
        VerificationTest[
                GDO[{}->{i}][α[i] a[i] + (B[i]-1)/b[i] x[i]y[i]]//tr[i],
                GDO[{{},{}}->{{},{i}}][
                        α[i] a[i] - Log[1 - t[i]tb]
                ]//.l2U//CF,
TestID->"tr behaves as defined on a doubly-nested almost exponential almost Q-only GDO."]
]

Module[
        {
                nonzeroWrithe = GDO[{}->{1}][5 a[1] b[1], 0,1]
        },
        VerificationTest[
                nonzeroWrithe // tr[1],
                nonzeroWrithe // tr[1],
                {tr::nonzeroSigma},
TestID->"tr does not compute when writhe is nonzero"]]

Module[
        {n = 5,
        gdo = GDO[{} -> {1, 3}][
                -ℏ(a[3] b[1] + a[1] b[3]),
                ((-1 + B[1]) x[3] y[1])/(b[1] B[1]) +
                ((-1 + B[3]) x[1] y[3])/(b[3] B[3]),
                1
        ]
        },
        VerificationTest[
                (gdo // tr[1])/.ℏ->1//Simplify,
                (GDO[{{},{}}->{{3},{1}}][
                        -b[3] a[1] - (1-Exp[b[3]]) a[3] t[1] +
                        x[3] y[3] (1-Exp[t[1](1-Exp[b[3]])])/b[3]
                        ]//.l2U/.ℏ->1)//Simplify,
TestID->"tr behaves as expected on a real-world GDO."]
]

Module[
        {
                gdo = GDO[{{1,2},{}}->{{},{3}}][
                        (α[1] + α[2])a[3] + (β[1] + β[2])(1-1/(A[1]A[2]))t[3],
                        (η[1]ξ[1]/A[2]+η[2]ξ[2]/A[1] + η[1]ξ[2]+η[2]ξ[1])t[3],
                        1
                ]//CF
        },
        VerificationTest[
                cm[{1,2},3]//tr[3],
                gdo,
TestID->"tr returns uppercase GDO's by default"]]

Module[
        {
                i = "i",
                j = "j"
        },
        VerificationTest[
                cR[i, j] // tr[i],
                GDO[{{},{}}->{{j},{i}}][0],
TestID->"tr closes properly on the overstrand of the Hopf Link."]
        VerificationTest[
                cR[i, j] // tr[j],
                GDO[{{},{}}->{{i},{j}}][a[j]b[i]],
TestID->"tr closes properly on the understrand of the Hopf Link."]
]

Module[
        {
                i="i",
                ηη="η",
                ββ="β",
                αα="α",
                ξξ="ξ",
                λλ="λ",
                ta
        },
        ta = (1-Exp[-αα]) t[i];
        VerificationTest[
                GDO[{{1,2},{}}->{{i},{}}][
                        αα a[i] +  ββ η[1]ξ[2] b[i]
                ] //tr[i],
                GDO[{{1,2},{}}->{{},{i}}][
                        αα a[i] + ββ η[1]ξ[2] ta
                ],
TestID->"tr behaves properly on GDO with nonempty domain."]]

Module[
        {
                i="i",
                η="η",
                β="β",
                α="α",
                ξ="ξ",
                λ="λ",
                ta,
                gdo,
                gdoTr
        },
        ta = (1-Exp[-α]) t[i];
        gdo = GDO[{{},{}}->{{i},{}}][
                α a[i] + η[b[i]] y[i] + β b[i] +
                ξ[b[i]] x[i] + λ[b[i]] x[i] y[i]
        ];
        gdoTr = GDO[{{},{}}->{{},{i}}][
                α a[i] + β ta + t[i](η[ta] ξ[ta])/(1-t[i] λ[ta])
                - Log[1 - t[i]λ[ta]]
        ];
        VerificationTest[
                gdo //tr[i],
                gdoTr,
TestID->"tr acts as expected on generic GDO element."
        ]
]

Module[
        {i="i", j="j", k="k"},
        VerificationTest[
                (Subscript[cm, j, i -> k] // tr[k])/.l2U//Simplify,
                (Subscript[cm, i, j -> k] // tr[k])/.l2U//Simplify,
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
        {
                whirl = RVT[
                        {Strand[i,3,5], Strand[j,4,6]},
                        {Xp[i,j]},
                        {{i,-1},{j,-1},{5,1},{6,1}}
                ],
                xp    = RVT[{Strand[i], Strand[j]},{Xp[i,j]},{{i,0},{j,0}}]
        },
        VerificationTest[
                whirl // ZFramed // Normal,
                xp    // ZFramed // Normal,
TestID->"ZFramed satisfies the positive whirl relation."]]

Module[
        {
                whirl = RVT[
                        {Strand[i,3,5], Strand[j,4,6]},
                        {Xm[i,j]},
                        {{i,-1},{j,-1},{5,1},{6,1}}
                ],
                xm    = RVT[{Strand[i], Strand[j]},{Xm[i,j]},{{i,0},{j,0}}]
        },
        VerificationTest[
                whirl // ZFramed // Normal,
                xm    // ZFramed // Normal,
TestID->"ZFramed satisfies the negative whirl relation."]]

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
                ZFramed[doubleTwist]//Normal,
                ZFramed[doubleSpiral]//Normal,
TestID -> "ZFramed satisfies cancelling kinks."]]

Module[
        { doubleTwist = RVT[
                {Strand[1,2,3,4]},
                {Xp[1,2], Xm[4,3]},
                {{2,-1},{4,-1},{1,0},{3,0}}]
        , doubleSpiral = RVT[{Strand[1]},{},{{1,0}}]
        },
        VerificationTest[
                ZFramed[doubleTwist]//Normal,
                ZFramed[doubleSpiral]//Normal,
TestID -> "ZFramed satisfies R1' with cancelling negative kinks."]]

Module[
        {
                r2pmb    = RVT[{Strand[1,2],Strand[3,4]}, {Xp[1,3],Xm[2,4]},{}],
                r2mpb    = RVT[{Strand[1,2],Strand[3,4]}, {Xm[1,3],Xp[2,4]},{}],
                parallel = RVT[{Strand[1], Strand[3]}, {},{}]
        },
        VerificationTest[
                ZFramed[r2pmb]//Normal,
                ZFramed[parallel]//Normal,
TestID->"ZFramed satisfies R2 (+-; braidlike)"];
        VerificationTest[
                ZFramed[r2mpb]//Normal,
                ZFramed[parallel]//Normal,
TestID->"ZFramed satisfies R2 (-+; braidlike)"]
]

Module[
        {
                r2pmcR    = RVT[
                        {Strand[1,2],Strand[3,4]}, {Xp[4,1],Xm[3,2]},{{2,1}}],
                r2mpcR    = RVT[
                        {Strand[1,2],Strand[3,4]}, {Xm[1,4],Xp[2,3]},{{2,1}}],
                parallelR = RVT[{Strand[1], Strand[3]},{},{{1,1}}]
        },
        VerificationTest[
                ZFramed[r2pmcR]//Normal,
                ZFramed[parallelR]//Normal,
TestID->"ZFramed satisfies R2 (+-; cyclic; right)"];
        VerificationTest[
                ZFramed[r2mpcR]//Normal,
                ZFramed[parallelR]//Normal,
TestID->"ZFramed satisfies R2 (-+; cyclic; right)"]
]

Module[
        {
                r2pmcL    = RVT[
                        {Strand[1,2],Strand[3,4]}, {Xp[1,4],Xm[2,3]},{{2,-1}}],
                r2mpcL    = RVT[
                        {Strand[1,2],Strand[3,4]}, {Xm[4,1],Xp[3,2]},{{2,-1}}],
                parallelL = RVT[{Strand[1], Strand[3]},{},{{1,-1}}]
        },
        VerificationTest[
                ZFramed[r2pmcL]//Normal,
                ZFramed[parallelL]//Normal,
TestID->"ZFramed satisfies R2 (+-; cyclic; left)"];
        VerificationTest[
                ZFramed[r2mpcL]//Normal,
                ZFramed[parallelL]//Normal,
TestID->"ZFramed satisfies R2 (-+; cyclic; left)"]
]

Module[
        {
                lhs = RVT[
                        {Strand[11,12], Strand[21,22], Strand[31,32]},
                        {Xp[11,21], Xp[12,31], Xp[22,32]},
                        {}
                ],
                rhs = RVT[
                        {Strand[11,12], Strand[21,22], Strand[31,32]},
                        {Xp[21,31], Xp[11,32], Xp[12,22]},
                        {}
                ]
        },
        VerificationTest[
                ZFramed[lhs]//Normal,
                ZFramed[rhs]//Normal,
TestID->"ZFramed satisfies R3+"]]

Module[
        {
                lhs = RVT[
                        {Strand[11,12], Strand[21,22], Strand[31,32]},
                        {Xm[21,11], Xm[31,12], Xm[32,22]},
                        {}
                ],
                rhs = RVT[
                        {Strand[11,12], Strand[21,22], Strand[31,32]},
                        {Xm[31,21], Xm[32,11], Xm[22,12]},
                        {}
                ]
        },
        VerificationTest[
                ZFramed[lhs]//Normal,
                ZFramed[rhs]//Normal,
TestID->"ZFramed satisfies R3-"]]

Module[
        {
                gdo = Link[7,Alternating,7]//toRVT
        },
        VerificationTest[
                gdo // ptr // Length,
                gdo // getCodomain // Length,
TestID->"ptr returns a list of k elements for a k-component tangle."]]

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
]
