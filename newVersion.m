setValue[value_,obj_,coords__]:=Module[
        {b=obj[[1]]},
        b[coords] = value; Head[obj]@b
        ]

(* PG[L, Q, P] = Perturbed Gaußian Pe^(L + Q) *)

toPG[L_, Q_, P_] := PG@<|"L"->L, "Q"->Q, "P"->P|>
fromE[e_\[DoubleStruckCapitalE]] := toPG@@e/.
        Subscript[(v:y|b|t|a|x|B|T|η|β|τ|α|ξ|A), i_] -> v[i]

δ[i_,j_] := If[SameQ[i,j],1,0]

getL[pg_PG] := Lookup[pg[[1]],"L",0]
getQ[pg_PG] := Lookup[pg[[1]],"Q",0]
getP[pg_PG] := Lookup[pg[[1]],"P",1]

setL[L_][pg_PG] := setValue[L, pg, "L"];
setQ[Q_][pg_PG] := setValue[Q, pg, "Q"];
setP[P_][pg_PG] := setValue[P, pg, "P"];

CCF[e_] := ExpandDenominator@ExpandNumerator@Together[
        Expand[e] //. E^x_ E^y_ :> E^(x + y) /. E^x_ :> E^CCF[x]
];
CF[es_List] := CF /@ es;
CF[sd_SeriesData] := MapAt[CF, sd, 3];
CF[e_] := Module[
        {vs = Union[
                Cases[e, Subscript[(y|b|t|a|x|η|β|τ|α|ξ), _], ∞],
                {y, b, t, a, x, η, β, τ, α, ξ}
        ]},
        Total[CoefficientRules[Expand[e], vs] /.
                (ps_ -> c_) :> CCF[c] (Times @@ (vs^ps))
        ]
];
CF[e_PG] := CF/@#&/@e;

PG /: Congruent[pg1_PG, pg2_PG] := And[
        CF[getL@pg1 == getL@pg2],
        CF[getQ@pg1 == getQ@pg2],
        CF[Normal[getP@pg1-getP@pg2] == 0]
]

PG /: pg1_PG * pg2_PG := toPG[
        getL@pg1 + getL@pg2,
        getQ@pg1 + getQ@pg2,
        getP@pg1 * getP@pg2
]

setEpsilonDegree[k_Integer][pg_PG]:= setP[Series[Normal@getP@pg,{ϵ, 0, k}]][pg]

ddsl2vars = {y, b, t, a, x};
ddsl2varsDual = {η, β, τ, α, ξ};

Evaluate[Dual/@ddsl2vars] = ddsl2varsDual;
Evaluate[Dual/@ddsl2varsDual] = ddsl2vars;
Dual@z = ζ;
Dual@ζ = z;

Dual[u_[i_]]:=Dual[u][i]

U2l = {
        B[i_]^p_. :> E^(-p ℏ γ b[i]), B^p_. :> E^(-p ℏ γ b),
        T[i_]^p_. :> E^(-p ℏ t[i]), T^p_. :> E^(-p ℏ t),
        A[i_]^p_. :> E^(p γ α[i]), A^p_. :> E^(-p γ α)
};
l2U = {
        E^(c_. b[i_] + d_.) :> B[i]^(-c/(ℏ γ))E^d,
        E^(c_. b + d_.) :> B^(-c/(ℏ γ))E^d,
        E^(c_. t[i_] + d_.) :> T[i]^(-c/ℏ)E^d,
        E^(c_. t + d_.) :> T^(-c/ℏ)E^d,
        E^(c_. α[i_] + d_.) :> A[i]^(c/γ)E^d,
        E^(c_. α + d_.) :> A^(c/γ)E^d,
        E^expr_ :> E^Expand@expr
};

(* Differentiation *)

DD[f_, b] := D[f, b] - ℏ γ B D[f, B];
DD[f_, b[i_]] := D[f, b[i]] - ℏ γ B[i] D[f, B[i]];

DD[f_, t] := D[f, t] - ℏ T D[f, T];
DD[f_, t[i_]] := D[f, t[i]] - ℏ T[i] D[f, T[i]];

DD[f_, α] := D[f, α] + γ A D[f, A];
DD[f_, α[i_]] := D[f, α[i]] + γ A[i] D[f, A[i]];

DD[f_, v_] := D[f, v];
DD[f_, {v_,0}] := f;
DD[f_, {}] := f;
DD[f_, {v_,n_Integer}] := DD[DD[f,v],{v,n-1}];
DD[f_, {l_List, ls___}] := DD[DD[f, l], {ls}];

(* Finite zips *)
collect[sd_SeriesData, ζ_] := MapAt[collect[#, ζ] &, sd, 3];
collect[expr_, ζ_] := Collect[expr, ζ];

Zip[{}][P_] := P;
Zip[ζs_List][Ps_List] := Zip[ζs]/@Ps;
Zip[{ζ_,ζs___}][P_] := (collect[P // Zip[{ζs}],ζ] /.
        f_. ζ^d_. :> DD[f,{Dual[ζ], d}]) /.
        Dual[ζ] -> 0 /.
        ((Dual[ζ] /. {b->B, t->T, α -> A}) -> 1)

(* Q-zips *)

QZip[ζs_List][pg_PG] := Module[{Q, P, ζ, z, zs, c, ys, ηs, qt, zrule, ζrule},
        zs = Dual/@ζs;
        Q  = pg//getQ;
        P  = pg//getP;
        c  = CF[Q/.Alternatives@@Union[ζs, zs]->0];
        ys = CF@Table[D[Q,ζ]/.Alternatives@@zs->0,{ζ,ζs}];
        ηs = CF@Table[D[Q,z]/.Alternatives@@ζs->0,{z,zs}];
        qt = CF@Inverse@Table[
                δ[z, Dual[ζ]] - D[Q,z,ζ],
                {ζ,ζs},{z,zs}
        ];
        zrule = Thread[zs -> CF[qt . (zs + ys)]];
        ζrule = Thread[ζs -> ζs + ηs . qt];
        CF@setQ[c + ηs.qt.ys]@setP[Det[qt] Zip[ζs][P /. Union[zrule, ζrule]]]@pg
]

LZip[ζs_List][pg_PG] := Module[
        {
                L, Q, P, ζ, z, zs, Zs, c, ys, ηs, lt,
                zrule, Zrule, ζrule, Q1, EEQ, EQ, U
        },
        zs = Dual/@ζs;
        {L, Q, P} = Through[{getL, getQ, getP}@pg];
        Zs = zs /. {b -> B, t -> T, α -> A};
        c  = CF[L/.Alternatives@@Union[ζs, zs]->0/.Alternatives@@Zs -> 1];
        ys = CF@Table[D[L,ζ]/.Alternatives@@zs->0,{ζ,ζs}];
        ηs = CF@Table[D[L,z]/.Alternatives@@ζs->0,{z,zs}];
        lt = CF@Inverse@Table[
                δ[z, Dual[ζ]] - D[L,z,ζ],
                {ζ,ζs},{z,zs}
        ];
        zrule = Thread[zs -> CF[lt . (zs + ys)]];
        Zrule = Join[zrule, zrule /.
                r_Rule :> ( (U = r[[1]] /. {b -> B, t -> T, α -> A}) ->
                (U /. U2l /. r //. l2U))
        ];
        \[Zeta]rule = Thread[\[Zeta]s -> \[Zeta]s + \[Eta]s . lt];
        Q1 = Q /. Union[Zrule, ζrule];
        EEQ[ps___] :=
                EEQ[ps] = (
                        CF[E^-Q1 DD[E^Q1,Thread[{zs,{ps}}]] /.
                                {Alternatives@@zs -> 0, Alternatives @@Zs -> 1}]
                );
        CF@toPG[
                c + ηs.lt.ys,
                Q1 /. {Alternatives@@zs -> 0, Alternatives@@Zs -> 1},
                Det[lt] (Zip[ζs][(EQ@@zs) (P /. Union[Zrule,ζrule])] /.
                        Derivative[ps___][EQ][___] :> EEQ[ps] /. _EQ ->1
                )
        ]

]

Pair[{}][L_PG,R_PG] := L R;
Pair[is_List][L_PG,R_PG] := Module[{n},
        Times[
                L /. ((v: b|B|t|T|a|x|y)[#] -> v[n@#]&/@is),
                R /. ((v: β|τ|α|A|ξ|η)[#] -> v[n@#]&/@is)
        ] // LZip[Join@@Table[Through[{β, τ, a}[n@i]],{i, is}]] //
        QZip[Join@@Table[Through[{ξ, y}[n@i]],{i, is}]]
]

(* GDO = Gaußian Differential Operator *)
toGDO[do_List,dc_List,co_List,cc_List,L_,Q_,P_] := GDO@<|
        "do" -> do,
        "dc" -> dc,
        "co" -> co,
        "cc" -> cc,
        "PG" -> toPG[L, Q, P]
|>

toGDO[do_List,dc_List,co_List,cc_List,pg_PG] := GDO@<|
        "do" -> do,
        "dc" -> dc,
        "co" -> co,
        "cc" -> cc,
        "PG" -> pg
|>

getDO[gdo_GDO] := Lookup[gdo[[1]], "do", {}]
getDC[gdo_GDO] := Lookup[gdo[[1]], "dc", {}]
getCO[gdo_GDO] := Lookup[gdo[[1]], "co", {}]
getCC[gdo_GDO] := Lookup[gdo[[1]], "cc", {}]

getPG[gdo_GDO] := Lookup[gdo[[1]], "PG", PG@<||> ]

getL[gdo_GDO] := gdo//getPG//getL
getQ[gdo_GDO] := gdo//getPG//getQ
getP[gdo_GDO] := gdo//getPG//getP

setPG[pg_PG][gdo_GDO] := setValue[pg, gdo, "PG"]

setL[L_][gdo_GDO] := setValue[L, gdo, "PG",1,"L"]
setQ[Q_][gdo_GDO] := setValue[Q, gdo, "PG",1,"Q"]
setP[P_][gdo_GDO] := setValue[P, gdo, "PG",1,"P"]

setDO[do_][gdo_GDO] := setValue[do, gdo, "do"]
setDC[dc_][gdo_GDO] := setValue[dc, gdo, "dc"]
setCO[co_][gdo_GDO] := setValue[co, gdo, "co"]
setCC[cc_][gdo_GDO] := setValue[cc, gdo, "cc"]

Pair[is_List][gdo1_GDO, gdo2_GDO] := GDO@<|
        "do" -> Union[gdo1//getDO, Complement[gdo2//getDO, is]],
        "dc" -> Union[gdo1//getDC, gdo2//getDC],
        "co" -> Union[gdo2//getCO, Complement[gdo1//getCO, is]],
        "cc" -> Union[gdo1//getCC, gdo2//getCC],
        "PG" -> Pair[is][gdo1//getPG, gdo2//getPG]
|>

gdo1_GDO // gdo2_GDO := Pair[Intersection[gdo1//getCO,gdo2//getDO]][gdo1,gdo2];

GDO /: Congruent[gdo1_GDO, gdo2_GDO] := And[
        Sort@*getDO/@Equal[gdo1, gdo2],
        Sort@*getDC/@Equal[gdo1, gdo2],
        Sort@*getCO/@Equal[gdo1, gdo2],
        Sort@*getCC/@Equal[gdo1, gdo2],
        Congruent[gdo1//getPG, gdo2//getPG]
]
