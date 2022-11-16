γ = 1; ℏ = 1; $k = 0;
setValue[value_,obj_,coord_]:=Module[
        {b=Association@@obj},
        b[coord] = value; Head[obj]@@Normal@b
]

(* PG[L, Q, P] = Perturbed Gaußian Pe^(L + Q) *)

toPG[L_, Q_, P_] := PG["L"->L, "Q"->Q, "P"->P]
fromE[e_\[DoubleStruckCapitalE]] := toPG@@e/.
        Subscript[(v:y|b|t|a|x|B|T|η|β|τ|α|ξ|A), i_] -> v[i]

δ[i_,j_] := If[SameQ[i,j],1,0]

getL[pg_PG] := Lookup[Association@@pg,"L",0]
getQ[pg_PG] := Lookup[Association@@pg,"Q",0]
getP[pg_PG] := Lookup[Association@@pg,"P",1]

setL[L_][pg_PG] := setValue[L, pg, "L"];
setQ[Q_][pg_PG] := setValue[Q, pg, "Q"];
setP[P_][pg_PG] := setValue[P, pg, "P"];

applyToL[f_][pg_PG] := pg//setL[pg//getL//f]
applyToQ[f_][pg_PG] := pg//setQ[pg//getQ//f]
applyToP[f_][pg_PG] := pg//setP[pg//getP//f]

CCF[e_] := ExpandDenominator@ExpandNumerator@Together[
        Expand[e] //. E^x_ E^y_ :> E^(x + y) /. E^x_ :> E^CCF[x]
];
CF[sd_SeriesData] := MapAt[CF, sd, 3];
CF[e_] := Module[
        {vs = Union[
                Cases[e, (y|b|t|a|x|η|β|τ|α|ξ)[_], ∞],
                {y, b, t, a, x, η, β, τ, α, ξ}
        ]},
        Total[CoefficientRules[Expand[e], vs] /.
                (ps_ -> c_) :> CCF[c] (Times @@ (vs^ps))
        ]
];
CF[e_PG] := e//applyToL[CF]//applyToQ[CF]//applyToP[CF]

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
        ys = CF/@Table[D[Q,ζ]/.Alternatives@@zs->0,{ζ,ζs}];
        ηs = CF/@Table[D[Q,z]/.Alternatives@@ζs->0,{z,zs}];
        qt = CF/@#&/@(Inverse@Table[
                δ[z, Dual[ζ]] - D[Q,z,ζ],
                {ζ,ζs},{z,zs}
        ]);
        zrule = Thread[zs -> CF/@(qt . (zs + ys))];
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
        ys = CF/@Table[D[L,ζ]/.Alternatives@@zs->0,{ζ,ζs}];
        ηs = CF/@Table[D[L,z]/.Alternatives@@ζs->0,{z,zs}];
        lt = CF/@#&/@Inverse@Table[
                δ[z, Dual[ζ]] - D[L,z,ζ],
                {ζ,ζs},{z,zs}
        ];
        zrule = Thread[zs -> CF/@(lt . (zs + ys))];
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
toGDO[do_List,dc_List,co_List,cc_List,L_,Q_,P_] := GDO[
        "do" -> do,
        "dc" -> dc,
        "co" -> co,
        "cc" -> cc,
        "PG" -> toPG[L, Q, P]
]

toGDO[do_List,dc_List,co_List,cc_List,pg_PG] := GDO[
        "do" -> do,
        "dc" -> dc,
        "co" -> co,
        "cc" -> cc,
        "PG" -> pg
]

getDO[gdo_GDO] := Lookup[Association@@gdo, "do", {}]
getDC[gdo_GDO] := Lookup[Association@@gdo, "dc", {}]
getCO[gdo_GDO] := Lookup[Association@@gdo, "co", {}]
getCC[gdo_GDO] := Lookup[Association@@gdo, "cc", {}]

getPG[gdo_GDO] := Lookup[Association@@gdo, "PG", PG[]]

getL[gdo_GDO] := gdo//getPG//getL
getQ[gdo_GDO] := gdo//getPG//getQ
getP[gdo_GDO] := gdo//getPG//getP

setPG[pg_PG][gdo_GDO] := setValue[pg, gdo, "PG"]

setL[L_][gdo_GDO] := setValue[setL[L][gdo//getPG], gdo, "PG"]
setQ[Q_][gdo_GDO] := setValue[setQ[Q][gdo//getPG], gdo, "PG"]
setP[P_][gdo_GDO] := setValue[setP[P][gdo//getPG], gdo, "PG"]

setDO[do_][gdo_GDO] := setValue[do, gdo, "do"]
setDC[dc_][gdo_GDO] := setValue[dc, gdo, "dc"]
setCO[co_][gdo_GDO] := setValue[co, gdo, "co"]
setCC[cc_][gdo_GDO] := setValue[cc, gdo, "cc"]

applyToDO[f_][gdo_GDO] := gdo//setDO[gdo//getDO//f]
applyToDC[f_][gdo_GDO] := gdo//setDC[gdo//getDC//f]
applyToCO[f_][gdo_GDO] := gdo//setCO[gdo//getCO//f]
applyToCC[f_][gdo_GDO] := gdo//setCC[gdo//getCC//f]

applyToPG[f_][gdo_GDO] := gdo//setPG[gdo//getPG//f]

applyToL[f_][gdo_GDO] := gdo//setL[gdo//getL//f]
applyToQ[f_][gdo_GDO] := gdo//setQ[gdo//getQ//f]
applyToP[f_][gdo_GDO] := gdo//setP[gdo//getP//f]

CF[e_GDO] := e//
        applyToDO[Union]//
	applyToDC[Union]//
	applyToCO[Union]//
	applyToCC[Union]//
        applyToPG[CF]

Pair[is_List][gdo1_GDO, gdo2_GDO] := GDO[
        "do" -> Union[gdo1//getDO, Complement[gdo2//getDO, is]],
        "dc" -> Union[gdo1//getDC, gdo2//getDC],
        "co" -> Union[gdo2//getCO, Complement[gdo1//getCO, is]],
        "cc" -> Union[gdo1//getCC, gdo2//getCC],
        "PG" -> Pair[is][gdo1//getPG, gdo2//getPG]
]

gdo1_GDO // gdo2_GDO := Pair[Intersection[gdo1//getCO,gdo2//getDO]][gdo1,gdo2];

GDO /: Congruent[gdo1_GDO, gdo2_GDO] := And[
        Sort@*getDO/@Equal[gdo1, gdo2],
        Sort@*getDC/@Equal[gdo1, gdo2],
        Sort@*getCO/@Equal[gdo1, gdo2],
        Sort@*getCC/@Equal[gdo1, gdo2],
        Congruent[gdo1//getPG, gdo2//getPG]
]

GDO /: gdo1_GDO gdo2_GDO := GDO[
        "do" -> Union[gdo1//getDO, gdo2//getDO],
        "dc" -> Union[gdo1//getDC, gdo2//getDC],
        "co" -> Union[gdo1//getCO, gdo2//getCO],
        "cc" -> Union[gdo1//getCC, gdo2//getCC],
        "PG" -> (gdo1//getPG)*(gdo2//getPG)
]

setEpsilonDegree[k_Integer][gdo_GDO]:=setP[Series[Normal@getP@gdo,{ϵ,0,k}]][gdo]

fromE[Subscript[\[DoubleStruckCapitalE],{do_List, dc_List}->{co_List, cc_List}][
        L_, Q_, P_
]] := toGDO[do, dc, co, cc, fromE[\[DoubleStruckCapitalE][L, Q, P]]]

fromE[Subscript[\[DoubleStruckCapitalE], dom_List->cod_List][
        L_, Q_, P_
]] := GDO["do" -> dom, "co" -> cod,
        "PG" -> fromE[\[DoubleStruckCapitalE][L, Q, P]]
]

fromLog[l_] := CF@Module[
        {L, l0 = Limit[l, ϵ->0]},
        L = l0 /. (η|y|ξ|x)[_]->0;
        PG[
                "L" -> L,
                "Q" -> l0 - L
        ]/.l2U
]

cΛ =    (η[i] + E^(-γ α[i] - ϵ β[i]) η[j]/(1+γ ϵ η[j]ξ[i]))y[k] +
        (β[i] + β[j] + Log[1 + γ ϵ η[j]ξ[i]]/ϵ) b[k] +
        (α[i] + α[j] + Log[1 + γ ϵ η[j]ξ[i]]/γ) a[k] +
        (ξ[j] + E^(-γ α[j] - ϵ β[j]) ξ[i]/(1+γ ϵ η[j]ξ[i]))x[k];

cm[i_, j_, k_] = GDO["do" -> {i,j}, "co" -> {k}, "PG" -> fromLog[cΛ]];

cη[i_] = GDO["co" -> {i}];
cσ[i_,j_] = GDO["do"->{i},"co"->{j},
        "PG"->fromLog[β[i] b[j] + α[i] a[j] + η[i] y[j] + ξ[i] x[j]]
];
cϵ[i_] = GDO["do" -> {i}];
cΔ[i_, j_, k_] = GDO["do"->{i}, "co"->{j, k},
        "PG" -> fromLog[
                β[i](b[j] + b[k]) +
                α[i](a[j] + a[k]) +
                η[i](y[j] + y[k]) +
                ξ[i](x[j] + x[k])
        ]
];

sY[i_, j_, k_, l_, m_] = GDO["do"->{i}, "co"->{j, k, l, m},
        "PG" -> fromLog[β[i]b[k] + α[i]a[l] + η[i]y[j] + ξ[i]x[m]]
];

sS[i_] = GDO["do"->{i},"co"->{i},
        "PG"->fromLog[-(β[i] b[i] + α[i] a[i] + η[i] y[i] + ξ[i] x[i])]
];

cS[i_] = sS[i] // sY[i, 1, 2, 3, 4] // cm[4,3, i] // cm[i, 2, i] // cm[i, 1, i];

getConstLCoef::usage = "getConstLCoef[i][gdo] returns the terms in the L-portion of a GDO expression which are not a function of y[i], b[i], a[i], nor x[i]."
getConstLCoef[i_][gdo_] :=
        (SeriesCoefficient[#, {b[i],0,0}]&) @*
        (Coefficient[#, y[i], 0]&) @*
        (Coefficient[#, a[i], 0]&) @*
        (Coefficient[#, x[i], 0]&) @*
        ReplaceAll[U2l] @*
        getL@
        gdo

getConstQCoef::usage = "getConstQCoef[i][gdo] returns the terms in the Q-portion of a GDO expression which are not a function of y[i], b[i], a[i], nor x[i]."
getConstQCoef[i_][gdo_][bb_] :=
        ReplaceAll[{b[i]->bb}] @*
        (Coefficient[#, y[i], 0]&) @*
        (Coefficient[#, a[i], 0]&) @*
        (Coefficient[#, x[i], 0]&) @*
        ReplaceAll[U2l] @*
        getQ@
        gdo

getyCoef::usage = "getyCoef[i][gdo][b[i]] returns the linear coefficient of y[i] as a function of b[i]."
getyCoef[i_][gdo_][bb_] :=
        ReplaceAll[{b[i]->bb}] @*
        ReplaceAll[U2l] @*
        (Coefficient[#, x[i],0]&) @*
        (Coefficient[#, y[i],1]&) @*
        getQ@
        gdo

getbCoef::usage = "getbCoef[i][gdo] returns the linear coefficient of b[i]."
getbCoef[i_][gdo_] :=
        (SeriesCoefficient[#, {b[i],0,1}]&) @*
        (Coefficient[#, a[i],0]&) @*
        (Coefficient[#, x[i],0]&) @*
        (Coefficient[#, y[i],0]&) @*
        ReplaceAll[U2l] @*
        getL@
        gdo

getPCoef::usage = "getPCoef[i][gdo] returns the perturbation P of a GDO as a function of b[i]."
getPCoef[i_][gdo_][bb_] :=
        ReplaceAll[{b[i]->bb}] @*
        (Coefficient[#, a[i],0]&) @*
        (Coefficient[#, x[i],0]&) @*
        (Coefficient[#, y[i],0]&) @*
        ReplaceAll[U2l] @*
        getP@
        gdo

getaCoef::usage = "getaCoef[i][gdo] returns the linear coefficient of a[i]."
getaCoef[i_][gdo_] :=
        (SeriesCoefficient[#, {b[i],0,0}]&) @*
        (Coefficient[#, a[i],1]&) @*
        ReplaceAll[U2l] @*
        getL@
        gdo

getxCoef::usage = "getxCoef[i][gdo][b[i]] returns the linear coefficient of x[i] as a function of b[i]."
getxCoef[i_][gdo_][bb_] :=
        ReplaceAll[{b[i]->bb}] @*
        ReplaceAll[U2l] @*
        (Coefficient[#, y[i],0]&) @*
        (Coefficient[#, x[i],1]&) @*
        getQ@
        gdo

getabCoef::usage = "getabCoef[i][gdo] returns the linear coefficient of a[i]b[i]."
getabCoef[i_][gdo_] :=
        (SeriesCoefficient[#,{b[i],0,1}]&) @*
        (Coefficient[#,a[i],1]&) @*
        ReplaceAll[U2l] @*
        getL@
        gdo

getxyCoef::usage = "getxyCoef[i][gdo][b[i]] returns the linear coefficient of x[i]y[i] as a function of b[i]."
getxyCoef[i_][gdo_][bb_] :=
        ReplaceAll[{b[i]->bb}] @*
        ReplaceAll[U2l] @*
        (Coefficient[#,x[i],1]&) @*
        (Coefficient[#,y[i],1]&) @*
        getQ@
        gdo

safeEval[f_][x_] := Module[{fx, x0},
        If[(fx=Quiet[f[x]]) === Indeterminate,
                Series[f[x0],{x0,x,0}]//Normal,
                fx
        ]
]

closeComponent[i_][gdo_GDO]:=gdo//
        setCO[Complement[gdo//getCO,{i}]]//
        setCC[Union[gdo//getCC,{i}]]

tr::usage = "tr[i] computes the trace of a GDO element on component i. Current implementation assumes the Subscript[a, i] Subscript[b, i] term vanishes and $k=0."
tr::nonzeroSigma = "tr[`1`]: Component `1` has writhe: `2`, expected: 0."
tr[i_][gdo_GDO] := Module[
        {
                cL = getConstLCoef[i][gdo],
                cQ = getConstQCoef[i][gdo],
                βP = getPCoef[i][gdo],
                ηη = getyCoef[i][gdo],
                ββ = getbCoef[i][gdo],
                αα = getaCoef[i][gdo],
                ξξ = getxCoef[i][gdo],
                λ = getxyCoef[i][gdo],
                ta
        },
        ta = (1-Exp[-αα]) t[i];
        expL = cL + αα a[i] + ββ ta;
        expQ = safeEval[cQ[#] + t[i]ηη[#]ξξ[#]/(1-t[i] λ[#])&][ta];
        expP = safeEval[βP[#]/(1-t[i] λ[#])&][ta];
        CF[(gdo//closeComponent[i]//setL[expL]//setQ[expQ]//setP[expP])//.l2U]
] /; Module[
        {σ = getabCoef[i][gdo]},
        If[σ == 0,
                True,
                Message[tr::nonzeroSigma, i, ToString[σ]]; False
        ]
]

(* Formatting *)

Format[gdo_GDO] := Subsuperscript[\[DoubleStruckCapitalE],
        Row[{gdo//getCO, ",", gdo//getCC}],
        Row[{gdo//getDO, ",", gdo//getDC}]
][gdo//getL, gdo//getQ, gdo//getP];

SubscriptFormat[v_] := (Format[v[i_]] := Subscript[v, i]);

SubscriptFormat/@{y,b,t,a,x,η,β,α,ξ,A,B,T};
