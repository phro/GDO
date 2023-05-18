(*
This is a Mathematica™ implementation by Bar-Natan and van der Veen in
\cite{BV}, modified by the author. We begin by setting some variables, as well
as a method for modifying associations.
*)
γ = 1; ℏ = 1; $k = 0;
setValue[value_,obj_,coord_]:=Module[
        {b=Association@@obj},
        b[coord] = value; Head[obj]@@Normal@b
]
(*
We introduce notation \mma{PG[L, Q, P]} to be interpreted as the Perturbed
Gaußian $P\Exp{L + Q}$. The function \mma{fromE} serves as a compatibility
layer between a former version of the code.
*)
toPG[L_, Q_, P_] := PG["L"->L, "Q"->Q, "P"->P]
fromE[e_\[DoubleStruckCapitalE]] := toPG@@e/.
        Subscript[(v:y|b|t|a|x|B|T|η|β|τ|α|ξ|A), i_] -> v[i]
(*
We define the Kronecker-$δ$ function next.
*)
δ[i_,j_] := If[SameQ[i,j],1,0]
(*
Next we introduce helper functions for the reading and manipulating of
\mma{PG}-objects:
*)
getL[pg_PG] := Lookup[Association@@pg,"L",0]
getQ[pg_PG] := Lookup[Association@@pg,"Q",0]
getP[pg_PG] := Lookup[Association@@pg,"P",1]

setL[L_][pg_PG] := setValue[L, pg, "L"];
setQ[Q_][pg_PG] := setValue[Q, pg, "Q"];
setP[P_][pg_PG] := setValue[P, pg, "P"];

applyToL[f_][pg_PG] := pg//setL[pg//getL//f]
applyToQ[f_][pg_PG] := pg//setQ[pg//getQ//f]
applyToP[f_][pg_PG] := pg//setP[pg//getP//f]
(*
Next is a function \mma{CF}, which bring objects into canonical form allows us
to compare for equality effectively. This is defined by Bar-Natan and van der
Veen.
*)
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
(*
We must also define the notion of equality for \mma{PG}-objects, as well as what
it means to multiply them.
*)
Congruent[x_, y_, z__] := And[Congruent[x, y], Congruent[y, z]]
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

setEpsilonDegree[k_Integer][pg_PG] := setP[Series[Normal@getP@pg,{ϵ, 0, k}]][pg]
(*
The variables $y$, $b$, $t$, $a$, and $x$ are paired with their dual variables
$η$, $β$, $τ$, $α$, and $ξ$. This applies as well when they have subscripts.
*)
ddsl2vars = {y, b, t, a, x, z};
ddsl2varsDual = {η, β, τ, α, ξ, ζ};

Evaluate[Dual/@ddsl2vars] = ddsl2varsDual;
Evaluate[Dual/@ddsl2varsDual] = ddsl2vars;
Dual@z = ζ;
Dual@ζ = z;
Dual[u_[i_]]:=Dual[u][i]
(*
Since various exponentials of the lowercase variables frequently appear, we
introduce capital variable names to handle various exponentiated forms.
*)
U2l = {
        B[i_]^p_. :> E^(-p ℏ γ b[i]), B^p_. :> E^(-p ℏ γ b),
        W[i_]^p_. :> E^(w[i])       , W^p_. :> E^(p w),
        T[i_]^p_. :> E^(-p ℏ t[i])  , T^p_. :> E^(-p ℏ t),
        A[i_]^p_. :> E^(p γ α[i])   , A^p_. :> E^(-p γ α)
};
l2U = {
        E^(c_. b[i_] + d_.) :> B[i]^(-c/(ℏ γ))E^d,
        E^(c_. b + d_.)     :> B^(-c/(ℏ γ))E^d,
        E^(c_. t[i_] + d_.) :> T[i]^(-c/ℏ)E^d,
        E^(c_. t + d_.)     :> T^(-c/ℏ)E^d,
        E^(c_. α[i_] + d_.) :> A[i]^(c/γ)E^d,
        E^(c_. α + d_.)     :> A^(c/γ)E^d,
        E^(c_. w[i_] + d_.) :> W[i]^(c)E^d,
        E^(c_. w + d_.)     :> W^(c)E^d,
        E^expr_             :> E^Expand@expr
};
(*
Below the notion of differentiation is defined for expressions which involve
both upper- and lower-case variables.
*)
DD[f_, b]     := D[f, b   ] - ℏ γ B    D[f, B   ];
DD[f_, b[i_]] := D[f, b[i]] - ℏ γ B[i] D[f, B[i]];

DD[f_, t    ] := D[f, t   ] - ℏ T    D[f, T   ];
DD[f_, t[i_]] := D[f, t[i]] - ℏ T[i] D[f, T[i]];

DD[f_, α    ] := D[f, α   ] + γ A    D[f, A   ];
DD[f_, α[i_]] := D[f, α[i]] + γ A[i] D[f, A[i]];

DD[f_, v_] := D[f, v];
DD[f_, {v_,0}] := f;
DD[f_, {}] := f;
DD[f_, {v_,n_Integer}] := DD[DD[f,v],{v,n-1}];
DD[f_, {l_List, ls___}] := DD[DD[f, l], {ls}];
(*
What follows now is the implementation of contraction as introduced in
\cref{def:contraction}. We begin with the introduction of contractions of
(finite) polynomials.
*)
collect[sd_SeriesData, ζ_] := MapAt[collect[#, ζ] &, sd, 3];
collect[expr_, ζ_] := Collect[expr, ζ];

Zip[{}][P_] := P;
Zip[ζs_List][Ps_List] := Zip[ζs]/@Ps;
Zip[{ζ_,ζs___}][P_] := (collect[P // Zip[{ζs}],ζ] /.
        f_. ζ^d_. :> DD[f,{Dual[ζ], d}]) /.
        Dual[ζ] -> 0 /.
        ((Dual[ζ] /. {b->B, t->T, α -> A}) -> 1)
(*
We define contraction along the variables $x$ and $y$ (here packaged into the
matrix \mma{Q}).
*)
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
(*
We define contraction along the variables $a$ and $b$ (here packaged into the
matrix \mma{L}).
*)
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
(*
The function \mma{Pair} combines the above zipping functions into the final
contraction map.
*)
Pair[{}][L_PG,R_PG] := L R;
Pair[is_List][L_PG,R_PG] := Module[{n},
        Times[
                L /. ((v: b|B|t|T|a|x|y)[#] -> v[n@#]&/@is),
                R /. ((v: β|τ|α|A|ξ|η)[#] -> v[n@#]&/@is)
        ] // LZip[Join@@Table[Through[{β, τ, a}[n@i]],{i, is}]] //
        QZip[Join@@Table[Through[{ξ, y}[n@i]],{i, is}]]
]
(*
Our next task is to provide domain and codomain information for the
\mma{PG}-objects. These will be packaged inside a \mma{GDO}, (Gaußian
Differential Operator). The four lists' names refer to whether it is a domain or
a codomain, and whether the index corresponds to an \emph{open} strand or a
\emph{closed} one.
*)
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
(*
Next are defined functions for accessing and modifying sub-parts of
\mma{GDO}-objects. The last argument of \mma{Lookup} is the default value if
nothing is specified. This means that a morphism with empty domain or codomain
may be specified as such by omitting that portion of the definition.
*)
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
(*
The canonical form function (\mma{CF}) and the contraction mapping (\mma{Pair})
we extend to include \mma{GDO}-objects. Furthermore, on the level of
\mma{GDO}-objects we can compose morphisms and keep track of the corresponding
domains and codomains, using the left-to-right composition operator
\enquote{$\then$}.
*)
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
(*
We also define notions of equality and multiplication (by concatenation) for
\mma{GDO}'s.
*)
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
(*
For the sake of compatibility with Bar-Natan and van der Veen's program, we
introduce several conversion functions between the two notations.
*)
setEpsilonDegree[k_Integer][gdo_GDO] :=
        setP[Series[Normal@getP@gdo,{ϵ,0,k}]][gdo]

fromE[Subscript[\[DoubleStruckCapitalE],{do_List, dc_List}->{co_List, cc_List}][
        L_, Q_, P_
]] := toGDO[do, dc, co, cc, fromE[\[DoubleStruckCapitalE][L, Q, P]]]

fromE[Subscript[\[DoubleStruckCapitalE], dom_List->cod_List][
        L_, Q_, P_
]] := GDO["do" -> dom, "co" -> cod,
        "PG" -> fromE[\[DoubleStruckCapitalE][L, Q, P]]
]
(*
It is at this point that we implement the morphisms of the algebra $\CU$. Each
operation is prepended with a \enquote{\mma{c}} to emphasize that this is a
classical algebra, not a quantum deformation.
*)
fromLog[l_] := CF@Module[
        {L, l0 = Limit[l, ϵ->0]},
        L = l0 /. (η|y|ξ|x)[_]->0;
        PG[
                "L" -> L,
                "Q" -> l0 - L
        ]/.l2U
]

cΛ = (η[i] + E^(-γ α[i] - ϵ β[i]) η[j]/(1+γ ϵ η[j]ξ[i])) y[k] +
     (β[i] + β[j] + Log[1 + γ ϵ η[j]ξ[i]]/ϵ            ) b[k] +
     (α[i] + α[j] + Log[1 + γ ϵ η[j]ξ[i]]/γ            ) a[k] +
     (ξ[j] + E^(-γ α[j] - ϵ β[j]) ξ[i]/(1+γ ϵ η[j]ξ[i])) x[k];

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

cR[i_, j_] = GDO[
        "co" -> {i,j},
        "PG" -> toPG[ℏ a[j] b[i], (B[i]-1)/(-b[i]) x[j] y[i], 1]
]

cRi[i_, j_] = GDO[
        "co" -> {i,j},
        "PG" -> toPG[-ℏ a[j] b[i], (B[i]-1)/(B[i] b[i]) x[j] y[i], 1]
]

CC[i_] :=  GDO["co"->{i},"PG"->PG["P"->B[i]^( 1/2)]]
CCi[i_] := GDO["co"->{i},"PG"->PG["P"->B[i]^(-1/2)]]

cKink[i_]  = Module[{k}, cR[i,k] CCi[k] // cm[i, k, i]]
cKinki[i_] = Module[{k}, cRi[i,k] CC[k] // cm[i, k, i]]

cKinkn[0][i_]  = cη[i]
cKinkn[1][i_]  = cKink[i]
cKinkn[-1][i_] = cKinki[i]
cKinkn[n_Integer][i_] := Module[{j},cKinkn[n-1][i]cKink[j]//cm[i,j,i]]/; n > 1
cKinkn[n_Integer][i_] := Module[{j},cKinkn[n+1][i]cKinki[j]//cm[i,j,i]]/; n < -1

uR[i_, j_]  = Module[{k}, cR[i,j] cKinki[k] // cm[i, k, i]]
uRi[i_, j_] = Module[{k}, cRi[i,j] cKink[k] // cm[i, k, i]]
(*
\section{Implementation of the trace}
Now we implement the trace. We introduce several functions which extract the
various coefficients of a \mma{GDO}, so that we may apply
\cref{eq:trace_on_gaussian}. Coefficients are extracted based on whether they
belong to the matrix \mma{L} or the matrix \mma{Q}.
*)
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
(*
In order to run more efficiently, limits are first computed by direct
evaluation, unless such an operation is ill-defined. In such a case, the
corresponding series is computed and evaluated at the limit point.
*)
safeEval[f_][x_] := Module[{fx, x0},
        If[(fx=Quiet[f[x]]) === Indeterminate,
                Series[f[x0],{x0,x,0}]//Normal,
                fx
        ]
]

closeComponent[i_][gdo_GDO]:=gdo//
        setCO[Complement[gdo//getCO,{i}]]//
        setCC[Union[gdo//getCC,{i}]]
(*
Now we come to the implementation of the trace map. The current implementation
requires that the coefficient of $a_ib_i$ be zero. (See \cref{sec:limitations}
for how this restriction limits computability.)
*)
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
        ta = (1-Exp[-αα]) z[i];
        expL = cL + αα w[i] + ββ ta;
        expQ = safeEval[cQ[#] + z[i]ηη[#]ξξ[#]/(1-z[i] λ[#])&][ta];
        expP = safeEval[βP[#]/(1-z[i] λ[#])&][ta];
        CF[(gdo//closeComponent[i]//setL[expL]//setQ[expQ]//setP[expP])//.l2U]
] /; Module[
        {σ = getabCoef[i][gdo]},
        If[σ == 0,
                True,
                Message[tr::nonzeroSigma, i, ToString[σ]]; False
        ]
]
(*
Here we introduce some formatting to display the output more aesthetically.
*)
Format[gdo_GDO] := Subsuperscript[\[DoubleStruckCapitalE],
        Row[{gdo//getCO, ",", gdo//getCC}],
        Row[{gdo//getDO, ",", gdo//getDC}]
][gdo//getL, gdo//getQ, gdo//getP];
Format[pg_PG] := \[DoubleStruckCapitalE][pg//getL, pg//getQ, pg//getP];

SubscriptFormat[v_] := (Format[v[i_]] := Subscript[v, i]);

SubscriptFormat/@{y,b,t,a,x,z,w,η,β,α,ξ,A,B,T,W};
(*
\subsection{Implementing the full invariant}
Now we are in a position to implement the $Z$ invariant to tangles with a closed
component. We begin by defining an object representing an isolated strand with
arbitrary integer rotation number, \mma{CCn}:
*)
CCn[i_][n_Integer]:=Module[{j},
  If[n==0,
    GDO["co"->{i}],
    If[n>0,
      If[n==1,
        CC[i],
        CC[j]//CCn[i][n-1]//cm[i,j,i]
      ],
      If[n==-1,
        CCi[i],
        CCi[j]//CCn[i][n+1]//cm[i,j,i]
      ]
    ]
  ]
]
(*
Since multiplication is associative, we may implement a generalized
multiplication which can take any number of arguments. It is also named
\mma{cm}, with a first argument given as an ordered list of indices to be
concatenated.
*)
cm[{}, j_] := cη[j]
cm[{i_}, j_] := cσ[i,j]
cm[{i_, j_}, k_] := cm[i,j,k]
cm[ii_List, k_] := Module[
        {
                i  = First[ii],
                is = Rest[ii],
                j  ,
                js ,
                l
        },
        j  = First[is];
        js = Rest[is];
        cm[i,j,l] // cm[Prepend[js, l], k]
]
(*
The function \mma{toGDO} serves as the invariant for the generators of the tangles.
We define its value on crossings and on concatenations of elements.
*)
toGDO[Xp[i_,j_]] := cR[i,j]
toGDO[Xm[i_,j_]] := cRi[i,j]
toGDO[xs_Strand] := cm[List@@xs, First[xs]]
toGDO[xs_Loop]   := Module[{x = First[xs]}, cm[List@@xs, x]//tr[x]]

getIndices[RVT[cs_List, _List, _List]] := Sort@Catenate@(List@@@cs)

TerminalQ[cs_List][i_] := MemberQ[Last/@cs,i];
next[cs_List][i_]:=If[TerminalQ[cs][i],
	Nothing,
	Extract[cs,((#/.{c_,j_}->{c,j+1}&)@FirstPosition[i]@cs)]
]

InitialQ[cs_List][i_] := MemberQ[First/@cs,i];
prev[cs_List][i_]:=If[InitialQ[cs][i],
	Nothing,
	Extract[cs,((#/.{c_,j_}->{c,j-1}&)@FirstPosition[i]@cs)]
]
(*
To minimize the size of computations, whenever adjacent indices are present in
the partial computation, they are to be concatenated before more crossings are
introduced.
*)
MultiplyAdjacentIndices[{cs_List,calc_GDO}]:=Module[
	{ is=getCO[calc]
	, i
	, i2
	},
	i = SelectFirst[is,MemberQ[is,next[cs][#]]&];
	If[Head[i]===Missing,
		{cs,calc},
		i2 = next[cs][i];
		{DeleteCases[cs,i2,2], calc//cm[i,i2,i]}
	]
]

MultiplyAllAdjacentIndices[{cs_List, calc_GDO}] :=
        FixedPoint[MultiplyAdjacentIndices, {cs, calc}]

generateGDOFromXing[x:_Xp|_Xm,rs_Association]:=Module[
	{p, i,j, in, jn},
	{i,j} = List@@x;
	{in,jn} = Lookup[rs,{i,j},0];
	toGDO[x]*CCn[p[i]][in]*CCn[p[j]][jn] //cm[p[i],i,i]//cm[p[j],j,j]
]

addRotsToXingFreeStrands[rvt_RVT] := GDO[] * Times @@ (
        CCn[#][Lookup[rvt[[3]], #, 0]] & /@
        First /@ Select[rvt[[1]], Length@# == 1 &]
)
(*
Next we implement the framed link invariant \mma{ZFramed}.
*)
ZFramedStep[{_List,{},_Association,calc_GDO}]:={{},{},<||>,calc};
ZFramedStep[{cs_List,xs_List,rs_Association,calc_GDO}]:=Module[
        { x=First[xs], xss=Rest[xs]
        , csOut, calcOut
        , new
        },
        new=calc*generateGDOFromXing[x,rs];
        {csOut,calcOut} = MultiplyAllAdjacentIndices[{cs,new}];
        {csOut,xss,rs,calcOut}
]

ZFramed[rvt_RVT] := Last@FixedPoint[ZFramedStep, {Sequence @@ rvt,
        addRotsToXingFreeStrands[rvt]}]
ZFramed[L_] := ZFramed[toRVT@L]
(*
Finally, when we wish to consider the unframed invariant, we apply the function
\mma{Unwrithe}, defined below.
*)
Z[rvt_RVT] := Unwrithe@Last@FixedPoint[ZFramedStep, {Sequence @@ rvt, GDO[]}]
Z[L_] := Z[toRVT@L]

combineBySecond[l_List] := mergeWith[Total,#]& /@ GatherBy[l, First];
combineBySecond[lis___] := combineBySecond[Join[lis]]

mergeWith[f_, l_] := {l[[1, 1]], f@(#[[2]] & /@ l)}

Reindex[RVT[cs_, xs_, rs_]] := Module[
  {
    sf,
    cs2, xs2, rs2,
    repl, repl2
  },
   sf = Flatten[List@@#&/@cs];
   repl = (Thread[sf -> Range[Length[sf]]]);
   repl2 = repl /. {(a_ -> b_) -> ({a, i_} -> {b, i})};
   cs2 = cs /. repl;
   xs2 = xs /. repl;
   rs2 = rs /. repl2;
   RVT[cs2, xs2, rs2]
]

UnwritheComp[i_][gdo_GDO] := Module[
        {n = gdo//getL//SeriesCoefficient[#,{a[i]b[i],0,1}]&, j},
        gdo//(cKinkn[-n][j])//cm[i,j,i]
]

Unwrithe[gdo_GDO]:=(Composition@@(UnwritheComp/@(gdo//getCO)))@gdo

toRVT[L_RVT] := L
(*
The partial trace is what we use to close a subset of the strands in a tangle.
It takes the trace of all but one component, then returns the collection of all
such ways of leaving one component open. (As described in
\cref{sec:dependence-on-open-component}).
*)
ptr[L_RVT] := Module[
        {
                ZL = Z[L],
                cod
        },
        cod = getCO@ZL;
        Table[(Composition@@Table[tr[j], {j,Complement[cod,{i}]}])[ZL], {i,cod}]
]
ptr[L_] := ptr[toRVT[L]]
(*
In order to be able to compare \mma{GDO}'s properly, we require a way to
canonically represent them. This is achieved by reindexing the strands of the
link and selecting one who's resulting invariant comes first in an
(arbitrarily-selected) order, in this case the built-in ordering of expressions
as defined by Mathematica™.
*)
getGDOIndices[gdo_GDO]:=Sort@Catenate@Through[{getDO, getDC, getCO, getCC}@gdo]

isolateVarIndices[i_ -> j_] := (v:y|b|t|a|x|η|β|α|ξ|A|B|T|w|z|W)[i]->v[j];

ReindexBy[f_][gdo_GDO] := Module[
        {
        replacementRules,
        varIndexFunc,
        repFunc,
        indices = getGDOIndices[gdo]
        },
        replacementRules = Thread[indices->(f/@indices)];
        repFunc = ReplaceAll[replacementRules];
        varIndexFunc = ReplaceAll[Thread[isolateVarIndices[replacementRules]]];
        gdo//applyToPG[varIndexFunc]//
                applyToCO[repFunc]//
                applyToDO[repFunc]//
                applyToDC[repFunc]//
                applyToCC[repFunc]
]

fromAssoc[ass_] := Association[ass][#] &

ReindexToInteger[gdos_List] := Module[
        {is = getGDOIndices@gdos[[1]], f},
        f = fromAssoc@Thread[is -> Range[Length[is]]];
        ReindexBy[f]/@gdos
]

getReindications[gdos_List] := Module[
        {
                gdosInt = ReindexToInteger[gdos],
                is,
                fs,
                ls
        },
        is = getGDOIndices[gdosInt[[1]]];
        fs = (fromAssoc@*Association@*Thread)/@(is -> # & /@ Permutations[is]);
        ls = CF@ReindexBy[#]/@gdosInt&/@fs;
        Sort[Sort/@ls]
]

getCanonicalIndex[gdo_] := First@getReindications@gdo

deleteIndex[i_][expr_] := SeriesCoefficient[expr/.U2l, Sequence @@ ({#[i], 0, 0} & /@ {
        y, b, t, a, x, z, w
})]/.l2U
(*
Here we introduce functions to further verify the co-algebra structure of a
traced ribbon meta-Hopf algebra. In particular, the counit is responsible for
deleting a strand. This has further applications in determining whether the
invariants of individual components are contained in those of more complex
links.
*)
deleteIndexPG[i_][pg_PG] := pg//
        applyToL[deleteIndex[i]]//
        applyToQ[deleteIndex[i]]//
        applyToP[deleteIndex[i]]

deleteLoop[i_][gdo_] := gdo//
        applyToCC[Complement[#,{i}]&]//
        applyToPG[deleteIndexPG[i]]
