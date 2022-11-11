(* PG[L, Q, P] = Perturbed Gaußian Pe^(L + Q) *)

toPG[L_, Q_, P_] := PG@<|"L"->L, "Q"->Q, "P"->P|>

getL[pg_PG] := pg[[1,"L"]]
getQ[pg_PG] := pg[[1,"Q"]]
getP[pg_PG] := pg[[1,"P"]]

setL[L_][pg_PG] := Module[{b = pg[[1]]}, b["L"] = L; PG@b]
setQ[Q_][pg_PG] := Module[{b = pg[[1]]}, b["Q"] = Q; PG@b]
setP[P_][pg_PG] := Module[{b = pg[[1]]}, b["P"] = P; PG@b]

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

QZip[{ζs_List}][pg_PG] := Module[{ζ, z, zs, c, ys, ηs, qt, zrule, ζrule},
        zs = Dual/@ζs;
        c  = CF[Q/.Alternatives@@Union[ζs, zs]->0];
        ys = CF@Table[D[Q,ζ]/Alternatives@@zs->0,{ζ,ζs}];
        ηs = CF@Table[D[Q,z]/Alternatives@@ζs->0,{z,zs}];
        qt = CF@Inverse@Table[KronekerDelta[z, Dual[ζ]] - D[Q,z,ζ],{z,zs}];
        zrule = Thread[zs -> CF[qt . (zs + ys)]];
        ζrule = Thread[ζs -> ζs + ηs . qt];
        CF@setQ[c + ηs.qt.ys]@setP[Det[qt] Zip[ζs][P /. Union[zrule, ζrule]]]@pg
]
(* GDO = Gaußian Differential Operator *)
