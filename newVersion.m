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

(* GDO = Gaußian Differential Operator *)
