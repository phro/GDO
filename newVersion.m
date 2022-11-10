(* PG[L, Q, P] = Perturbed Gaußian Pe^(L + Q) *)

toPG[L_, Q_, P_] := PG[<|"L"->L, "Q"->Q, "P"->P|>]

getL[pg_PG] := pg[[1,"L"]]
getQ[pg_PG] := pg[[1,"Q"]]
getP[pg_PG] := pg[[1,"P"]]

setL[L_][pg_PG] := Module[{b = pg[[1]]}, b["L"] = L; PG@b]
setQ[Q_][pg_PG] := Module[{b = pg[[1]]}, b["Q"] = Q; PG@b]
setP[P_][pg_PG] := Module[{b = pg[[1]]}, b["P"] = P; PG@b]

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

(* GDO = Gaußian Differential Operator *)
