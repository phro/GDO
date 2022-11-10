(* PG[L, Q, P] = Perturbed Gaußian Pe^(L + Q) *)

PG[a__][i_]:=Association[a][i]

Congruent[pg1_PG, pg2_PG] := And[
        CF[pg1["L"] == pg2["L"]],
        CF[pg1["Q"] == pg2["Q"]],
        CF[Normal[pg1["P"]-pg2["P"]] == 0]
]

pg1_PG pg2_PG := PG[<|
        "L"->pg1["L"] + pg2["L"],
        "Q"->pg1["Q"] + pg2["Q"],
        "P"->pg1["P"] * pg2["P"]
|>]

setEpsilonDegree[k_Integer][pg_PG]:= Module[{b = pg},
        b["P"] = Series[Normal@P,{ε, 0, k}]
]

(* GDO = Gaußian Differential Operator *)
