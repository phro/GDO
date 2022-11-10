(* PG[L, Q, P] = Perturbed Gaußian Pe^(L + Q) *)

PG[a__][i_]:=Association[a][i]

Congruent[pg1_PG, pg2_PG] := And[
        CF[pg1["L"] == pg2["L"]],
        CF[pg1["Q"] == pg2["Q"]],
        CF[Normal[pg1["P"]-pg2["P"]] == 0]
]

(* GDO = Gaußian Differential Operator *)
