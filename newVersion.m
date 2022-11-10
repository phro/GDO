(* PG[L, Q, P] = Perturbed Gaußian Pe^(L + Q) *)

Congruent[PG[pg1_Association], PG[pg2_Association]] := And[
        CF[pg1["L"] == pg2["L"]],
        CF[pg1["Q"] == pg2["Q"]],
        CF[Normal[pg1["P"]-pg2["P"]] == 0]
]

(* GDO = Gaußian Differential Operator *)
