toMixed[Subscript[\[DoubleStruckCapitalE], o1_->o2_][L_,Q_,P_]]:=
  Subscript[\[DoubleStruckCapitalE], {o1, {}} -> {o2, {}}][L,Q,P];
toMixed[
  Subscript[\[DoubleStruckCapitalE], {o1_, c1_} -> {o2_, c2_}][L_,Q_,P_]
]:= Subscript[\[DoubleStruckCapitalE], {o1, c1} -> {o2, c2}][L,Q,P];

addClosedDomain[domc_][
  Subscript[\[DoubleStruckCapitalE], {o1_, c1_} -> {o2_, c2_}][L_,Q_,P_]
]:=
  Subscript[\[DoubleStruckCapitalE],
    {o1, c1 \[Union] domc} -> {o2, c2}
  ][L,Q,P];
addClosedDomain[domc_][
  Subscript[\[DoubleStruckCapitalE], o1_->o2_][L_,Q_,P_]
]:=
  Subscript[\[DoubleStruckCapitalE], {o1, domc} -> {o2, {}}][L,Q,P];
addClosedCodomain[codc_][
  Subscript[\[DoubleStruckCapitalE], {o1_, c1_} -> {o2_, c2_}][L_,Q_,P_]
]:=
  Subscript[\[DoubleStruckCapitalE],
    {o1, c1} -> {o2, c2 \[Union] codc}
  ][L,Q,P];
addClosedCodomain[codc_][
  Subscript[\[DoubleStruckCapitalE], o1_->o2_][L_,Q_,P_]
]:=
  Subscript[\[DoubleStruckCapitalE], {o1, {}} -> {o2, codc}][L,Q,P];

addClosedIndices[domc_,codc_][GDO_] :=
  GDO//addClosedDomain[domc]//addClosedCodomain[codc];


(* ::Input::Initialization:: *)
(*Subscript[B, is_List][Subscript[\[DoubleStruckCapitalE], d1_->r1_][L1_,Q1_,P1_],Subscript[\[DoubleStruckCapitalE], d2_->r2_][L2_,Q2_,P2_]]:=Subscript[\[DoubleStruckCapitalE], (d1\[Union]Complement[d2,is])->(r2\[Union]Complement[r1,is])]@@Subscript[B, is][\[DoubleStruckCapitalE][L1,Q1,P1],\[DoubleStruckCapitalE][L2,Q2,P2]];*)
Subscript[\[DoubleStruckCapitalE], {d1_, dc1_} -> {r1_, rc1_}][L1_,Q1_,P1_]// Subscript[\[DoubleStruckCapitalE], d2_->r2_][L2_,Q2_,P2_]:= Subscript[B, r1\[Intersection]d2][Subscript[\[DoubleStruckCapitalE], d1->r1][L1,Q1,P1],Subscript[\[DoubleStruckCapitalE], d2->r2][L2,Q2,P2]]//addClosedIndices[dc1,rc1];
Subscript[\[DoubleStruckCapitalE], {d1_, dc1_} -> {r1_, rc1_}][L1_,Q1_,P1_]//Subscript[\[DoubleStruckCapitalE], {d2_, {}} -> {r2_, rc2_}][L2_,Q2_,P2_]:= Subscript[B, r1\[Intersection]d2][Subscript[\[DoubleStruckCapitalE], d1->r1][L1,Q1,P1],Subscript[\[DoubleStruckCapitalE], d2->r2][L2,Q2,P2]]//addClosedIndices[dc1,rc1\[Union]rc2];
Subscript[\[DoubleStruckCapitalE], {d1_, dc1_} -> {r1_, rc1_}][L1_,Q1_,P1_] ===
Subscript[\[DoubleStruckCapitalE], {d2_, dc2_} -> {r2_, rc2_}][L2_,Q2_,P2_] ^:=
(d1==d2)&&(r1==r2)&& (dc1==dc2) && (rc1==rc2) &&
(\[DoubleStruckCapitalE][L1,Q1,P1]===\[DoubleStruckCapitalE][L2,Q2,P2]);
(*Subscript[\[DoubleStruckCapitalE], d1_->r1_][L1_,Q1_,P1_]Subscript[\[DoubleStruckCapitalE], d2_->r2_][L2_,Q2_,P2_] ^:= Subscript[\[DoubleStruckCapitalE], (d1\[Union]d2)->(r1\[Union]r2)]@@(\[DoubleStruckCapitalE][L1,Q1,P1]\[DoubleStruckCapitalE][L2,Q2,P2]);*)
(*Subscript[Subscript[\[DoubleStruckCapitalE], dr_][L_,Q_,P_], $k_]:=Subscript[\[DoubleStruckCapitalE], dr]@@Subscript[\[DoubleStruckCapitalE][L,Q,P], $k];*)
(*Subscript[\[DoubleStruckCapitalE], _][\[ScriptCapitalE]___][i_Integer]:={\[ScriptCapitalE]}\[LeftDoubleBracket]i\[RightDoubleBracket];*)
