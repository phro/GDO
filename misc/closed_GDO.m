toMixed[
        Subscript[\[DoubleStruckCapitalE],
                {o1_List, c1_List} -> {o2_List, c2_List}][L_,Q_,P_]
        ]:= Subscript[\[DoubleStruckCapitalE], {o1, c1} -> {o2, c2}][L,Q,P];
toMixed[Subscript[\[DoubleStruckCapitalE], o1_->o2_][L_,Q_,P_]]:=
        Subscript[\[DoubleStruckCapitalE], {o1, {}} -> {o2, {}}][L,Q,P];
toMixed[{o_List, c_List}]:= {o, c};
toMixed[is_List]:={is,{}};

addClosedDomain[domc_][
        Subscript[\[DoubleStruckCapitalE],
                {o1_List, c1_List} -> {o2_List, c2_List}][L_,Q_,P_]
        ]:=
        Subscript[\[DoubleStruckCapitalE],
                {o1, c1 \[Union] domc} -> {o2, c2}
        ][L,Q,P];
addClosedDomain[domc_][Subscript[\[DoubleStruckCapitalE], o1_->o2_][L_,Q_,P_]]:=
        Subscript[\[DoubleStruckCapitalE], {o1, domc} -> {o2, {}}][L,Q,P];

addClosedCodomain[codc_][
        Subscript[\[DoubleStruckCapitalE],
                {o1_List, c1_List} -> {o2_List, c2_List}][L_,Q_,P_]
        ]:=
        Subscript[\[DoubleStruckCapitalE],
                {o1, c1} -> {o2, c2 \[Union] codc}
        ][L,Q,P];
addClosedCodomain[codc_][
        Subscript[\[DoubleStruckCapitalE], o1_->o2_][L_,Q_,P_]
] := Subscript[\[DoubleStruckCapitalE], {o1, {}} -> {o2, codc}][L,Q,P];

addClosedIndices[domc_,codc_][GDO_] :=
  GDO//addClosedDomain[domc]//addClosedCodomain[codc];

closeComponent[i_][{os_List, cs_List}] := {Complement[os,{i}], Union[cs,{i}]}
closeComponent[i_][is_List] := {Complement[is,{i}], {i}}


(* ::Input::Initialization:: *)
(*Subscript[B, is_List][Subscript[\[DoubleStruckCapitalE], d1_->r1_][L1_,Q1_,P1_],Subscript[\[DoubleStruckCapitalE], d2_->r2_][L2_,Q2_,P2_]]:=Subscript[\[DoubleStruckCapitalE], (d1\[Union]Complement[d2,is])->(r2\[Union]Complement[r1,is])]@@Subscript[B, is][\[DoubleStruckCapitalE][L1,Q1,P1],\[DoubleStruckCapitalE][L2,Q2,P2]];*)
Subscript[\[DoubleStruckCapitalE],
        {d1_List, dc1_List} -> {r1_List, rc1_List}
][L1_,Q1_,P1_]//
Subscript[\[DoubleStruckCapitalE],
        {d2_List, dc2_List} -> {r2_List, rc2_List}
][L2_,Q2_,P2_] :=
Subscript[B, r1\[Intersection]d2][
        Subscript[\[DoubleStruckCapitalE], d1->r1][L1,Q1,P1],
        Subscript[\[DoubleStruckCapitalE], d2->r2][L2,Q2,P2]
]//addClosedIndices[dc1\[Union]dc2,rc1\[Union]rc2];
Subscript[\[DoubleStruckCapitalE],
        {d1_List, dc1_List} -> {r1_List, rc1_List}
][L1_,Q1_,P1_]//
Subscript[\[DoubleStruckCapitalE],
        d2_->r2_
][L2_,Q2_,P2_]:=
Subscript[B, r1\[Intersection]d2][
        Subscript[\[DoubleStruckCapitalE], d1->r1][L1,Q1,P1],
        Subscript[\[DoubleStruckCapitalE], d2->r2][L2,Q2,P2]
]//addClosedIndices[dc1,rc1];
Subscript[\[DoubleStruckCapitalE],
        d1_->r1_
][L1_,Q1_,P1_]//
Subscript[\[DoubleStruckCapitalE],
        {d2_List, dc2_List} -> {r2_List, rc2_List}
][L2_,Q2_,P2_]:=
Subscript[B, r1\[Intersection]d2][
        Subscript[\[DoubleStruckCapitalE], d1->r1][L1,Q1,P1],
        Subscript[\[DoubleStruckCapitalE], d2->r2][L2,Q2,P2]
]//addClosedIndices[dc2,rc2];

Congruent[
        Subscript[\[DoubleStruckCapitalE],
                {d1_List, dc1_List} -> {r1_List, rc1_List}
        ][L1_,Q1_,P1_]
        Subscript[\[DoubleStruckCapitalE],
                {d2_List, dc2_List} -> {r2_List, rc2_List}
        ][L2_,Q2_,P2_]
] ^:=
        (Sort@d1 ==Sort@d2)  &&
        (Sort@r1 ==Sort@r2)  &&
        (Sort@dc1==Sort@dc2) &&
        (Sort@rc1==Sort@rc2) &&
        Congruent[
                \[DoubleStruckCapitalE][L1,Q1,P1],
                \[DoubleStruckCapitalE][L2,Q2,P2]
        ];
(*Subscript[\[DoubleStruckCapitalE], d1_->r1_][L1_,Q1_,P1_]Subscript[\[DoubleStruckCapitalE], d2_->r2_][L2_,Q2_,P2_] ^:= Subscript[\[DoubleStruckCapitalE], (d1\[Union]d2)->(r1\[Union]r2)]@@(\[DoubleStruckCapitalE][L1,Q1,P1]\[DoubleStruckCapitalE][L2,Q2,P2]);*)
(*Subscript[Subscript[\[DoubleStruckCapitalE], dr_][L_,Q_,P_], $k_]:=Subscript[\[DoubleStruckCapitalE], dr]@@Subscript[\[DoubleStruckCapitalE][L,Q,P], $k];*)
(*Subscript[\[DoubleStruckCapitalE], _][\[ScriptCapitalE]___][i_Integer]:={\[ScriptCapitalE]}\[LeftDoubleBracket]i\[RightDoubleBracket];*)
