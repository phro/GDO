(* ::Package:: *)

(************************************************************************)
(* This file was generated automatically by the Mathematica front end.  *)
(* It contains Initialization cells from a Notebook file, which         *)
(* typically will have the same name as this file except ending in      *)
(* ".nb" instead of ".m".                                               *)
(*                                                                      *)
(* This file is intended to be loaded into the Mathematica kernel using *)
(* the package loading commands Get or Needs.  Doing so is equivalent   *)
(* to using the Evaluate Initialization Cells menu command in the front *)
(* end.                                                                 *)
(*                                                                      *)
(* DO NOT EDIT THIS FILE.  This entire file is regenerated              *)
(* automatically each time the parent Notebook file is saved in the     *)
(* Mathematica front end.  Any changes you make to this file will be    *)
(* overwritten.                                                         *)
(************************************************************************)



(*Mathematica implementation of Perturbed Gaussian generating functions for universal
knot invariants by Dror Bar-Natan and Roland van der Veen, September 2021. (Standard version)*)


(* ::Input::Initialization:: *)
Once[<<KnotTheory`];


(* ::Input::Initialization:: *)
 $k=1;\[Gamma]=1;\[HBar]=1;


(* ::Input::Initialization:: *)
CCF[\[ScriptCapitalE]_] := ExpandDenominator@ExpandNumerator@Together[
Expand[\[ScriptCapitalE]] //. E^x_ E^y_:>E^(x+y) /. E^x_:>E^CCF[x]];
CF[\[ScriptCapitalE]_List]:=CF/@\[ScriptCapitalE];
CF[sd_SeriesData] := MapAt[CF,sd,3];
CF[\[ScriptCapitalE]_] := Module[
{vs=Cases[\[ScriptCapitalE],Subscript[(y|b|t|a|x|\[Eta]|\[Beta]|\[Tau]|\[Alpha]|\[Xi]), _],\[Infinity]]\[Union]{y,b,t,a,x,\[Eta],\[Beta],\[Tau],\[Alpha],\[Xi]}},
Total[CoefficientRules[Expand[\[ScriptCapitalE]], vs] /. (ps_->c_) :> CCF[c](Times@@(vs^ps))]
];
CF[\[ScriptCapitalE]_\[DoubleStruckCapitalE]]:=CF/@\[ScriptCapitalE]; CF[Subscript[\[DoubleStruckCapitalE], sp___][\[ScriptCapitalE]s___]]:=CF/@Subscript[\[DoubleStruckCapitalE], sp][\[ScriptCapitalE]s];


(* ::Input::Initialization:: *)
K\[Delta]/:Subscript[K\[Delta], i_,j_]:=If[i===j,1,0];


(* ::Input::Initialization:: *)
\[DoubleStruckCapitalE]/:\[DoubleStruckCapitalE][L1_,Q1_,P1_]\[Congruent]\[DoubleStruckCapitalE][L2_,Q2_,P2_]:=CF[L1==L2]\[And]CF[Q1==Q2]\[And]CF[Normal[P1-P2]==0];
\[DoubleStruckCapitalE]/:\[DoubleStruckCapitalE][L1_,Q1_,P1_]\[DoubleStruckCapitalE][L2_,Q2_,P2_]:=\[DoubleStruckCapitalE][L1+L2,Q1+Q2,P1*P2];
Subscript[\[DoubleStruckCapitalE][L_,Q_,P_], $k_]:=\[DoubleStruckCapitalE][L,Q,Series[Normal@P,{\[Epsilon],0,$k}]];


(* ::Input::Initialization:: *)
{SuperStar[t],SuperStar[b],SuperStar[y],SuperStar[a],SuperStar[x],SuperStar[z]}={\[Tau],\[Beta],\[Eta],\[Alpha],\[Xi],\[Zeta]}; 
{SuperStar[\[Tau]],SuperStar[\[Beta]],SuperStar[\[Eta]],SuperStar[\[Alpha]],SuperStar[\[Xi]],SuperStar[\[Zeta]]}={t,b,y,a,x,z}; SuperStar[(Subscript[u_, i_])]:=Subscript[(SuperStar[u]), i];


(* ::Input::Initialization:: *)
U2l={\!\(
\*SubsuperscriptBox[\(B\), \(i_\), \(p_.\)] :> 
\*SuperscriptBox[\(E\), \(\(-p\)\ \[HBar]\ \[Gamma]\ 
\*SubscriptBox[\(b\), \(i\)]\)]\),B^p_.:>E^(-p \[HBar] \[Gamma] b), \!\(
\*SubsuperscriptBox[\(T\), \(i_\), \(p_.\)] :> 
\*SuperscriptBox[\(E\), \(\(-p\)\ \[HBar]\ 
\*SubscriptBox[\(t\), \(i\)]\)]\),T^p_.:>E^(-p \[HBar] t),\!\(
\*SubsuperscriptBox[\(\[ScriptCapitalA]\), \(i_\), \(p_.\)] :> 
\*SuperscriptBox[\(E\), \(p\ \[Gamma]\ 
\*SubscriptBox[\(\[Alpha]\), \(i\)]\)]\),\[ScriptCapitalA]^p_.:>E^(p \[Gamma] \[Alpha])}; 
l2U={E^(c_. Subscript[b, i_]+d_.):>\!\(
\*SubsuperscriptBox[\(B\), \(i\), \(\(-c\)/\((\[HBar]\ \[Gamma])\)\)] 
\*SuperscriptBox[\(E\), \(d\)]\),E^(c_. b+d_.):>B^(-c/(\[HBar] \[Gamma])) E^d,
E^(c_. Subscript[t, i_]+d_.):>\!\(
\*SubsuperscriptBox[\(T\), \(i\), \(\(-c\)/\[HBar]\)] 
\*SuperscriptBox[\(E\), \(d\)]\),E^(c_. t+d_.):>T^(-c/\[HBar]) E^d,
E^(c_. Subscript[\[Alpha], i_]+d_.):>\!\(
\*SubsuperscriptBox[\(\[ScriptCapitalA]\), \(i\), \(c/\[Gamma]\)] 
\*SuperscriptBox[\(E\), \(d\)]\),E^(c_. \[Alpha]+d_.):>\[ScriptCapitalA]^(c/\[Gamma]) E^d,
E^\[ScriptCapitalE]_:>E^Expand@\[ScriptCapitalE]};


(* ::Input::Initialization:: *)
Subscript[D, b][f_]:=\!\(
\*SubscriptBox[\(\[PartialD]\), \(b\)]f\)-\[HBar] \[Gamma] B \!\(
\*SubscriptBox[\(\[PartialD]\), \(B\)]f\); Subscript[D, Subscript[b, i_]][f_]:=\!\(
\*SubscriptBox[\(\[PartialD]\), 
SubscriptBox[\(b\), \(i\)]]f\)-\[HBar] \[Gamma] Subscript[B, i]\!\(
\*SubscriptBox[\(\[PartialD]\), 
SubscriptBox[\(B\), \(i\)]]f\);
Subscript[D, t][f_]:=\!\(
\*SubscriptBox[\(\[PartialD]\), \(t\)]f\)-\[HBar] T \!\(
\*SubscriptBox[\(\[PartialD]\), \(T\)]f\); Subscript[D, Subscript[t, i_]][f_]:=\!\(
\*SubscriptBox[\(\[PartialD]\), 
SubscriptBox[\(t\), \(i\)]]f\)-\[HBar] Subscript[T, i]\!\(
\*SubscriptBox[\(\[PartialD]\), 
SubscriptBox[\(T\), \(i\)]]f\); 
Subscript[D, \[Alpha]][f_]:=\!\(
\*SubscriptBox[\(\[PartialD]\), \(\[Alpha]\)]f\)+\[Gamma] \[ScriptCapitalA] \!\(
\*SubscriptBox[\(\[PartialD]\), \(\[ScriptCapitalA]\)]f\); Subscript[D, Subscript[\[Alpha], i_]][f_]:=\!\(
\*SubscriptBox[\(\[PartialD]\), 
SubscriptBox[\(\[Alpha]\), \(i\)]]f\)+\[Gamma] Subscript[\[ScriptCapitalA], i] \!\(
\*SubscriptBox[\(\[PartialD]\), 
SubscriptBox[\(\[ScriptCapitalA]\), \(i\)]]f\);
Subscript[D, v_][f_]:=\!\(
\*SubscriptBox[\(\[PartialD]\), \(v\)]f\); \!\(\*SubscriptBox[\(D\), \({v_, 0}\)]\)[f_]:=f; \!\(\*SubscriptBox[\(D\), \({}\)]\)[f_]:=f; \!\(\*SubscriptBox[\(D\), \({v_, n_Integer}\)]\)[f_]:=Subscript[D, v][\!\(\*SubscriptBox[\(D\), \({v, n - 1}\)]\)[f]];
\!\(\*SubscriptBox[\(D\), \({l_List, ls___}\)]\)[f_]:=\!\(\*SubscriptBox[\(D\), \({ls}\)]\)[Subscript[D, l][f]];


(* ::Input::Initialization:: *)
collect[sd_SeriesData, \[Zeta]_] := MapAt[collect[#,\[Zeta]]&,sd,3];
collect[\[ScriptCapitalE]_,\[Zeta]_] := Collect[\[ScriptCapitalE],\[Zeta]];
\!\(\*SubscriptBox[\(Zip\), \({}\)]\)[P_]:=P;
Subscript[Zip, \[Zeta]s_][Ps_List]:=Subscript[Zip, \[Zeta]s]/@Ps;
\!\(\*SubscriptBox[\(Zip\), \({\[Zeta]_, \[Zeta]s___}\)]\)[P_] := 
(collect[P//\!\(\*SubscriptBox[\(Zip\), \({\[Zeta]s}\)]\),\[Zeta]] /. f_. \[Zeta]^d_.:>(\!\(\*SubscriptBox[\(D\), \({
\*SuperscriptBox[\(\[Zeta]\), \(*\)], d}\)]\)[f]))/.SuperStar[\[Zeta]]->0/.((SuperStar[\[Zeta]]/.{b->B,t->T,\[Alpha]->\[ScriptCapitalA]})->1)


(* ::Input::Initialization:: *)
Subscript[QZip, \[Zeta]s_List]@\[DoubleStruckCapitalE][L_,Q_,P_] := Module[{\[Zeta],z,zs,c,ys,\[Eta]s,qt,zrule,\[Zeta]rule,out},
zs=Table[SuperStar[\[Zeta]],{\[Zeta],\[Zeta]s}];
c=CF[Q/.Alternatives@@(\[Zeta]s\[Union]zs)->0];
ys=CF@Table[\!\(
\*SubscriptBox[\(\[PartialD]\), \(\[Zeta]\)]\((Q /. Alternatives @@ zs -> 0)\)\),{\[Zeta],\[Zeta]s}];
\[Eta]s=CF@Table[\!\(
\*SubscriptBox[\(\[PartialD]\), \(z\)]\((Q /. Alternatives @@ \[Zeta]s -> 0)\)\),{z,zs}];
qt=CF@Inverse@Table[Subscript[K\[Delta], z,SuperStar[\[Zeta]]]-\!\(
\*SubscriptBox[\(\[PartialD]\), \(z, \[Zeta]\)]Q\),{\[Zeta],\[Zeta]s},{z,zs}];
zrule=Thread[zs->CF[qt.(zs+ys)]];
\[Zeta]rule=Thread[\[Zeta]s->\[Zeta]s+\[Eta]s.qt];
CF /@ \[DoubleStruckCapitalE][L,c+\[Eta]s.qt.ys,Det[qt]Subscript[Zip, \[Zeta]s][P/.(zrule\[Union]\[Zeta]rule)]] ];


(* ::Input::Initialization:: *)
Subscript[LZip, \[Zeta]s_List]@\[DoubleStruckCapitalE][L_,Q_,P_] := Module[{\[Zeta],z,zs,Zs,c,ys,\[Eta]s,lt,zrule,Zrule,\[Zeta]rule,Q1,EEQ,EQ},
zs=Table[SuperStar[\[Zeta]],{\[Zeta],\[Zeta]s}];
Zs=zs/.{b->B,t->T,\[Alpha]->\[ScriptCapitalA]};
c=L/.Alternatives@@(\[Zeta]s\[Union]zs)->0/.Alternatives@@Zs->1;
ys=Table[\!\(
\*SubscriptBox[\(\[PartialD]\), \(\[Zeta]\)]\((L /. Alternatives @@ zs -> 0)\)\),{\[Zeta],\[Zeta]s}];
\[Eta]s=Table[\!\(
\*SubscriptBox[\(\[PartialD]\), \(z\)]\((L /. Alternatives @@ \[Zeta]s -> 0)\)\),{z,zs}];
lt=Inverse@Table[Subscript[K\[Delta], z,SuperStar[\[Zeta]]]-\!\(
\*SubscriptBox[\(\[PartialD]\), \(z, \[Zeta]\)]L\),{\[Zeta],\[Zeta]s},{z,zs}];
zrule=Thread[zs->lt.(zs+ys)];
Zrule=Join[zrule,zrule/.r_Rule:>((U=r[[1]]/.{b->B,t->T,\[Alpha]->\[ScriptCapitalA]})->(U/.U2l/.r//.l2U))];
\[Zeta]rule=Thread[\[Zeta]s->\[Zeta]s+\[Eta]s.lt];
Q1=Q/.(Zrule\[Union]\[Zeta]rule);
EEQ[ps___]:=EEQ[ps]=(CF[E^-Q1 Subscript[D, Thread[{zs,{ps}}]][E^Q1]]/.{Alternatives@@zs->0,Alternatives@@Zs->1});
CF@\[DoubleStruckCapitalE][c+\[Eta]s.lt.ys,Q1/.{Alternatives@@zs->0,Alternatives@@Zs->1},
Det[lt](Subscript[Zip, \[Zeta]s][(EQ@@zs)(P/.(Zrule\[Union]\[Zeta]rule))] /.
Derivative[ps___][EQ][___]:> EEQ[ps] /. _EQ->1)]];


(* ::Input::Initialization:: *)
\!\(\*SubscriptBox[\(B\), \({}\)]\)[L_,R_]:=L R;
\!\(\*SubscriptBox[\(B\), \({is__}\)]\)[L_\[DoubleStruckCapitalE],R_\[DoubleStruckCapitalE]] := Module[{n},
Times[
L/.Table[Subscript[(v:b|B|t|T|a|x|y), i]->Subscript[v, n@i],{i,{is}}],
R/.Table[Subscript[(v:\[Beta]|\[Tau]|\[Alpha]|\[ScriptCapitalA]|\[Xi]|\[Eta]), i]->Subscript[v, n@i],{i,{is}}]
] // Subscript[LZip, Join@@Table[{Subscript[\[Beta], n@i],Subscript[\[Tau], n@i],Subscript[a, n@i]},{i,{is}}]] // Subscript[QZip, Join@@Table[{Subscript[\[Xi], n@i],Subscript[y, n@i]},{i,{is}}]] ];
Subscript[B, is___][L_,R_]:=\!\(\*SubscriptBox[\(B\), \({is}\)]\)[L,R];


(* ::Input::Initialization:: *)
Subscript[B, is_List][Subscript[\[DoubleStruckCapitalE], d1_->r1_][L1_,Q1_,P1_],Subscript[\[DoubleStruckCapitalE], d2_->r2_][L2_,Q2_,P2_]]:=Subscript[\[DoubleStruckCapitalE], (d1\[Union]Complement[d2,is])->(r2\[Union]Complement[r1,is])]@@Subscript[B, is][\[DoubleStruckCapitalE][L1,Q1,P1],\[DoubleStruckCapitalE][L2,Q2,P2]];
Subscript[\[DoubleStruckCapitalE], d1_->r1_][L1_,Q1_,P1_]//Subscript[\[DoubleStruckCapitalE], d2_->r2_][L2_,Q2_,P2_] := Subscript[B, r1\[Intersection]d2][Subscript[\[DoubleStruckCapitalE], d1->r1][L1,Q1,P1],Subscript[\[DoubleStruckCapitalE], d2->r2][L2,Q2,P2]];
Subscript[\[DoubleStruckCapitalE], d1_->r1_][L1_,Q1_,P1_]\[Congruent]Subscript[\[DoubleStruckCapitalE], d2_->r2_][L2_,Q2_,P2_] ^:= (d1==d2)\[And](r1==r2)\[And](\[DoubleStruckCapitalE][L1,Q1,P1]\[Congruent]\[DoubleStruckCapitalE][L2,Q2,P2]);
Subscript[\[DoubleStruckCapitalE], d1_->r1_][L1_,Q1_,P1_]Subscript[\[DoubleStruckCapitalE], d2_->r2_][L2_,Q2_,P2_] ^:= Subscript[\[DoubleStruckCapitalE], (d1\[Union]d2)->(r1\[Union]r2)]@@(\[DoubleStruckCapitalE][L1,Q1,P1]\[DoubleStruckCapitalE][L2,Q2,P2]);
Subscript[Subscript[\[DoubleStruckCapitalE], dr_][L_,Q_,P_], $k_]:=Subscript[\[DoubleStruckCapitalE], dr]@@Subscript[\[DoubleStruckCapitalE][L,Q,P], $k];
Subscript[\[DoubleStruckCapitalE], _][\[ScriptCapitalE]___][i_]:={\[ScriptCapitalE]}[[i]];


(* ::Input::Initialization:: *)
Subscript[\[DoubleStruckCapitalE], dr_][\[CapitalLambda]_]:=CF@Module[{L,\[CapitalLambda]0=Limit[\[CapitalLambda],\[Epsilon]->0]},Subscript[Subscript[\[DoubleStruckCapitalE], dr][L=\[CapitalLambda]0 /. Subscript[(\[Eta]|y|\[Xi]|x), _]->0,\[CapitalLambda]0-L,E^(\[CapitalLambda]-\[CapitalLambda]0)], $k]/.l2U]


(* ::Input::Initialization:: *)
SetAttributes[Define, HoldAll];
Define[def_,defs__] := (Define[def]; Define[defs];);
Define[Subscript[op_, is__]=\[ScriptCapitalE]_] := Module[{SD,ii,jj,kk,isp,nis,nisp,sis},Block[{i,j,k},
ReleaseHold[Hold[
SD[Subscript[op, nisp,$k_Integer],Block[{i,j,k},Subscript[op, isp,$k]=\[ScriptCapitalE];Subscript[op, nis,$k]]];
SD[Subscript[op, isp],\!\(\*SubscriptBox[\(op\), \({is}, $k\)]\)]; SD[Subscript[op, sis__],\!\(\*SubscriptBox[\(op\), \({sis}\)]\)];
]/. {SD->SetDelayed,
isp->{is}/.{i->i_,j->j_,k->k_},
nis->{is}/.{i->ii,j->jj,k->kk},
nisp->{is}/.{i->ii_,j->jj_,k->kk_}
}]  ]]


(* ::Input::Initialization:: *)
Subscript[sm, i_,j_->k_]:=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i, j} \[Rule] {k}\)]\)[Subscript[b, k](Subscript[\[Beta], i]+Subscript[\[Beta], j])+Subscript[t, k](Subscript[\[Tau], i]+Subscript[\[Tau], j])+Subscript[a, k](Subscript[\[Alpha], i]+Subscript[\[Alpha], j])+Subscript[y, k](Subscript[\[Eta], i]+Subscript[\[Eta], j])+Subscript[x, k](Subscript[\[Xi], i]+Subscript[\[Xi], j])];
Subscript[s\[CapitalDelta], i_->j_,k_]:=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i} \[Rule] {j, k}\)]\)[Subscript[\[Beta], i](Subscript[b, j]+Subscript[b, k])+Subscript[\[Tau], i](Subscript[t, j]+Subscript[t, k])+Subscript[\[Alpha], i](Subscript[a, j]+Subscript[a, k])+Subscript[\[Eta], i](Subscript[y, j]+Subscript[y, k])+Subscript[\[Xi], i](Subscript[x, j]+Subscript[x, k])];
Subscript[sS, i_]:=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i} \[Rule] {i}\)]\)[-Subscript[\[Beta], i] Subscript[b, i]-Subscript[\[Tau], i] Subscript[t, i]-Subscript[\[Alpha], i] Subscript[a, i]-Subscript[\[Eta], i] Subscript[y, i]-Subscript[\[Xi], i] Subscript[x, i]];
Subscript[s\[Epsilon], i_]:=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({} \[Rule] {i}\)]\)[0];Subscript[s\[Eta], i_]:=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i} \[Rule] {}\)]\)[0];


(* ::Input::Initialization:: *)
Subscript[s\[Sigma], i_->j_]:=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i} \[Rule] {j}\)]\)[Subscript[\[Beta], i] Subscript[b, j]+Subscript[\[Tau], i] Subscript[t, j]+Subscript[\[Alpha], i] Subscript[a, j]+Subscript[\[Eta], i] Subscript[y, j]+Subscript[\[Xi], i] Subscript[x, j]];
Subscript[s\[CapitalUpsilon], i_->j_,k_,l_,m_]:=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i} \[Rule] {j, k, l, m}\)]\)[Subscript[\[Beta], i] Subscript[b, k]+Subscript[\[Tau], i] Subscript[t, k]+Subscript[\[Alpha], i] Subscript[a, l]+Subscript[\[Eta], i] Subscript[y, j]+Subscript[\[Xi], i] Subscript[x, m]];


(* ::Input::Initialization:: *)
Define[Subscript[a\[Sigma], i->j]=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i} \[Rule] {j}\)]\)[Subscript[a, j] Subscript[\[Alpha], i]+Subscript[x, j] Subscript[\[Xi], i]],Subscript[b\[Sigma], i->j]=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i} \[Rule] {j}\)]\)[Subscript[b, j] Subscript[\[Beta], i]+Subscript[y, j] Subscript[\[Eta], i]]]


(* ::Input::Initialization:: *)
Define[Subscript[am, i,j->k]=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i, j} \[Rule] {k}\)]\)[(Subscript[\[Alpha], i]+Subscript[\[Alpha], j])Subscript[a, k]+(\!\(
\*SubsuperscriptBox[\(\[ScriptCapitalA]\), \(j\), \(-1\)] 
\*SubscriptBox[\(\[Xi]\), \(i\)]\)+Subscript[\[Xi], j])Subscript[x, k]],
Subscript[bm, i,j->k]=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i, j} \[Rule] {k}\)]\)[(Subscript[\[Beta], i]+Subscript[\[Beta], j])Subscript[b, k]+(Subscript[\[Eta], i]+E^(- \[Epsilon] Subscript[\[Beta], i]) Subscript[\[Eta], j])Subscript[y, k]]]


(* ::Input::Initialization:: *)
Define[Subscript[R, i,j]=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({} \[Rule] {i, j}\)]\)[\[HBar] Subscript[a, j] Subscript[b, i]+\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(k = 1\), \($k + 1\)]\ 
\*FractionBox[\(
\*SuperscriptBox[\((1 - 
\*SuperscriptBox[\(E\), \(\[Gamma]\ \[Epsilon]\ \[HBar]\)])\), \(k\)] 
\*SuperscriptBox[\((\[HBar]\ 
\*SubscriptBox[\(y\), \(i\)] 
\*SubscriptBox[\(x\), \(j\)])\), \(k\)]\), \(k \((1 - 
\*SuperscriptBox[\(E\), \(k\ \[Gamma]\ \[Epsilon]\ \[HBar]\)])\)\)]\)],
Subscript[\!\(\*OverscriptBox[\(R\), \(_\)]\), i,j]=CF@\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({} \[Rule] {i, j}\)]\)[-\[HBar] Subscript[a, j] Subscript[b, i],-\[HBar] Subscript[x, j] Subscript[y, i]/Subscript[B, i],1+If[$k==0, 0,Subscript[(\!\(\*SubscriptBox[
OverscriptBox[\(R\), \(_\)], \({i, j}, $k - 1\)]\)), $k][3]-
((Subscript[(\!\(\*SubscriptBox[
OverscriptBox[\(R\), \(_\)], \({i, j}, 0\)]\)), $k] Subscript[R, 1,2] Subscript[(\!\(\*SubscriptBox[
OverscriptBox[\(R\), \(_\)], \({3, 4}, $k - 1\)]\)), $k])//(Subscript[bm, i,1->i] Subscript[am, j,2->j])//(Subscript[bm, i,3->i] Subscript[am, j,4->j]))[3]]],
Subscript[P, i,j]=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i, j} \[Rule] {}\)]\)[Subscript[\[Beta], j]Subscript[\[Alpha], i]/\[HBar],Subscript[\[Eta], j]Subscript[\[Xi], i]/\[HBar],1+If[$k==0,0,Subscript[(\!\(\*SubscriptBox[\(P\), \({i, j}, $k - 1\)]\)), $k][3]-
(Subscript[R, 1,2]//(Subscript[(\!\(\*SubscriptBox[\(P\), \({i, 1}, 0\)]\)), $k] Subscript[(\!\(\*SubscriptBox[\(P\), \({2, j}, $k - 1\)]\)), $k]))[3]]]]


(* ::Input::Initialization:: *)
Define[Subscript[aS, i]=(Subscript[a\[Sigma], i->2] Subscript[\!\(\*OverscriptBox[\(R\), \(_\)]\), 1,i])//Subscript[P, 2,1],
Subscript[\!\(\*OverscriptBox[\(aS\), \(_\)]\), i]=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i} \[Rule] {i}\)]\)[-Subscript[a, i] Subscript[\[Alpha], i],-Subscript[x, i] Subscript[\[ScriptCapitalA], i] Subscript[\[Xi], i],1+If[$k==0, 0,Subscript[(\!\(\*SubscriptBox[
OverscriptBox[\(aS\), \(_\)], \({i}, $k - 1\)]\)), $k][3]-
(Subscript[(\!\(\*SubscriptBox[
OverscriptBox[\(aS\), \(_\)], \({i}, 0\)]\)), $k]//Subscript[aS, i]//Subscript[(\!\(\*SubscriptBox[
OverscriptBox[\(aS\), \(_\)], \({i}, $k - 1\)]\)), $k])[3]]]]


(* ::Input::Initialization:: *)
Define[Subscript[bS, i]=Subscript[b\[Sigma], i->1] Subscript[R, i,2]//Subscript[aS, 2]//Subscript[P, 2,1],
Subscript[\!\(\*OverscriptBox[\(bS\), \(_\)]\), i]=Subscript[b\[Sigma], i->1] Subscript[R, i,2]//Subscript[\!\(\*OverscriptBox[\(aS\), \(_\)]\), 2]//Subscript[P, 2,1],
Subscript[a\[CapitalDelta], i->j,k]=(Subscript[R, 1,j] Subscript[R, 2,k])//Subscript[bm, 1,2->3]//Subscript[P, i,3],
Subscript[b\[CapitalDelta], i->j,k]=(Subscript[R, j,1] Subscript[R, k,2])//Subscript[am, 1,2->3]//Subscript[P, 3,i]]


(* ::Input::Initialization:: *)
Define[Subscript[dm, i,j->k]=((Subscript[s\[CapitalUpsilon], i->4,4,1,1]//Subscript[a\[CapitalDelta], 1->1,2]//Subscript[a\[CapitalDelta], 2->2,3]//Subscript[\!\(\*OverscriptBox[\(aS\), \(_\)]\), 3])(Subscript[s\[CapitalUpsilon], j->-1,-1,-4,-4]//Subscript[b\[CapitalDelta], -1->-1,-2]//Subscript[b\[CapitalDelta], -2->-2,-3]))//(Subscript[P, 1,-3] Subscript[P, 3,-1] Subscript[am, 2,-4->k] Subscript[bm, 4,-2->k])]


(* ::Input::Initialization:: *)
Define[Subscript[d\[Sigma], i->j]=Subscript[a\[Sigma], i->j] Subscript[b\[Sigma], i->j],
Subscript[d\[Epsilon], i]=Subscript[s\[Epsilon], i], Subscript[d\[Eta], i]=Subscript[s\[Eta], i],
Subscript[dS, i]=Subscript[s\[CapitalUpsilon], i->1,1,2,2]//(Subscript[bS, 1] Subscript[\!\(\*OverscriptBox[\(aS\), \(_\)]\), 2])//Subscript[dm, 2,1->i],
Subscript[\!\(\*OverscriptBox[\(dS\), \(_\)]\), i]=Subscript[s\[CapitalUpsilon], i->1,1,2,2]//(Subscript[\!\(\*OverscriptBox[\(bS\), \(_\)]\), 1] Subscript[aS, 2])//Subscript[dm, 2,1->i],
Subscript[d\[CapitalDelta], i->j,k]=(Subscript[b\[CapitalDelta], i->1,3] Subscript[a\[CapitalDelta], i->4,2])//(Subscript[dm, 3,4->k] Subscript[dm, 1,2->j])]


(* ::Input::Initialization:: *)
Define[Subscript[C, i]=Subscript[\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({} \[Rule] {i}\)]\)[0,0,\!\(
\*SubsuperscriptBox[\(B\), \(i\), \(1/2\)] 
\*SuperscriptBox[\(E\), \(\(-\[HBar]\)\ \[Epsilon]\ 
\*SubscriptBox[\(a\), \(i\)]/2\)]\)], $k],
Subscript[\!\(\*OverscriptBox[\(C\), \(_\)]\), i]=Subscript[\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({} \[Rule] {i}\)]\)[0,0,\!\(
\*SubsuperscriptBox[\(B\), \(i\), \(\(-1\)/2\)] 
\*SuperscriptBox[\(E\), \(\[HBar]\ \[Epsilon]\ 
\*SubscriptBox[\(a\), \(i\)]/2\)]\)], $k],
Subscript[c, i]=Subscript[\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({} \[Rule] {i}\)]\)[0,0,\!\(
\*SubsuperscriptBox[\(B\), \(i\), \(1/4\)] 
\*SuperscriptBox[\(E\), \(\(-\[HBar]\)\ \[Epsilon]\ 
\*SubscriptBox[\(a\), \(i\)]/4\)]\)], $k],
Subscript[\!\(\*OverscriptBox[\(c\), \(_\)]\), i]=Subscript[\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({} \[Rule] {i}\)]\)[0,0,\!\(
\*SubsuperscriptBox[\(B\), \(i\), \(\(-1\)/4\)] 
\*SuperscriptBox[\(E\), \(\[HBar]\ \[Epsilon]\ 
\*SubscriptBox[\(a\), \(i\)]/4\)]\)], $k],
Subscript[Kink, i] = (Subscript[R, 1,3] Subscript[\!\(\*OverscriptBox[\(C\), \(_\)]\), 2])//Subscript[dm, 1,2->1]//Subscript[dm, 1,3->i],
Subscript[\!\(\*OverscriptBox[\(Kink\), \(_\)]\), i] = (Subscript[\!\(\*OverscriptBox[\(R\), \(_\)]\), 1,3] Subscript[C, 2])//Subscript[dm, 1,2->1]//Subscript[dm, 1,3->i],
Subscript[\[Rho], i]=(Subscript[c, 1] Subscript[\!\(\*OverscriptBox[\(c\), \(_\)]\), 3] Subscript[dS, i])//Subscript[dm, 1,i->i]//Subscript[dm, i,3->i]](*\[Rho] reverses a strand*)


(* ::Input::Initialization:: *)
Define[Subscript[b2t, i]=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i} \[Rule] {i}\)]\)[Subscript[\[Alpha], i] Subscript[a, i]+Subscript[\[Beta], i](\[Epsilon] Subscript[a, i]+Subscript[t, i])/\[Gamma]+Subscript[\[Xi], i] Subscript[x, i]+Subscript[\[Eta], i] Subscript[y, i]],
Subscript[t2b, i]=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i} \[Rule] {i}\)]\)[Subscript[\[Alpha], i] Subscript[a, i]+Subscript[\[Tau], i](-\[Epsilon] Subscript[a, i]+\[Gamma] Subscript[b, i])+Subscript[\[Xi], i] Subscript[x, i]+Subscript[\[Eta], i] Subscript[y, i]]]


(* ::Input::Initialization:: *)
Define[Subscript[kR, i,j]=Subscript[R, i,j]//(Subscript[b2t, i] Subscript[b2t, j]) /. Subscript[t, i|j]->t,
Subscript[\!\(\*OverscriptBox[\(kR\), \(_\)]\), i,j]=Subscript[\!\(\*OverscriptBox[\(R\), \(_\)]\), i,j]//(Subscript[b2t, i] Subscript[b2t, j]) /. {Subscript[t, i|j]->t,Subscript[T, i|j]->T},
Subscript[km, i,j->k]=((Subscript[t2b, i] Subscript[t2b, j])//Subscript[dm, i,j->k]//Subscript[b2t, k] )/. {Subscript[t, k]->t, Subscript[T, k]->T,Subscript[\[Tau], i|j]->0},
Subscript[kC, i]=(Subscript[C, i]//Subscript[b2t, i] )/. Subscript[T, i]->T,
Subscript[\!\(\*OverscriptBox[\(kC\), \(_\)]\), i]=(Subscript[\!\(\*OverscriptBox[\(C\), \(_\)]\), i]//Subscript[b2t, i] )/. Subscript[T, i]->T,
Subscript[kKink, i]=Subscript[Kink, i]//Subscript[b2t, i] /. {Subscript[t, i]->t, Subscript[T, i]->T},
Subscript[\!\(\*OverscriptBox[\(kKink\), \(_\)]\), i]=Subscript[\!\(\*OverscriptBox[\(Kink\), \(_\)]\), i]//Subscript[b2t, i] /. {Subscript[t, i]->t, Subscript[T, i]->T}]


(* ::Input::Initialization:: *)
Define[Subscript[tm, i,j->k]=Subscript[t2b, i]//Subscript[t2b, j]//Subscript[dm, i,j->k]//Subscript[b2t, k]]
Define[Subscript[t\[CapitalDelta], i->j,k]=Subscript[t2b, i]//Subscript[d\[CapitalDelta], i->j,k]//Subscript[b2t, j]//Subscript[b2t, k]]
Define[Subscript[tS, i]=Subscript[t2b, i]//Subscript[dS, i]//Subscript[b2t, i]]
Define[Subscript[\!\(\*OverscriptBox[\(tS\), \(_\)]\), i]=Subscript[t2b, i]//Subscript[\!\(\*OverscriptBox[\(dS\), \(_\)]\), i]//Subscript[b2t, i]]
Define[Subscript[tR, i,j]=Subscript[R, i,j]//Subscript[b2t, i]//Subscript[b2t, j],Subscript[\!\(\*OverscriptBox[\(tR\), \(_\)]\), i,j]=Subscript[\!\(\*OverscriptBox[\(R\), \(_\)]\), i,j]//Subscript[b2t, i]//Subscript[b2t, j]]
Define[Subscript[tC, i]=Subscript[C, i]//Subscript[b2t, i] ,Subscript[\!\(\*OverscriptBox[\(tC\), \(_\)]\), i]=Subscript[\!\(\*OverscriptBox[\(C\), \(_\)]\), i]//Subscript[b2t, i] ]
Define[Subscript[tKink, i]=Subscript[Kink, i]//Subscript[b2t, i] ,Subscript[\!\(\*OverscriptBox[\(tKink\), \(_\)]\), i]=Subscript[\!\(\*OverscriptBox[\(Kink\), \(_\)]\), i]//Subscript[b2t, i]]
Define[Subscript[tBS, i,j->k]=Subscript[tC, 3] Subscript[tC, 4] Subscript[t\[CapitalDelta], i->r1,l1] Subscript[t\[CapitalDelta], j->r2,l2]//Subscript[\!\(\*OverscriptBox[\(tS\), \(_\)]\), r1]//Subscript[tS, r2]//Subscript[tm, l1,r2->k]//Subscript[tm, k,3->k]//Subscript[tm, k,4->k]//Subscript[tm, k,r1->k]//Subscript[tm, k,l2->k]]


(* ::Input::Initialization:: *)
RVK::usage="RVK[xs, rots] represents a Rotational Virtual Knot with a list of n Xp/Xm crossings xs and a length 2n list of rotation numbers rots. Crossing sites are indexed 1 through 2n, and rots\[LeftDoubleBracket]k\[RightDoubleBracket] is the rotation between site k-1 and site k. RVK is also a casting operator converting to the RVK presentation from other knot presentations.";


(* ::Input::Initialization:: *)
RVK[pd_PD]:=Module[{n,xs,x,rots,front={0},k},
n=Length@pd;rots=Table[0,{2n}];
xs=Cases[pd,x_X:>\[Piecewise]{
 {Xp[x[[4]],x[[1]]], PositiveQ@x},
 {Xm[x[[2]],x[[1]]], True}
}];
For[k=0,k<2n,++k,If[k==0\[Or]FreeQ[front,-k],
front=Flatten@Replace[front,k->(xs/.{
Xp[k+1,l_]|Xm[l_,k+1]:>{l,k+1,1-l},
Xp[l_,k+1]|Xm[k+1,l_]:>(++rots[[l]];{1-l,k+1,l}),
_Xp|_Xm:>{}
}), {1}],
Cases[front,k|-k]/.{k,-k}:>--rots[[k+1]];
]];
RVK[xs,rots] ];
RVK[K_]:=RVK[PD[K]];


(* ::Input::Initialization:: *)
rot[i_,0]:=\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({} \[Rule] {i}\)]\)[0,0,1];
rot[i_,n_]:=rot[i,n,$k];
rot[i_,n_,k_]:=Module[{j},
rot[i,n,k]=If[n>0,rot[i,n-1]Subscript[kC, j],rot[i,n+1]Subscript[\!\(\*OverscriptBox[\(kC\), \(_\)]\), j]]//Subscript[km, i,j->i]];


(* ::Input::Initialization:: *)
Width[pd_PD]:=Max[Length/@FoldList[Complement[#1\[Union]#2,#1\[Intersection]#2]&, {}, List@@List@@@pd]]


(* ::Input::Initialization:: *)
ThinPosition[K_]:=Module[{todo,done,pd,c},
todo=List@@PD@K; done={}; pd=PD[];
While[todo=!={},
AppendTo[pd,c=RandomChoice@MaximalBy[todo, Length[done\[Intersection]List@@#]&]];
todo=DeleteCases[todo, c];
done=done\[Union]List@@c];
pd ];
ThinPosition[K_,n_] := First@MinimalBy[Table[ThinPosition[K], n], Width];


(* ::Input::Initialization:: *)
Z[K_] := Z[RVK@EchoFunction[Width]@ThinPosition[K,100]];
Z[rvk_RVK] := Monitor[ Module[{\[Zeta],done,st,c, \[Chi],i,j,k},
\[Zeta]=1; done={}; st=Range[2Length[rvk[[1]]]]; $M={};
Do[AppendTo[$M,c];
{i,j}=List@@c;
\[Chi]=(c/.{_Xp:>Subscript[kR, i,j] Subscript[\!\(\*OverscriptBox[\(kKink\), \(_\)]\), 0],_Xm:>Subscript[\!\(\*OverscriptBox[\(kR\), \(_\)]\), i,j] Subscript[kKink, 0]})//Subscript[km, j,0->j];
Do[\[Chi]=(rot[0,rvk[[2,k]]]\[Chi])//Subscript[km, 0,k->k], {k,{i,j}}];
\[Zeta]*=\[Chi];
Do[
If[MemberQ[done, k+1],\[Zeta]=\[Zeta]//Subscript[km, k,k+1->k]; st=st/.k+1->k];
If[MemberQ[done, k-1],\[Zeta]=\[Zeta]//Subscript[km, st[[k-1]],k->st[[k-1]]]; st=st/.k->st[[k-1]]],
{k,{i,j}}];
done=done\[Union]{i,j},
{c,rvk[[1]]}
];
CF/@ (\[Zeta] /. {Subscript[x, 1]->x,Subscript[y, 1]->y,Subscript[a, 1]->a})
], {Length@$M,$M}]
Subscript[\[Rho], 1][K_]:=Coefficient[Alexander[K][T]^3 (-T)/(T-1)^2 Z[K][[3]]/.{a->-1/2,x->0},\[Epsilon]]//Together//Expand



