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



(* ::Input::Initialization:: *)


Permute\[DoubleStruckCapitalE][GDO_][perm_]:= Module[
	{
		indices=getIndices[GDO],
		replacementRules,
		subscriptReplacementRules,
		is=getDomain[GDO],
		js=getCodomain[GDO],
		Q=getSeries[GDO],
		is2,js2,Q2
	},
	replacementRules=Thread[indices->Permute[indices,perm]];
	subscriptReplacementRules = Thread[isolateSubscripts[replacementRules]];
	is2=is/.replacementRules;
	js2=js/.replacementRules;
	Q2=Q/.subscriptReplacementRules;
	Subscript[\[DoubleStruckCapitalE], is2->js2]@@Q2
]


(* ::Code::Initialization:: *)
ReindexThenGetPermutations[GDO_] := Module[
	{
		R = Reindex\[DoubleStruckCapitalE][GDO],
		indices,
		replacementRules,
		subscriptReplacementRules
	},
	indices = getIndices[R];
	Permutations[indices]
]

ReindexThenPermuteAll[GDO_] := Permute\[DoubleStruckCapitalE][Reindex\[DoubleStruckCapitalE][GDO]]/@ReindexThenGetPermutations[GDO]


EquivalentQ[G1s_List,G2s_List]:=Module[
	{
		G1sSorted = SortBy[getPLength]@G1s,
		G2sSorted = SortBy[getPLength]@G2s,
		perms = ReindexThenGetPermutations[G1s[[1]]]
	},
	Echo@(getPLength/@G1sSorted == getPLength/@G1sSorted) &&
	Echo@(Length/@getDomain[#]&/@G1sSorted == Length/@getDomain[#]&/@G2sSorted) &&
	Echo@(Length/@getCodomain[#]&/@G1sSorted == Length/@getCodomain[#]&/@G2sSorted) &&
	Or@@Table[(Permute\[DoubleStruckCapitalE][#][p]&@G1sSorted)==G2sSorted,{p,perms}]
]
EquivalentQ[G1_,G2_]:=
	Length/@getDomain[G1] == Length/@getDomain[G2] && (* When domain is a list of lists, ensure these are the same *)
	Length/@getCodomain[G1] == Length/@getCodomain[G2] &&
	getPLength@G1 == getPLength@G2 &&
	MemberQ[ReindexThenPermuteAll[G1],Reindex\[DoubleStruckCapitalE][G2]]
