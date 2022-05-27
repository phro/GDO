testDeg=1;
BeginTestSection["GDO"];

(* A-algebra testing *)
Block[{$k=testDeg},
VerificationTest[
  Subscript[a\[CapitalDelta], 1->2,3]//Subscript[a\[CapitalDelta], 2->1,2],
  Subscript[a\[CapitalDelta], 1->1,2]//Subscript[a\[CapitalDelta], 2->2,3],
TestID->"a Coassociativity"]
]
Block[{$k=testDeg},
VerificationTest[
  Subscript[a\[CapitalDelta], i->1,2] Subscript[a\[CapitalDelta], j->3,4]//Subscript[am, 1,3->i]//Subscript[am, 2,4->j],
  Subscript[am, i,j->k]//Subscript[a\[CapitalDelta], k->i,j],
TestID->"a Algebra morphism"]
]
Block[{$k=testDeg},
VerificationTest[
  Subscript[am, 2,3->k]//Subscript[am, 1,k->k],
  Subscript[am, 1,2->k]//Subscript[am, k,3->k],
TestID->"a Associativity"]
]

Block[{$k=testDeg},
VerificationTest[
  Normal@(Subscript[a\[CapitalDelta], i->1,2]//Subscript[aS, 1]//Subscript[am, 1,2->1]),
  \!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i} \[Rule] {1}\)]\)[0,0,1],
TestID->"a Antipode L"]
]
Block[{$k=testDeg},
VerificationTest[
  Normal@(Subscript[a\[CapitalDelta], i->1,2]//Subscript[aS, 2]//Subscript[bm, 1,2->1]),
  \!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i} \[Rule] {1}\)]\)[0,0,1],
TestID->"a Antipode R"]
]

(* B-algebra testing *)
Block[{$k=testDeg},
VerificationTest[
  Subscript[b\[CapitalDelta], 1->2,3]//Subscript[b\[CapitalDelta], 2->1,2],
  Subscript[b\[CapitalDelta], 1->1,2]//Subscript[b\[CapitalDelta], 2->2,3],
TestID->"b Coassociativity"]
]
Block[{$k=testDeg},
VerificationTest[
  Subscript[b\[CapitalDelta], i->1,2] Subscript[b\[CapitalDelta], j->3,4]//Subscript[bm, 1,3->i]//Subscript[bm, 2,4->j],
  Subscript[bm, i,j->k]//Subscript[b\[CapitalDelta], k->i,j],
TestID->"b Algebra morphism"]
]
Block[{$k=testDeg},
VerificationTest[
  Subscript[bm, 2,3->k]//Subscript[bm, 1,k->k],
  Subscript[bm, 1,2->k]//Subscript[bm, k,3->k],
TestID->"b Associativity"]

]
Block[{$k=testDeg},
VerificationTest[
  Normal@(Subscript[b\[CapitalDelta], i->1,2]//Subscript[bS, 1]//Subscript[bm, 1,2->1]),
  \!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i} \[Rule] {1}\)]\)[0,0,1],
TestID->"b Antipode L"]
]
Block[{$k=testDeg},
VerificationTest[
  Normal@(Subscript[b\[CapitalDelta], i->1,2]//Subscript[bS, 2]//Subscript[bm, 1,2->1]),
  \!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i} \[Rule] {1}\)]\)[0,0,1],
TestID->"b Antipode R"]
]

(* CU-algebra testing *)
Block[{$k=testDeg},
VerificationTest[
  Subscript[c\[CapitalDelta], 1->2,3]//Subscript[c\[CapitalDelta], 2->1,2],
  Subscript[c\[CapitalDelta], 1->1,2]//Subscript[c\[CapitalDelta], 2->2,3],
TestID->"c Coassociativity"]
]
Block[{$k=testDeg},
VerificationTest[
  Subscript[c\[CapitalDelta], i->1,2] Subscript[c\[CapitalDelta], j->3,4]//Subscript[cm, 1,3->i]//Subscript[cm, 2,4->j],
  Subscript[cm, i,j->k]//Subscript[c\[CapitalDelta], k->i,j],
TestID->"c Algebra morphism"]
]
Block[{$k=testDeg},
VerificationTest[
  Subscript[cm, 2,3->k]//Subscript[cm, 1,k->k],
  Subscript[cm, 1,2->k]//Subscript[cm, k,3->k],
TestID->"c Associativity"]

]
Block[{$k=testDeg},
VerificationTest[
  Normal@(Subscript[c\[CapitalDelta], i->1,2]//Subscript[cS, 1]//Subscript[cm, 1,2->1]),
  \!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i} \[Rule] {1}\)]\)[0,0,1],
TestID->"c Antipode L"]
]
Block[{$k=testDeg},
VerificationTest[
  Normal@(Subscript[c\[CapitalDelta], i->1,2]//Subscript[cS, 2]//Subscript[cm, 1,2->1]),
  \!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i} \[Rule] {1}\)]\)[0,0,1],
TestID->"c Antipode R"]
]

(* QU-algebra testing *)
Block[{$k=testDeg},
VerificationTest[
	Subscript[d\[CapitalDelta], 1->2,3]//Subscript[d\[CapitalDelta], 2->1,2],
	Subscript[d\[CapitalDelta], 1->1,2]//Subscript[d\[CapitalDelta], 2->2,3],
TestID->"d Coassociativity"]
]
Block[{$k=testDeg},
VerificationTest[
	Subscript[d\[CapitalDelta], i->1,2] Subscript[d\[CapitalDelta], j->3,4]//Subscript[dm, 1,3->i]//Subscript[dm, 2,4->j],
	Subscript[dm, i,j->k]//Subscript[d\[CapitalDelta], k->i,j],
TestID->"d Algebra morphism"]
]
Block[{$k=testDeg},
VerificationTest[
	Subscript[dm, 2,3->k]//Subscript[dm, 1,k->k],
	Subscript[dm, 1,2->k]//Subscript[dm, k,3->k],
TestID->"d Associativity"]

]
Block[{$k=testDeg},
VerificationTest[
	Normal@(Subscript[d\[CapitalDelta], i->1,2]//Subscript[dS, 1]//Subscript[dm, 1,2->1]),
	\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i} \[Rule] {1}\)]\)[0,0,1],
TestID->"d Antipode L"]
]
Block[{$k=testDeg},
VerificationTest[
	Normal@(Subscript[d\[CapitalDelta], i->1,2]//Subscript[dS, 2]//Subscript[dm, 1,2->1]),
	\!\(\*SubscriptBox[\(\[DoubleStruckCapitalE]\), \({i} \[Rule] {1}\)]\)[0,0,1],
TestID->"d Antipode R"]

]
Block[{$k=testDeg},
VerificationTest[
	Subscript[R, 1,3]//Subscript[d\[CapitalDelta], 1->1,2],
	Subscript[R, 1,3] Subscript[R, 2,4]//Subscript[dm, 3,4->3],
TestID->"d Quasitriangular 1"]
]
Block[{$k=testDeg},
VerificationTest[
	Subscript[R, 1,3]//Subscript[d\[CapitalDelta], 3->2,3],
	Subscript[R, 1,3] Subscript[R, 0,2]//Subscript[dm, 1,0->1],
TestID->"d Quasitriangular 2"]
]
Block[{$k=testDeg},
VerificationTest[
	Subscript[d\[CapitalDelta], i->k,j] Subscript[R, 1,2]//Subscript[dm, j,1->1]//Subscript[dm, k,2->2],
	Subscript[R, 1,2] Subscript[d\[CapitalDelta], i->j,k]//Subscript[dm, 1,j->1]//Subscript[dm, 2,k->2],
TestID->"d Quasitriangular 3"]

]
Block[{$k=testDeg},
VerificationTest[
	Subscript[R, 1,2]//Subscript[aS, 2],
	Subscript[\!\(\*OverscriptBox[\(R\), \(_\)]\), 1,2],
TestID->"d R-matrix inverse"]
]
EndTestSection[];
