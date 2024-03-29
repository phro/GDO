(* Get["~/ed/gdo/StandardVersion.m"] *)
(* Get["coverage/newVersion.m"]; *)
(* Get["coverage/RVT.m"] *)

pg1 = toPG[Subscript[a, 1],Subscript[x, 1],1 + \[Epsilon] + O[\[Epsilon]]^3]; 
pg2 = toPG[Subscript[b, 1],Subscript[y, 1],-1 + 2\[Epsilon] + O[\[Epsilon]]^3];

(* Getters and Setters *)
VerificationTest[
        getL@pg1
,
        Subscript[a, 1]
,
{TestID->"getL extracts L part of PG"}]
VerificationTest[
        getL@PG@<||>
,
        0
,
{TestID->"getL returns defualt value of 0 on PG"}]
VerificationTest[
        getQ@PG@<||>
,
        0
,
{TestID->"getQ returns defualt value of 0 on PG"}]
VerificationTest[
        getP@PG@<||>
,
        1
,
{TestID->"getP returns defualt value of 1 on PG"}]
VerificationTest[
        getQ@pg1
,
        Subscript[x, 1]
,
{TestID->"getQ extracts Q part of PG"}]
VerificationTest[
        getP@pg1
,
        1 + \[Epsilon] + O[\[Epsilon]]^3
,
{TestID->"getP extracts P part of PG"}]
VerificationTest[
        setL[Subscript[a, 1] Subscript[b, 1]]@pg1
,
        toPG[Subscript[a, 1] Subscript[b, 1],Subscript[x, 1],1 + \[Epsilon] + O[\[Epsilon]]^3]
,
{TestID->"setL sets L part of PG"}]
VerificationTest[
        setQ[Subscript[x, 1] Subscript[y, 1]]@pg1
,
        toPG[Subscript[a, 1],Subscript[x, 1] Subscript[y, 1],1 + \[Epsilon] + O[\[Epsilon]]^3]
,
{TestID->"setQ sets Q part of PG"}]
VerificationTest[
        setP[1]@pg1
,
        toPG[Subscript[a, 1],Subscript[x, 1],1]
,
{TestID->"setP sets P part of PG"}]
VerificationTest[
        pg1 pg2
,
        toPG[Subscript[a, 1]+Subscript[b, 1],Subscript[x, 1]+Subscript[y, 1],-1 + \[Epsilon] + 2\[Epsilon]^2 +O[\[Epsilon]]^3]
,
{TestID->"multiplication of PG's behaves properly"}]

(* Algebraic axioms *)

(** meta-monoid axioms **)
VerificationTest[
        cm[1,2,1]//cm[1,3,1],
        cm[2,3,2]//cm[1,2,1],
{TestID->"mult",SameTest->Congruent}]

VerificationTest[
        cη[1]//cη[2]//cm[1,2,1],
        cη[1],
{TestID->"unit 1",SameTest->Congruent}]

VerificationTest[
        cη[1]//cη[2]//cm[2,1,1],
        cη[1],
{TestID->"unit 2",SameTest->Congruent}]

(** meta-comonoid axioms **)
VerificationTest[
        cΔ[1,1,2]//cΔ[2,2,3],
        cΔ[1,1,3]//cΔ[1,1,2],
{TestID->"comult",SameTest->Congruent}]

VerificationTest[
        cη[1]//cΔ[1,1,2]//cϵ[2],
        cη[1],
{TestID->"counit 1",SameTest->Congruent}]

VerificationTest[
        cη[1]//cΔ[1,2,1]//cϵ[2],
        cη[1],
{TestID->"counit 2",SameTest->Congruent}]

(** meta-bimonoid axoims **)
VerificationTest[
        cΔ[1,1,3]//cΔ[2,2,4]//cm[1,2,1]//cm[3,4,2],
        cm[1,2,1]//cΔ[1,1,2],
TestID->"mult comult",SameTest->Congruent]

VerificationTest[
        cη[1]cη[2]//cm[1,2,1]//cϵ[1],
        cη[1]cη[2]//cϵ[1]//cϵ[2],
TestID->"mult counit",SameTest->Congruent]

VerificationTest[
        cη[1]//cΔ[1,1,2],
        cη[1]cη[2],
TestID->"comult unit",SameTest->Congruent]

VerificationTest[
        cη[2]cη[1]//cϵ[1],
        cη[2],
TestID->"unit counit",SameTest->Congruent]

(** meta-Hopf monoid axioms **)
VerificationTest[
        cη[1]//cϵ[1]//cη[1],
        cΔ[1,1,2]//cS[1]//cm[1,2,1],
TestID->"antipode 1",SameTest->Congruent]

VerificationTest[
        cη[1]//cϵ[1]//cη[1],
        cΔ[1,1,2]//cS[2]//cm[1,2,1],
TestID->"antipode 2",SameTest->Congruent]


(* Reidemeister moves *)
VerificationTest[
        Module[{k},cR[k,i]CC[k]//cm[i,k,i]]
,
        cKink[i]
,
{TestID->"Reidemeister 1' for classical algebra (positive)"}]
VerificationTest[
        Module[{k},cRi[k,i]CCi[k]//cm[i,k,i]]
,
        cKinki[i]
,
{TestID->"Reidemeister 1' for classical algebra (negative)"}]
VerificationTest[
        cR[4,1]cRi[3,2]CC[2]//cm[1,2,1]//cm[3,4,2]
,
        CC[1]c\[Eta][2]
,
{TestID->"Reidemeister 2 for classical algebra (i)"}]
VerificationTest[
        cRi[1,4]cR[2,3]CC[2]//cm[1,2,1]//cm[3,4,2]
,
        CC[1]c\[Eta][2]
,
{TestID->"Reidemeister 2 for classical algebra (ii)"}]
VerificationTest[
        Module[{k},uR[i,k] CCi[k]//cm[i,k,i]]
,
        c\[Eta][i]
,
{TestID->"R1 for writhe-corrected classical algebra (uR)",SameTest->Congruent}]
VerificationTest[
        Module[{k},uRi[i,k] CC[k]//cm[i,k,i]]
,
        c\[Eta][i]
,
{TestID->"R1 for writhe-corrected classical algebra (uRi)",SameTest->Congruent}]

ugdo = GDO["co"->{1,2},"PG"->PG["L"->a[1]b[1] + a[1]b[2] -3a[2]b[2]]]
VerificationTest[
        Unwrithe@ugdo,
        ugdo//cKinkn[-1][3]//cKinkn[3][4]//cm[1,3,1]//cm[2,4,2],
        {TestID->"ugdo test"}
]
VerificationTest[
        Z@RVT[{Strand[1,2]},{Xp[1,2]},<|2->-1|>]
,
        GDO["co"->{1}]
,
{SameTest->Congruent}]
VerificationTest[
        ZFramed@RVT[{Strand[1,3],Strand[2,4]},{Xm[1,4],Xp[3,2]},<|4->1|>],
        ZFramed@RVT[{Strand[1],Strand[2]},{},<|2->1|>],
        {TestID->"ZFramed R2"}
]
VerificationTest[
        cR[1,2]CC[pr1]CCi[po1]CC[pr2]CCi[po2]//
                cm[{pr1,1, po1},1]//
                cm[{pr2,2, po2},2]
,
        cR[1,2]
,
{TestID->"Positive CCW Whirl relation",SameTest->Congruent}]
VerificationTest[
        cR[1,2]CCi[pr1]CC[po1]CCi[pr2]CC[po2]//
                cm[{pr1,1, po1},1]//
                cm[{pr2,2, po2},2]
,
        cR[1,2]
,
{TestID->"Positive CW Whirl relation",SameTest->Congruent}]
VerificationTest[
        cRi[1,2]CC[pr1]CCi[po1]CC[pr2]CCi[po2]//
                cm[{pr1,1, po1},1]//
                cm[{pr2,2, po2},2]
,
        cRi[1,2]
,
{TestID->"Negative CCW Whirl relation",SameTest->Congruent}]
VerificationTest[
        cRi[1,2]CCi[pr1]CC[po1]CCi[pr2]CC[po2]//
                cm[{pr1,1, po1},1]//
                cm[{pr2,2, po2},2]
,
        cRi[1,2]
,
{TestID->"Negative CW Whirl relation",SameTest->Congruent}]
VerificationTest[
        CCi[1]CCi[2]cR[3,4]CC[5]CC[6]//cm[{1,3,5},i]//cm[{2,4,6},j]
,
        cR[i,j]
,
{SameTest->Congruent}]
VerificationTest[
Z@
RVT[{Strand[1,3],Loop[2,4,5,6]}
		,{Xm[1,5],Xp[6,2],Xm[4,3]}
		,<|5->1|>
	],
Z@
RVT[{Strand[1,3],Loop[2,4,5,6,7,8,9,10]}
		,{Xm[7,1],Xm[3,8],Xm[6,2],Xp[9,4],Xp[5,10]}
		,<|6->-1|>
	],
{TestID->"Z behaves appropriately on two Hopf links with differing writhe.",SameTest->Congruent}
]
VerificationTest[
        Z@RVT[
                {Strand[1,3],Strand[2,4,5,6]},
                {Xm[1,5],Xm[2,6],Xm[4,3]},
                <|5->1|>
        ],
        Z@RVT[
                {Strand[1,3],Strand[2,4,5,6]},
                {Xm[5,1],Xm[3,6],Xm[4,2]},
                <|4->-1|>
	],
{TestID->"Z behaves appropriately on a Hopf link with different rotation numbers."}
]
VerificationTest[
        Z@RVT[{Strand[1,3],Strand[2,4,5,6]}
        ,{Xm[3,6],Xm[2,1],Xm[4,5]}
                                ,<|5->1|>
        ],
        Z@RVT[{Strand[1,3],Strand[2,4,5,6]}
        ,{Xm[5,1],Xm[3,6],Xm[4,2]}
                                ,<|4->-1|>
        ],
{TestID->"Z behaves appropriately on a simpler Hopf link with different rotation numbers."}
]
VerificationTest[
        Z@RVT[
                {Strand[1],Strand[2,4,5]},
                {Xm[2,1],Xm[4,5]},
                <|5->1|>
        ],
        Z@RVT[
                {Strand[1],Strand[2,4,5]},
                {Xm[5,1],Xm[4,2]},
                <|4->-1|>
        ],
{TestID->"Z behaves appropriately on a xing with different rotation numbers."}
]
VerificationTest[
        ZFramed@RVT[{Strand[1,2]},{Xm[1,2]},<|2->1|>]
,
        ZFramed@RVT[{Strand[1,2]},{Xm[2,1]},<|2->-1|>]
,
{TestID->"R1' holds for ZFramed."}]
