Get["~/ed/gdo/StandardVersion.m"]
Get["~/ed/gdo/newVersion.m"];
Get["~/ed/gdo/RVT.m"]

pg1 = toPG[Subscript[a, 1],Subscript[x, 1],1 + \[Epsilon] + O[\[Epsilon]]^3]; 
pg2 = toPG[Subscript[b, 1],Subscript[y, 1],-1 + 2\[Epsilon] + O[\[Epsilon]]^3];


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
VerificationTest[
        QZip[{\[Xi][i]}][toPG[a[i],\[Mu] \[Xi][i]x[i],1]]
,
        fromE@Subscript[QZipOld, {Subscript[\[Xi], i]}][\[DoubleStruckCapitalE][Subscript[a, i],\[Mu] Subscript[\[Xi], i] Subscript[x, i],1]]
,
{TestID->"New QZip matches old QZip.",SameTest->Congruent}]
VerificationTest[
        LZip[{\[Xi][i]}][toPG[a[i]b[i] + \[Lambda] b[i],\[Mu] \[Xi][i]x[i],b[i]^2]]
,
        fromE@Subscript[LZipOld, {Subscript[\[Xi], i]}][\[DoubleStruckCapitalE][Subscript[a, i] Subscript[b, i] + \[Lambda] Subscript[b, i],\[Mu] Subscript[\[Xi], i] Subscript[x, i],Subscript[b, i]^2]]
,
{TestID->"New LZip matches old LZip.",SameTest->Congruent}]
VerificationTest[
        Pair[{i}][toPG[a[i],x[i],b[i]^2],toPG[\[Mu] \[Alpha][i]+ c \[Beta][i], \[Lambda] \[Xi][i],1]]
,
        fromE@Subscript[B, {i}][\[DoubleStruckCapitalE][Subscript[a, i],Subscript[x, i],Subscript[b, i]^2],\[DoubleStruckCapitalE][\[Mu] Subscript[\[Alpha], i]+ c Subscript[\[Beta], i], \[Lambda] Subscript[\[Xi], i],1]]
,
{TestID->"Pair behaves the same as Subscript[B, _]",SameTest->Congruent}]
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
