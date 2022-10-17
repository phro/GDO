(*
 * Purpose:
 * Using the GDO package, define the trace operator. Currently, it is only defined
 * to a(n arbitrarily large) finite degree, with the intension of extending to a
 * general form if it is determined that this indeed defines an interesting
 * invariant.
 *)

$k = 0; \[Gamma] = 1;

$Assumptions = Element[_, Reals]

η[i_] := Subscript[η, i];
β[i_] := Subscript[β, i];
α[i_] := Subscript[α, i];
ξ[i_] := Subscript[ξ, i];
τ[i_] := Subscript[τ, i];
y[i_] := Subscript[y, i];
b[i_] := Subscript[b, i];
B[i_] := Subscript[B, i];
A[i_] := Subscript[\[ScriptCapitalA], i];
a[i_] := Subscript[a, i];
x[i_] := Subscript[x, i];
t[i_] := Subscript[t, i];
T[i_] := Subscript[T, i];

GDO::usage = "GDO[is -> js][Qs] is shorthand for Subscript[\[DoubleStruckCapitalE], is -> js][Qs]."
GDO[ijs___][Qs___] := Subscript[\[DoubleStruckCapitalE], ijs][Qs]

getDomain[GDO[is_->js_][L_,Q_,P_]]:=is;
getCodomain[GDO[is_->js_][L_,Q_,P_]]:=js;
getSeries[GDO[is_->js_][L_,Q_,P_]]:={L,Q,P};
getGDOIndices[gdo_]:=Union@Flatten@{getDomain[gdo],getCodomain[gdo]};
isolateSubscripts[a_->b_]:=Subscript[x_, a]->Subscript[x, b];
getPLength[gdo_] := Map[Length,ExpandAll[GDO],{1}][[3]];

getSkeleton[L_RVT] := L[[1]]
getXings[L_RVT]    := L[[2]]
getRotNums[L_RVT]  := L[[3]]
Component = Strand | Loop

cm[{}, j_] := Subscript[cη, j]
cm[{i_}, j_] := Subscript[cσ, i->j]
cm[{i_, j_}, k_] := Subscript[cm, i, j -> k]
cm[ii_List, k_] := Module[
        {
                i  = First[ii],
                is = Rest[ii],
                j  ,
                js ,
                l
        },
        j  = First[is];
        js = Rest[is];
        Subscript[cm, i, j-> l] // cm[Prepend[js, l], k]
]

toGDO[Xp[i_,j_]] := cR[i,j]
toGDO[Xm[i_,j_]] := cRi[i,j]
toGDO[{i_,n_}]   := CCn[i][n]
toGDO[xs_Strand] := cm[List@@xs, First[xs]]
toGDO[xs_Loop]   := Module[{x = First[xs]}, cm[List@@xs, x]//tr[x]]

toList[RVT[cs_List, xs_List, rs_List]] := Flatten[#,1]&@((toGDO/@#&)/@{xs,rs,cs})

getIndices[RVT[cs_List, _List, _List]] := Sort@Flatten[#,1]&@(List@@@cs)

ReindexBy[f_][gdo_] := Module[
        {
        replacementRules,
        subscriptReplacementRules,
        indices = getGDOIndices[gdo],
        is = getDomain[gdo],
        js = getCodomain[gdo],
        Q =  getSeries[gdo],
        is2,js2,Q2
        },
        replacementRules = Thread[indices->(f/@indices)];
        subscriptReplacementRules = Thread[isolateSubscripts[replacementRules]];
        is2 = is/.replacementRules;
        js2 = js/.replacementRules;
        Q2 = Q/.subscriptReplacementRules;
        GDO[is2->js2]@@Q2
]

Reindex\[DoubleStruckCapitalE][gdo_]:=Module[
        {
        replacementRules,
        subscriptReplacementRules,
        indices = getGDOIndices[gdo],
        is = getDomain[gdo],
        js = getCodomain[gdo],
        Q =  getSeries[gdo],
        is2,js2,Q2
        },
        replacementRules = Thread[indices->Range[Length[indices]]];
        subscriptReplacementRules = Thread[isolateSubscripts[replacementRules]];
        is2 = is/.replacementRules;
        js2 = js/.replacementRules;
        Q2 = Q/.subscriptReplacementRules;
        GDO[is2->js2]@@Q2
]

MatrixForm[GDO[{} -> ss_][L_,Q_,P_]] ^:=
  GDO[{} -> ss][
    MatrixForm[Table[Table[
      D[L,Subscript[a, i], Subscript[b, j]],
      {i,ss}],
      {j,ss}]
    ],
    MatrixForm[Table[Table[
      D[Q,Subscript[x, i], Subscript[y, j]]
      {i,ss}],
      {j,ss}]
    ],P
  ]


(*
 * Generic \[CurlyEpsilon]=0 elements of GDO
 *)
EtestScal[n_] := GDO[{} -> Range[n]][
  Sum[
    ħ Subscript[l, i,j] Subscript[b, i] Subscript[a, j],
    {i,1,n}, {j,1,n}
  ],
  Sum[
    ħ Subscript[q, i,j][ħ Subscript[b, i]]
    Subscript[y, i] Subscript[x, j],
    {i,1,n},{j,1,n}],
  1
]

Etest[n_] := GDO[{} -> Range[n]][
  Sum[
    ħ Subscript[l, i,j] Subscript[b, i] Subscript[a, j],
    {i,1,n}, {j,1,n}
  ],
  Sum[
    ħ Subscript[q, i,j] Subscript[y, i] Subscript[x, j],
    {i,1,n},{j,1,n}],
  1
]


coinv::usage = "coinv[i][f] gives the coinvarant of expression in sl2+ f with respect to variables indexed by i. It returns a finite sum of monomials when given a finite sum."
coinv[ii_][lincomb_Plus]:=coinv[ii]/@lincomb;
coinv[ii_][word_]:=Module[{
        i,j,k,l,λ,
        yii = Subscript[y, ii],
        bii = Subscript[b, ii],
        aii = Subscript[a, ii],
        xii = Subscript[x, ii],
        tii = Subscript[t, ii]
        },
        \[Lambda] = Total@Flatten@CoefficientList[word,{yii, bii, aii, xii}];
        {i,j,k,l}=Exponent[word,Subscript[#, ii]]&/@{y,b,a,x};
        If[i==l && j<=k,
                If[j==0,
                        λ i! aii^k tii^i,
                        coinv[ii]@Expand[
                                λ/(i+1) *
                                yii^(i + 1) * bii^(j-1) *
                                (aii^k-(aii-1)^k) * xii^(i+1)
                        ]
                ],
                0
        ]
]

trGenFunc::usage = "trGenFunc[m][i] generates the generating function for coinv[i] up to degree m, with (filtered) degree defined by giving weight 1 to each of y, b, a, and x."
trGenFunc[m_][ii_] := Module[{
        i,j,k,l,
        yii = Subscript[y, ii],
        bii = Subscript[b, ii],
        aii = Subscript[a, ii],
        xii = Subscript[x, ii],
        ηii = Subscript[η, ii],
        βii = Subscript[β, ii],
        αii = Subscript[α, ii],
        ξii = Subscript[ξ, ii]
        },
        Sum[
                coinv[ii][yii^i bii^j aii^k xii^l]
                (ηii^i βii^j αii^k ξii^l)/(i!j!k!l!),
        {i,0,m},{j,0,m-i},{k,0,m-i-j},{l,0,m-i-j-k}
        ]
]

trDeg::usage = "trDeg[m][i] is the component-i trace up to degree m as a GDO element."
trDeg[m_][ii_] := GDO[{{ii},{}} -> {{},{ii}}][0, 0, trGenFunc[m][ii]]//CF

trGuess::usage = "trGuess[i] is a placeholder guess for a GDO expression which represents a trace."
trGuess[i_] := GDO[{{i},{}}->{{},{i}}][
        α[i]a[i],η[i]ξ[i]t[i], Exp[β[i] (1-Exp[-α[i]])t[i]]
]

(* Coefficient-extraction functions *)

getConstCoef::usage = "getConstCoef[i][gdo] returns the terms in a GDO expression which are not a function of y[i], b[i], a[i], nor x[i]."
getConstCoef[i_][gdo_] :=
        (SeriesCoefficient[#, {b[i],0,0}]&) @*
        (Coefficient[#, y[i], 0]&) @*
        (Coefficient[#, a[i], 0]&) @*
        (Coefficient[#, x[i], 0]&) @
        ReplaceAll[U2l] @
        (gdo[1] + gdo[2] + Log[gdo[3]])

getyCoef::usage = "getyCoef[i][gdo][b[i]] returns the linear coefficient of y[i] as a function of b[i]."
getyCoef[i_][gdo_][bb_] :=
        ReplaceAll[{b[i]->bb}] @*
        ReplaceAll[U2l] @*
        (Coefficient[#, x[i],0]&) @*
        (Coefficient[#, y[i],1]&) @
        getSeries[gdo][[2]]

getbCoef::usage = "getbCoef[i][gdo] returns the linear coefficient of b[i]."
getbCoef[i_][gdo_] :=
        (SeriesCoefficient[#, {b[i],0,1}]&) @*
        (Coefficient[#, a[i],0]&) @*
        (Coefficient[#, x[i],0]&) @*
        (Coefficient[#, y[i],0]&) @*
        ReplaceAll[U2l] @
        (gdo[1] + gdo[2] + Log[gdo[3]])

getaCoef::usage = "getaCoef[i][gdo] returns the linear coefficient of a[i]."
getaCoef[i_][gdo_] :=
        (SeriesCoefficient[#, {b[i],0,0}]&) @*
        (Coefficient[#, a[i],1]&) @*
        ReplaceAll[U2l] @
        getSeries[gdo][[1]]

getxCoef::usage = "getxCoef[i][gdo][b[i]] returns the linear coefficient of x[i] as a function of b[i]."
getxCoef[i_][gdo_][bb_] :=
        ReplaceAll[{b[i]->bb}] @*
        ReplaceAll[U2l] @*
        (Coefficient[#, y[i],0]&) @*
        (Coefficient[#, x[i],1]&) @
        getSeries[gdo][[2]]

getabCoef::usage = "getabCoef[i][gdo] returns the linear coefficient of a[i]b[i]."
getabCoef[i_][gdo_] :=
        (SeriesCoefficient[#,{b[i],0,1}]&) @*
        (Coefficient[#,a[i],1]&) @*
        ReplaceAll[U2l] @
        getSeries[gdo][[1]]

getxyCoef::usage = "getxyCoef[i][gdo][b[i]] returns the linear coefficient of x[i]y[i] as a function of b[i]."
getxyCoef[i_][gdo_][bb_] :=
        ReplaceAll[{b[i]->bb}] @*
        ReplaceAll[U2l] @*
        (Coefficient[#,x[i],1]&) @*
        (Coefficient[#,y[i],1]&) @
        getSeries[gdo][[2]]

safeEval[f_][x_] := Module[{fx, x0},
        If[(fx=Quiet[f[x]]) === Indeterminate,
                Series[f[x0],x0 -> x]//Normal,
                fx
        ]
]

tr::usage = "tr[i] computes the trace of a GDO element on component i. Current implementation assumes the Subscript[a, i] Subscript[b, i] term vanishes and $k=0."
tr::nonzeroSigma = "tr[`1`]: Component `1` has writhe: `2`, expected: 0."
tr[i_][gdo_] := Module[
        {
                c = getConstCoef[i][gdo],
                ηη = getyCoef[i][gdo],
                ββ = getbCoef[i][gdo],
                αα = getaCoef[i][gdo],
                ξξ = getxCoef[i][gdo],
                λ = getxyCoef[i][gdo],
                ins  = toMixed@getDomain[gdo],
                outs = toMixed@getCodomain[gdo],
                ta,
                exponent
        },
        ta = (1-Exp[-αα]) t[i];
        exponent = safeEval[
                c + αα a[i] + ββ ta +
                t[i](ηη[#]ξξ[#])/(1-t[i] λ[#]) -
                Log[1-t[i] λ[#]]
                &
        ][ta];
        CF[GDO[ins -> closeComponent[i][outs]][exponent]//.l2U]
] /; Module[
        {σ = getabCoef[i][gdo]},
        If[σ == 0,
                True,
                Message[tr::nonzeroSigma, i, ToString[σ]]; False
        ]
]

(*
 * Convert a GDO series to a polynomial
 *)
(*  TODO: the following should only track the y- and the b- degrees: *)
ScaleBy::usage = "ScaleBy[λ][i] rescales all variables of a GDO expression in tensor factor i by a factor of λ."
ScaleBy[λ_][i_] := GDO[{i} -> {i}][
  \[Lambda] (
    Subscript[a, i] Subscript[\[Alpha], i] +
    Subscript[b, i] Subscript[\[Beta], i]),
  \[Lambda] (
    Subscript[y, i] Subscript[\[Eta], i] +
    Subscript[x, i] Subscript[\[Xi], i]),
  1
]

TruncateToDegree::usage = "TruncateToDegree[n][λ] takes a Taylor-expandable series and truncates it to λ-degree at most n."
TruncateToDegree[n_][λ_][f_] := Expand@Normal[Series[f,{λ,0,n}]]

GDOTruncateToDegree::usage = "GDOTruncateToDegree[n] takes a GDO element and writes it as a finite polynomial of degree at most n."
GDOTruncateToDegree[n_][gdo_]:=Module[
        {i,
        is = getDomain[gdo],
        js = getCodomain[gdo],
        scalerDomain,
        scalerCodomain,
        L, P, Q,
        λ, μ
        },
        scalerDomain = # -> λ # & /@
                Flatten[#, 1]&@(Thread /@ Map[#[Flatten@is]&, {η, β, α, ξ}]);
        scalerCodomain = # -> μ # & /@
                Flatten[#, 1]&@(Thread /@ Map[#[Flatten@js]&, {y, b, a, x, t}]);
        {L, Q, P} = getSeries[gdo/.U2l/.scalerDomain/.scalerCodomain];
        GDO[is->js][0, 0, (TruncateToDegree[n][μ]@*TruncateToDegree[n][λ])@
                ((Exp[L+Q]*P)//.U2l)
        ]/.{λ->1, μ->1}//CF
]

GDOToList[GDO[is_->js_][L_,Q_,P_]] := {is, js, L, Q, P};
GDOFromList[is_, js_, L_, Q_, P_] := GDO[is->js][L,Q,P]

(* Skeleton-Xing form *)
SXForm[L_SXForm]:=L
SXForm[L_] := SXForm[
  Skeleton[L],
  List@@PD[L] /. (X[i_,j_,k_,l_] :>
    If[PositiveQ[X[i,j,k,l]],Xp[l,i], Xm[j,i]])
];

getWritheOfXing[c:Component[__]][Xp[is__]] := If[SubsetQ[List@@c,{is}],1,0]
getWritheOfXing[c:Component[__]][Xm[is__]] := If[SubsetQ[List@@c,{is}],-1,0]
getWritheOfComponent[L_RVT][c:Component[__]] := Total[
        getWritheOfXing@c /@ getXings@L
]
Writhe[L_RVT] := getWritheOfComponent[L] /@ getSkeleton[L]
Writhe::badArg = "Writhe must be called with head RVT, called instead with head `1`"
Writhe[L_] := Message[Writhe::badArg, Head@L]

combineBySecond[l_List] := mergeWith[Total,#]& /@ GatherBy[l, First];
combineBySecond[lis___] := combineBySecond[Join[lis]]

mergeWith[f_, l_] := {l[[1, 1]], f@(#[[2]] & /@ l)}

(* Overloaded RVT as a typecaster should function on objects already in RVT form. *)
RVT::usage := ""
RVT::SXForm := "Conversion from SXForm not implemented in Mathematica™."
RVT[L_RVT] := L
RVT[L_SXForm] := Message[RVT::SXForm]

(*
 * Modify each component of a link diagram to have writhe=0
 * Properties:
 *  - Union@Writhe[Unwrithe[L]] = {0}
 *  - Unwrithe@*Unwrithe = Unwrithe (assuming properly indexed SXForm to begin)
 *)
Unwrithe[L_SXForm] := Module[{s, z, lw},
  {s, z} = List @@ L;
  (* Loops, together with their writhes *)
  lw = Table[{l,Plus@@z/.{
      Xp[i_,j_]:>If[MemberQ[l,i] \[And] MemberQ[l,j], 1,0],
      Xm[i_,j_]:>If[MemberQ[l,i] \[And] MemberQ[l,j],-1,0]
    }},{l,s}];
  (* Print["{(Loop,writhe)}: ",lw]; *)
  addLoops[l_,n_]:=Join[l, Head[l]@@Table[Subscript[Last[l], i],{i,2 Abs[n]}]];
  Xn[n_]:=If[n>=0,Xm,Xp]; (* Loops to counteract the writhe. *)
  addXings[l_,n_]:=If[n==0,
    {},
    Table[Xn[n][Subscript[Last[l],2 i -1], Subscript[Last[l], 2i]],{i,Abs[n]}]
    ];
  Reindex@SXForm[addLoops@@@lw,Join [z, Flatten[addXings@@@lw]]]
]
Unwrithe[RVT[cs_List, xs_List, rs_List]] := Module[{lw},
  lw = Table[{l, Plus@@xs/.{
      Xp[i_,j_] :> If[MemberQ[l,i] \[And] MemberQ[l,j], 1,0],
      Xm[i_,j_] :> If[MemberQ[l,i] \[And] MemberQ[l,j],-1,0]
    }},{l, cs}];
  addLoops[l_,n_]:=Join[l, Head[l]@@Table[Subscript[Last[l], i],{i,2 Abs[n]}]];
  Xn[n_]:=If[n>=0,Xm,Xp]; (* Loops to counteract the writhe. *)
  addXings[l_,n_]:=If[n==0,
    {},
    Table[Xn[n][Subscript[Last[l],2 i -1], Subscript[Last[l], 2i]],{i,Abs[n]}]
    ];
  addRots[l_,n_] := {First@l,n};
  (* Print["lw: ", lw]; *)
  Reindex@RVT[addLoops@@@lw,Join [xs, Flatten[addXings@@@lw]], combineBySecond[rs,addRots@@@lw]]
]
Unwrithe[L_] := Unwrithe[SXForm[L]]

(*
 * Modify the arc labels so that the SXForm contains consecutive integers starting
 * at 1.
 *
 * TODO: Maybe? modify so that `(First@*List)/@s` is a list of consecutive
 * integers beginning at 1, with each element of `List/@s` being a list of
 * strictly increasing integers. Yes. This is pretty.
 *)
Reindex[L_SXForm]:=Module[{s,z,is,sf, i},
  {s,z}=List@@L;
  sf = Flatten[List@@#&/@s];
  L/.Table[sf[[i]]-> i,{i,Length[sf]}]
]
Reindex[RVT[cs_, xs_, rs_]] := Module[
  {
    sf,
    cs2, xs2, rs2,
    repl, repl2
  },
   sf = Flatten[List@@#&/@cs];
   repl = (Thread[sf -> Range[Length[sf]]]);
   repl2 = repl /. {(a_ -> b_) -> ({a, i_} -> {b, i})};
   cs2 = cs /. repl;
   xs2 = xs /. repl;
   rs2 = rs /. repl2;
   RVT[cs2, xs2, rs2]
]

(*
 * The classical R-matrices, both in human-typable form and in front-end form
 *)
cR[i_,j_] := Module[
        {
                yi = Subscript[y, i],
                bi = Subscript[b, i],
                Bi = Subscript[B, i],
                aj = Subscript[a, j],
                xj = Subscript[x, j]
        },
        GDO[{}->{i,j}][ℏ aj bi, (Bi-1)/(-bi) xj yi, 1]
]
cRi[i_,j_] := Module[
        {
                yi = Subscript[y, i],
                bi = Subscript[b, i],
                Bi = Subscript[B, i],
                aj = Subscript[a, j],
                xj = Subscript[x, j]
        },
        GDO[{}->{i,j}][-ℏ aj bi, (Bi-1)/(Bi bi) xj yi, 1]
]

CC[i_] := Subscript[C, i];
CCi[i_] := Subscript[\!\(\*OverscriptBox[\(C\), \(_\)]\), i]


Subscript[Overscript[cR, _], i_, j_] := cRi[i, j]
Subscript[cR, i_,j_] := cR[i, j]

(*
 * Compute the rotation number of each component in a link already in SXForm
 * (formatting is necessary, as the output is a list which corresponds to s)
 * TODO: test or remove this function
 * FIXME: this should not depend on arc labelling
 *)
RotationNumbers[L_SXForm] := Module[{s, xs},
  {s, xs} = List @@ L;
  XingRotationNumbers[Xp[n_,N_]] := Sign[n-N];
  XingRotationNumbers[Xm[n_,N_]] := Sign[N-n];
  Table[
    Plus@@(XingRotationNumbers/@(Select[xs,SubsetQ[List@@l,List@@#]&]))
    ,{l,s}
  ]
]

CCn[i_][n_Integer]:=Module[{j},
  If[n==0,
    GDO[{} -> {i}][0,0,1],
    If[n>0,
      If[n==1,
        CC[i],
        CC[j]//CCn[i][n-1]//Subscript[cm, i,j->i]
      ],
      If[n==-1,
        CCi[i],
        CCi[j]//CCn[i][n+1]//Subscript[cm, i,j->i]
      ]
    ]
  ]
]

(*
 * Dror's GDO invariant of framed knots.
 *)
ZFramed[rvt_RVT] := Fold[#2[#1]&, GDO[{}->getIndices@rvt][0,0,1], toList@rvt]
ZFramed::notRVT := "Argument `1` is not in RVT form."
ZFramed[L_] := Message[ZFramed::notRVT, L];ZFramed[toRVT[L]]

(*
 * Dror's GDO invariant, computed in the classical algebra together with a
 * writhe correction.
 *)
Z[L_RVT] := ZFramed[PrintTemporary["Unwrithing..."]; Unwrithe[L]]
Z::notRVT := "Argument `1` is not in RVT form."
Z[L_notRVT] := Message[Z::notRVT, L]; Z@toRVT@L

(*
 * The Z invariant restricted in degree, together with the trace applied to its elements
 *)
Zdeg[deg_, L_] := CF[GDOTruncateToDegree[deg][Z[L]]]
Ztr[deg_,L_] := Zdeg[deg, L] // (Composition @@ Table[
    trDeg[i][deg],
    {i, Echo[Cases[(Unwrithe@L)[[1]], Loop[j_, __] -> j]]}
    ]
  )

ptr[L_] := Module[
        {
                ZL = Z[L],
                cod
        },
        cod = getCodomain@ZL;
        Table[(Composition@@Table[tr[j],{j,Complement[cod,{i}]}])[ZL],{i,cod}]
]
