(*
 * Purpose:
 * Using the GDO package, define the trace operator. Currently, it is only defined
 * to a(n arbitrarily large) finite degree, with the intension of extending to a
 * general form if it is determined that this indeed defines an interesting
 * invariant.
 *)

$k = 0; \[Gamma] = 1;

η[i_] := Subscript[η, i];
β[i_] := Subscript[β, i];
α[i_] := Subscript[α, i];
ξ[i_] := Subscript[ξ, i];
τ[i_] := Subscript[τ, i];
y[i_] := Subscript[y, i];
b[i_] := Subscript[b, i];
B[i_] := Subscript[B, i];
a[i_] := Subscript[a, i];
x[i_] := Subscript[x, i];
t[i_] := Subscript[t, i];
T[i_] := Subscript[T, i];

GDO::usage = "GDO[is -> js][Qs] is shorthand for Subscript[\[DoubleStruckCapitalE], is -> js][Qs]."
GDO[ijs___][Qs___] := Subscript[\[DoubleStruckCapitalE], ijs][Qs]

getDomain[GDO[is_->js_][L_,Q_,P_]]:=is;
getCodomain[GDO[is_->js_][L_,Q_,P_]]:=js;
getSeries[GDO[is_->js_][L_,Q_,P_]]:={L,Q,P};
getIndices[gdo_]:=Union@Flatten@{getDomain[GDO],getCodomain[GDO]};
isolateSubscripts[a_->b_]:=Subscript[x_, a]->Subscript[x, b];
getPLength[gdo_] := Map[Length,ExpandAll[GDO],{1}][[3]];


Reindex\[DoubleStruckCapitalE][gdo_]:=Module[
        {
        replacementRules,
        subscriptReplacementRules,
        indices = getIndices[gdo],
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
(* trDeg[m_][ii_] := GDO[{{ii},{}} -> {{},{ii}}][
        0, 0, trGenFunc[m][ii]
] *)
trDeg[m_][i_] := GDOTruncateToDegree[m]@trGuess[i]

trGuess::usage = "trGuess[i] is a placeholder guess for a GDO expression which represents a trace."
trGuess[i_] := Module[
        {ηi, βi, αi, ξi, ai, ti},
        ηi = Subscript[η, i];
        βi = Subscript[β, i];
        αi = Subscript[α, i];
        ξi = Subscript[ξ, i];
        ai = Subscript[a, i];
        ti = Subscript[t, i];
        GDO[{{i},{}}->{{},{i}}][αi ai, ηi ξi ti, Exp[βi (1-Exp[-αi]) ti]]
        (* GDO[{{i},{}}->{{},{i}}][αi ai, ηi ξi ti, 1 + βi (1-Exp[-αi]) ti]/.l2U *)
]

(* Coefficient-extraction functions *)

getConstCoef::usage = "getConstCoef[i][gdo] returns the terms in a GDO expression which are not a function of y[i], b[i], a[i], nor x[i]."
getConstCoef[i_][gdo_] := Total@(getSeries[gdo]/.
        {y[i]->0,b[i]->0,a[i]->0,x[i]->0})

getyCoef::usage = "getyCoef[i][gdo][b[i]] returns the linear coefficient of y[i] as a function of b[i]."
getyCoef[i_][gdo_][bb_] := (Coefficient[getSeries[gdo][[2]]/.{x[i]->0}, y[i],
        1]/.U2l)/.Subscript[b, i]:>bb

getbCoef::usage = "getbCoef[i][gdo] returns the linear coefficient of b[i]."
getbCoef[i_][gdo_] :=
        (SeriesCoefficient[#, {b[i],0,1}]&) @*
        (Coefficient[#, a[i],0]&) @*
        ReplaceAll[U2l] @
        getSeries[gdo][[1]]

getaCoef::usage = "getaCoef[i][gdo] returns the linear coefficient of a[i]."
getaCoef[i_][gdo_] := Coefficient[getSeries[gdo][[1]]/.U2l/.{b[i]->0}, a[i], 1]

getxCoef::usage = "getxCoef[i][gdo][b[i]] returns the linear coefficient of x[i] as a function of b[i]."
getxCoef[i_][gdo_][bb_] :=
        ReplaceAll[{b[i]->bb}] @*
        ReplaceAll[U2l] @*
        (Coefficient[#, y[i],0]&) @*
        (Coefficient[#, x[i],1]&) @
                (getSeries[gdo][[2]])

getabCoef::usage = "getabCoef[i][gdo] returns the linear coefficient of a[i]b[i]."
getabCoef[i_][gdo_] := (Coefficient[#,b[i],1]&) @* (Coefficient[#,a[i],1]&) @
        (getSeries[gdo][[1]]/.U2l)

getxyCoef::usage = "getxyCoef[i][gdo][b[i]] returns the linear coefficient of x[i]y[i] as a function of b[i]."
getxyCoef[i_][gdo_][bb_] := (Coefficient[#,x[i],1]&) @* (Coefficient[#,y[i],1]&)@
        (getSeries[gdo][[2]]/.U2l)/.{b[i]->bb}

tr::usage = "tr[i] computes the trace of a GDO element on component i. Current implementation assumes the Subscript[a, i] Subscript[b, i] term vanishes and $k=0."
tr::nonzeroSigma = "tr[`1`]: Component `1` has writhe: `2`, expected: 0."
tr[i_][gdo_] := Module[
        {
                c = getConstCoef[i][gdo],
                η = getyCoef[i][gdo],
                β = getbCoef[i][gdo],
                α = getaCoef[i][gdo],
                ξ = getxCoef[i][gdo],
                λ = getxyCoef[i][gdo],
                ins  = toMixed@getDomain[gdo],
                outs = toMixed@getCodomain[gdo],
                ta
        },
        ta = (1-Exp[-α]) t[i];
        GDO[ins -> closeComponent[i][outs]][
                c + α a[i] + β ta + t[i] (η[ta] ξ[ta] + λ[ta])/(1-t[i] λ[ta])
        ]
] /; Module[
        {σ = getabCoef[i][gdo]},
        If[σ == 0,
                True,
                Message[tr::nonzeroSigma, i, ToString[σ]]; False
        ]
]

(* FIXME: BEGIN DEPRECATED CODE *)
(* Front-end beautification *)
Subscript[trDeg, ii_][m_] := trDeg[m][ii]

(*
 * Scale each variable by a factor of ħ
 *)
Sħ[is_List] := Product[Sħ[i],{i, is}]//Simplify;
Sħ[i_] := GDO[{i} -> {i}][
  ħ(Subscript[\[Alpha], i] Subscript[a, i] +Subscript[\[Beta], i] Subscript[b, i]),
  ħ(Subscript[\[Xi], i] Subscript[x, i] +Subscript[\[Eta], i] Subscript[y, i]),
  1
];
Subscript[Sħ, is_List]:= Sħ[is];
Subscript[Sħ, i_] := Sħ[i];
(* FIXME: END DEPRECATED CODE *)

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
        scaler
        },
        scaler=Product[ScaleBy[λ][i],{i, Flatten@is}];
        {L, Q, P} = getSeries[scaler//gdo];
        GDO[is->js][0, 0, TruncateToDegree[n][λ][(Exp[L+Q]*P)/.U2l]]/.(λ->1)
]

GDOToList[GDO[is_->js_][L_,Q_,P_]] := {is, js, L, Q, P};
GDOFromList[is_, js_, L_, Q_, P_] := GDO[is->js][L,Q,P]

(* GDOTruncateToDegreeWrong[n_][gdo_] := Module[
  {is, js, ks, L, Q, P},
  ks = GDOToList[GDO][[2]];
  [>{is, js, L, Q, P} = GDOToList[Sħ[ks] // GDO];<]
  {is, js, L, Q, P} = GDOToList[GDO // Sħ[ks]];
  GDO[is->js][0,0, Normal[Series[Exp[L+Q]*P/.U2l,{ħ,0,n}]]]
] *)

(* Skeleton-Xing form *)
SXForm[L_SXForm]:=L
SXForm[L_] := SXForm[
  Skeleton[L],
  List@@PD[L] /. (X[i_,j_,k_,l_] :>
    If[PositiveQ[X[i,j,k,l]],Xp[l,i], Xm[j,i]])
];

(*
 * Compute the writhe of a link, returning a list of integers corresponding to the
 * components.
 *)
Writhe[L_SXForm]:=Module[{s,z},
  {s,z}=List@@L;
  (* Print["s: ",s]; *)
  (* Print["z: ",z]; *)
  Table[
      (Plus@@z)/.{
        Xp[i_,j_]:>If[MemberQ[l,i] \[And] MemberQ[l,j], 1,0],
        Xm[i_,j_]:>If[MemberQ[l,i] \[And] MemberQ[l,j],-1,0]
    },
    {l,s}
  ]
]
Writhe[L_]:=Writhe[SXForm[L]]

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
Unwrithe[RVT[cs_, xs_, rs_]] := Module[{lw},
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
(* CCi[i_] := Subscript[Overscript[C, _], i] *)
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
 * TODO: implement rotation number corrections
 *)
ZFramed[RVT[cs_, xs_, rs0_]] := Module[{
    z,
    is = Flatten[List@@@cs],
    i1,
    rs,
    b,
    (* i, *)
    j,
    (* localprint = Print *)
    localprint = Identity
  },
  rs = DeleteCases[rs0,{_,0}];
  (* localprint[rs]; *)
  z=Times@@xs/.{Xp[i_,j_]:>cR[i,j], Xm[i_,j_]:>cRi[i,j]};
  (* localprint["Introducing strands..."]; *)
  z *= Product[Subscript[c\[Eta],i], {i, is}];
  (* localprint["Building Rotation numbers..."]; *)
  z *= Times@@(rs /. {{i_Integer, n_Integer} -> CCn[b[i]][n]});
  (* localprint["Applying kinks..."]; *)
  Do[
    (* localprint["(", i, "<-", b[i], ")"]; *)
    z = z // Subscript[cm, b[i], i -> i],
    {i, First/@rs}
  (* localprint["Applying multiplication..."]; *)
  ];
  Do[
    i1 = First[i];
    (* localprint["(", i1,"\[LeftArrow]", k,")..."]; *)
    z = z // Subscript[cm, i1, k -> i1];
    If[k==2,
      (* localprint["Simplifying..."]; *)
      z = Simplify[z]
    ],
    {i, cs},{k, List@@Rest[i]}
  ];
  z
]
ZFramed::NotRVT := "Argument `1` is not in RVT form."
ZFramed[L_] := Message[ZFramed::NotRVT, L];ZFramed[toRVT[L]]

(* ZFramed[E_GDOSeq] :=  *)

(*
 * Dror's GDO invariant, computed in the classical algebra together with a
 * writhe correction.
 *)
Z::SXForm := "Argument `1` is not in RVT form."
Z[L_RVT] := ZFramed[PrintTemporary["Unwrithing..."]; Unwrithe[L]]
Z[L_SXForm] := Message[Z::SXForm, L]
Z[L_] := Z[PrintTemporary["Converting to SXForm..."]; SXForm[L]]

(* trZ := ((Times @@ Table[trDeg[i][2], {i, #[[0, 2, 2]]}])[#] & )@* Simplify@*(GDOTruncateToDegree[4, #] &)@*Z) & *)

(*
 * The Z invariant restricted in degree, together with the trace applied to its elements
 *)
Zdeg[deg_, L_] := CF[GDOTruncateToDegree[deg][Z[L]]]
(* trZ[deg_,L_] :=  (Times @@ Table[trDeg[i][deg], {i,      #[[0, 2, 2]]}])[#]&[Zdeg[deg, L]] *)
Ztr[deg_,L_] := Zdeg[deg, L] // (Composition @@ Table[
    trDeg[i][deg],
    {i, Echo[Cases[(Unwrithe@L)[[1]], Loop[j_, __] -> j]]}
    ]
  )

ptr[deg_][L_] := Module[
  {
    ZL = Zdeg[deg, L],
    cod
  },
  cod = getCodomain@ZL;
  Table[
    (Composition @@ Table[
      trDeg[j][deg],
      {j, Complement[cod,{i}]}
    ])[ZL]
    ,{i, cod}
  ]
]
