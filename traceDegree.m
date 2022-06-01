(*
 * Purpose:
 * Using the GDO package, define the trace operator. Currently, it is only defined
 * to a(n arbitrarily large) finite degree, with the intension of extending to a
 * general form if it is determined that this indeed defines an interesting
 * invariant.
 *)

$k = 0; \[Gamma] = 1;


MatrixForm[Subscript[\[DoubleStruckCapitalE], {} -> ss_][L_,Q_,P_]] ^:=
  Subscript[\[DoubleStruckCapitalE], {} -> ss][
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
EtestScal[n_] := Subscript[\[DoubleStruckCapitalE], {} -> Range[n]][
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

Etest[n_] := Subscript[\[DoubleStruckCapitalE], {} -> Range[n]][
  Sum[
    ħ Subscript[l, i,j] Subscript[b, i] Subscript[a, j],
    {i,1,n}, {j,1,n}
  ],
  Sum[
    ħ Subscript[q, i,j] Subscript[y, i] Subscript[x, j],
    {i,1,n},{j,1,n}],
  1
]


(*
 * The coinvariants map defined on the (uncompleted) sl2-algebra expressed as a
 * non-standard multiplicative structure on a polynomial algebra.
 *)
coinv::usage = "coinv[i][f] gives the coinvarant of expression f with respect to variables indexed by i. It returns a(n in)finite sum of monomials when given a(n in)finite sum."
coinv[ii_][lincomb_Plus]:=coinv[ii]/@lincomb;
coinv[ii_][word_]:=Module[{i,j,k,l,\[Lambda]},
  \[Lambda] = Total@Flatten@CoefficientList[word,{Subscript[y, ii],Subscript[b, ii],Subscript[a, ii],Subscript[x, ii]}];
  {i,j,k,l}=Exponent[word,Subscript[#, ii]]&/@{y,b,a,x};
  If[i==l && j<=k,
    If[j==0,
      \[Lambda] i! Subscript[a, ii]^k Subscript[t, ii]^i,
      coinv[ii]@Expand[
        \[Lambda]/(i+1) *
        Subscript[y, ii]^(i + 1) *
        Subscript[b, ii]^(j-1) *
        (Subscript[a, ii]^k-(Subscript[a, ii]-1)^k) *
        Subscript[x, ii]^(i+1)
      ]
    ],
    0
  ]
]

trGenFunc::usage = "trGenFunc[i][m] generates the generating function for coinv[i] up to degree m, with (filtered) degree defined by giving weight 1 to each of y, b, a, and x."
trGenFunc[ii_][m_] := Module[{i,j,k,l},
        Sum[coinv[ii][
                Subscript[y, ii]^i Subscript[b, ii]^j
                Subscript[a, ii]^k Subscript[x, ii]^l
        ]
        (Subscript[\[Eta], ii]^i Subscript[\[Beta], ii]^j
        Subscript[\[Alpha], ii]^k Subscript[\[Xi], ii]^l)/(i!j!k!l!),
        {i,0,m},{j,0,m-i},{k,0,m-i-j},{l,0,m-i-j-k}
        ]
]

tr::usage = "tr[i][m] is the GDO element corresponding to trGenFunc[i][m]."
tr[ii_][m_] :=Module[{i,j,k,l},
        Subscript[\[DoubleStruckCapitalE], {{ii},{}} -> {{},{ii}}][
                0,0, trGenFunc[i][m]
        ]
]

(* Front-end beautification *)
Subscript[tr, ii_][m_] := tr[ii][m]

(*
 * Scale each variable by a factor of ħ
 *)
Sħ[is_List] := Product[Sħ[i],{i, is}]//Simplify;
Sħ[i_] := Subscript[\[DoubleStruckCapitalE], {i} -> {i}][
  ħ(Subscript[\[Alpha], i] Subscript[a, i] +Subscript[\[Beta], i] Subscript[b, i]),
  ħ(Subscript[\[Xi], i] Subscript[x, i] +Subscript[\[Eta], i] Subscript[y, i]),
  1
];
Subscript[Sħ, is_List]:= Sħ[is];
Subscript[Sħ, i_] := Sħ[i];

(*
 * Convert a GDO series to a polynomial
 *)

ScaleByLambda[i_] := Subscript[\[DoubleStruckCapitalE],{i} -> {i}][
  \[Lambda] (
    Subscript[a, i] Subscript[\[Alpha], i] +
    Subscript[b, i] Subscript[\[Beta], i] +
    Subscript[t, i] Subscript[\[Tau], i]),
  \[Lambda] (
    Subscript[y, i] Subscript[\[Eta], i] +
    Subscript[x, i] Subscript[\[Xi], i]),
  1
]

AddWeight[Subscript[\[DoubleStruckCapitalE], is__->js__][L_,Q_,P_]] := Module[
  {
    L2, Q2, P2
  },
  Subscript[\[DoubleStruckCapitalE], is->js][L2, Q2, P2]
]

TruncateToDegree[n_][
  Subscript[\[DoubleStruckCapitalE], is__->js__][L_,Q_,P_]]:=
  Subscript[\[DoubleStruckCapitalE], is->js][0,0,
    Expand@Normal[Series[Exp[L+Q]*P/.U2l,{ħ,0,n}]]
]

GDOToList[Subscript[\[DoubleStruckCapitalE], is_->js_][L_,Q_,P_]] := {is, js, L, Q, P};
GDOFromList[is_, js_, L_, Q_, P_] := Subscript[\[DoubleStruckCapitalE], is->js][L,Q,P]

(* TruncateToDegreeWrong[n_][GDO_] := Module[
  {is, js, ks, L, Q, P},
  ks = GDOToList[GDO][[2]];
  [>{is, js, L, Q, P} = GDOToList[Sħ[ks] // GDO];<]
  {is, js, L, Q, P} = GDOToList[GDO // Sħ[ks]];
  Subscript[\[DoubleStruckCapitalE], is->js][0,0, Normal[Series[Exp[L+Q]*P/.U2l,{ħ,0,n}]]]
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
cR[i_,j_] := Subscript[\[DoubleStruckCapitalE],{}->{i,j}][
  ħ Subscript[a, j] Subscript[b, i],
  (Subscript[B, i]-1)/(-Subscript[b, i]) Subscript[x, j] Subscript[y, i],
  1
]
cRi[i_,j_] := Subscript[\[DoubleStruckCapitalE],{}->{i,j}][
  -ħ Subscript[a, j] Subscript[b, i],
  (Subscript[B, i]-1)/(Subscript[B, i] Subscript[b, i]) Subscript[x, j] Subscript[y, i],
  1
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
    Subscript[\[DoubleStruckCapitalE], {} -> {i}][0,0,1],
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
  ];
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

(* trZ := ((Times @@ Table[tr[i][2], {i, #[[0, 2, 2]]}])[#] & )@* Simplify@*(TruncateToDegree[4, #] &)@*Z) & *)

(*
 * The Z invariant restricted in degree, together with the trace applied to its elements
 *)
Zdeg[deg_, L_] := CF[TruncateToDegree[deg][Z[L]]]
(* trZ[deg_,L_] :=  (Times @@ Table[tr[i][deg], {i,      #[[0, 2, 2]]}])[#]&[Zdeg[deg, L]] *)
Ztr[deg_,L_] := Zdeg[deg, L] // (Composition @@ Table[
    tr[i][deg],
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
      tr[j][deg],
      {j, Complement[cod,{i}]}
    ])[ZL]
    ,{i, cod}
  ]
]
