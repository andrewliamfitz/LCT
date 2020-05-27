(* ::Package:: *)

(* ::Chapter:: *)
(*Set parameters*)


If[!NumberQ[Nc],Print["Need to specify Nc first"];Abort[] ]
If[!NumberQ[\[CapitalDelta]max],Print["Need to specify \[CapitalDelta]max first"];Abort[] ]


(* ::Chapter:: *)
(*Basis states*)


(* These are the coefficients in the double trace construction *)
PrimCoeffs[\[CapitalDelta]A_, \[CapitalDelta]B_, l_, k_] = ((-1)^
   k Gamma[2 \[CapitalDelta]A + l] Gamma[2 \[CapitalDelta]B + l])/(
  k! (l - k)! Gamma[2 \[CapitalDelta]A + k] Gamma[
    2 \[CapitalDelta]B + l - k]);


(*
monoExpand[op] expands the primary operators into monomials. The input is an operator specified by
{O1,O2,l,n,Delta}, which is generated in stateSet[dim].
The output is a list of monomials specified by
	{ ck, { {k1, k2}, {k3, k4},... } }
which means the operator ck(d^k1 psidag d^k2 psi)(d^k3 psidag d^k4 psi)...
The coefficients ck are computed by explicitly taking the double trace construction
	Sum[PrimCoeffs[\[CapitalDelta]1,\[CapitalDelta]2,l,k]  \[Times] dMono[O1,k] \[Times] dMono[O2,l-k],k]
*)
monoExpand[op_?ListQ] := monoExpand[op] = If[op[[4]] != 1, Block[
    {l = op[[3]], dim1 = op[[1, 5]], dim2 = op[[2, 5]],
     coeff, n1 = op[[1, 4]], n2 = op[[2, 4]],
     op1 = monoExpand[op[[1]]], op2 = monoExpand[op[[2]]],
     dMonosList1, dMonosList2
     },
    dMonosList1 = dMonosList[ monoExpand[op[[1]]], l ];
    dMonosList2 = dMonosList[ monoExpand[op[[2]]], l ];
    
    DeleteCases[
     {#[[;; , 1]] // Total, #[[1, 2]]} & /@ GatherBy[Flatten[Table[
         coeff = PrimCoeffs[dim1, dim2, l, k]*
           mono1[[1]]*mono2[[1]];
         {coeff, Sort[Join[mono1[[2]], mono2[[2]]]]},
         {k, 0, l},
         {mono1, dMonosList1[[k + 1]]},
         {mono2, dMonosList2[[l - k + 1]]}
         ], 2], Last],
     {0, __}]
    ],
   Table[
    {PrimCoeffs[1/2, 1/2, op[[3]], k],
     {{k, op[[3]] - k}}},
    {k, 0, op[[3]]}]
   ]


(*stateSet[dim] computes the basis states at dimension dim from taking the double-trace construction of lower dim. Subscript[\[ScriptCapitalO], 1]Overscript[\[PartialD]^\[ScriptL], \[TwoWayRule]]Subscript[\[ScriptCapitalO], 2]\[Congruent]\!\(
\*SubscriptBox[\(\[Sum]\), \(k\)]\(PrimCoeffs[\[CapitalDelta]1, \[CapitalDelta]2, \[ScriptL], k]\ 
\*SuperscriptBox[\(\[PartialD]\), \(k\)]\ 
\*SubscriptBox[\(\[ScriptCapitalO]\), \(1\)]
\*SuperscriptBox[\(\[PartialD]\), \(\[ScriptL] - k\)]
\*SubscriptBox[\(\[ScriptCapitalO]\), \(2\)]\)\) 
The output of stateSet[dim] is a list of operators written as
	{O1,O2,l, n, Delta }
where O1 and O2 are the two low dim operators that the operator is made of,
l is the total number of derivatives acting on O1 and O2,
n is half of the total number of particles,
Delta is the total dimension, dim.
The beginning seed are operators psi and psidag, represented by 1 and (-1), respectively.*)
ClearAll[stateSet]
stateSet[dim_] := stateSet[dim] = DeleteDuplicatesBy[
   Select[
    Block[
     { set = {} },
     If[dim >= 1,
      AppendTo[set, {-1, 1, dim - 1, 1, dim}];
      Do[
       AppendTo[
        set, {state1, state2, dim - dim1 - dim2, 
         state1[[4]] + state2[[4]], dim}],
       {dim1, dim - 1, 1, -1},
       {dim2, 1, Min[dim - dim1, dim1], 1},
       {state1, stateSet[dim1]},
       {state2, stateSet[dim2]}]  ];
     set
     ],
    monoExpand[#] != {} &], monoExpand]


(* Take the derivative of a monomial *)
dMono[mono_] := Block[{mono1},
  {#[[2]]*mono[[1]], #[[1]]} & /@ Tally[Flatten[Table[
      mono1 = mono[[2]]; mono1[[r1, s1]] += 1;
      Sort[mono1],
      {r1, 1, Length[mono[[2]]]}, {s1, 1, 2}], 1] ]
  ]
(* Make a list of d^k O, k = 0,1,2,...,l *)
dMonosList[monos_, l_] := Block[
  {res = {}, last},
  AppendTo[res, monos];
  Do[
   last = DeleteCases[
     {#[[;; , 1]] // Total, #[[1, 2]]} & /@ 
      GatherBy[Flatten[dMono /@ res[[-1]], 1], Last],
     {0, __}];
   AppendTo[res, last];,
   {k, 1, l}];
  res
  ]


(* ::Chapter:: *)
(*Wick Contraction*)


(* ::Section:: *)
(*Inner products, color indices and contractions of spectators*)


(*AF[ \[Lambda]1 ,\[Lambda]2, tensor ] computes the Wick contraction of the spectators recursively.
AF[ \[Lambda]1 ,\[Lambda]2, tensor ] has the following structure:
\[Lambda]1 specifies the monomial on the left and \[Lambda]2 specifies the monomial on the right.
\[Lambda]\[Congruent]{ { k, s, m },.... } and { k, s, m } means
	 d^k psi_im if s=1
	 d^k psidag_im if s=-1 
tensor specifies the tensors like delta_ij delta_kl multiplying the formula.*)


(* Take the tensor contraction of color indices. *)
indicesReduce = {
   Times[delta[a_, b_], delta[b_, c_]] /; a != c
    -> delta[a, c],
   Times[delta[a_, b_], delta[b_, a_]]
    -> Nc,
   delta[a_, a_] -> Nc
   };
SetAttributes[delta, Orderless];


(* Compute the Wick contraction of the spectators recursively. *)
ClearAll[AF]
AF[{}, {}, 1] = 1;
AF[{}, {}, tensor_] := ReplaceRepeated[tensor, indicesReduce];
AF[\[Lambda]1_List, \[Lambda]2_List(*/;Length@\[Lambda]2>=2*), 
   tensor_] := 
  AF[\[Lambda]1, \[Lambda]2, tensor] = 
   Block[{n = Length[\[Lambda]2], num}, Sum[
     (-1)^(n - i)*((num = # /. delta[__] -> 1)*
          Gamma[\[Lambda]1[[1, 1]] + \[Lambda]2[[i, 1]] + 1]
          AF[Drop[\[Lambda]1, {1}], Drop[\[Lambda]2, {i}],
           (*List@@#*)#/num
           ]
         ) &@ReplaceRepeated[
       Times[tensor, 
        delta[ \[Lambda]1[[1, 3]], \[Lambda]2[[i, 3]] ]  ],
       indicesReduce
       ], {i,
      Flatten[Position[\[Lambda]2[[;; , 2]], -\[Lambda]1[[1, 2]]] ]
      }]
    ];


(* ::Chapter:: *)
(*Gauge interaction*)


(* ::Section:: *)
(*Gauge interaction: structure*)


(* ::Subsection:: *)
(*Make a rule for selecting the active part*)


(* ::Subsubsection:: *)
(*N to N*)


(*In the 2n to 2n matrix elements, 2 fermions in the bra and 2 fermions in the ket contracts with the active part. 
selectionNtoN[n] gives a list of possible ways to contract these fermions
	{ { iL, jL }, { iR, jR } }
which means the iL-th and jL-th fermion in the bra contract with the active part,
and  iR-th and jR-th fermion in the ket contract with the active part.
The spins of the contracted fermions have to work out. The odd positions are psidag and even positions are psi.
Note that in this subsection, n is the number of fermions. In other parts of the code the number of fermions is usually 2n.*)


ClearAll[selectionNtoN]
selectionNtoN[n_] := 
 selectionNtoN[n] = 
  DeleteDuplicates[DeleteCases[Map[Sort, Thread /@ Subsets[Join[
        Tuples[  {Select[Range[n], OddQ], 
          Select[Range[n], EvenQ]}  ],
        Tuples[  {Select[Range[n], EvenQ], Select[Range[n], OddQ]}  ]
        ], {2}], {2}], {_, {x_, x_}} | {{x_, x_}, _}]]


(* ::Subsubsection:: *)
(*N to N+2*)


(*In the 2n to 2n+2 matrix elements, 1 fermion in the bra and 3 fermions in the ket contracts with the active part. 
selectionNtoN2[nR] gives a list of possible ways to contract these fermions
	{ { iL }, { iR, jR, kR } }
which means the iL-th fermion in the bra contracts with the active part,
and  iR-th, jR-th and  kR-th fermion in the ket contract with the active part.
The spins of the contracted fermions have to work out. The odd positions are psidag and even positions are psi.
Note that in this subsection, n is the number of fermions. In other parts of the code the number of fermions is usually 2n.*)


ClearAll[selectionNtoN2]
selectionNtoN2[nR_] := selectionNtoN2[nR] =
  Join[
   Tuples[{
     Subsets[Select[Range[nR - 2], EvenQ], {1}],
     Sort /@ Flatten /@ Tuples[{
         Select[Range[nR], EvenQ],
         Subsets[  Select[Range[nR], OddQ], {2}  ]
         }]
     }],
   Tuples[{
     Subsets[Select[Range[nR - 2], OddQ], {1}],
     Sort /@ Flatten /@ Tuples[{
         Select[Range[nR], OddQ],
         Subsets[  Select[Range[nR], EvenQ], {2}  ]
         }]
     }]
   ]


(* ::Subsection:: *)
(*Find the permutation signature, color factor and the spectator inner product for each active part*)


(* ::Subsubsection:: *)
(*N to N*)


(*NtoNFActive[{ s1, s2, s3, s4 }][ k1, k2, k3, k4, i1, i2, i3, i4, \[Lambda], \[Lambda]p ] computes 
the contribution to the monomial's 2n to 2n matrix elements from a certain selection 
of the "active fermions" that contract with the interaction:
psidag T^a psi (1/d^2) psidag T^a psi= Int dy' dy''(psidag T^a psi)(y')(psidag T^a psi)(y'') 
{ s1, s2, s3, s4 } specifies the whether a particle is (if s=1) psi or (if s=-1) psidag .
{ k1, k2, k3, k4 } specifies the number of derivative k in d^k psi or d^k psidag of the active fermions.
{ i1, i2, i3, i4 } specifies the color indices of the active fermions.
\[Lambda] and \[Lambda]p are the spectators.

The definition of NtoNFActive are automatically generated by running the following code, 
which iterates all possible cases and defines NtoNFActive for each case.*)


ClearAll[NtoNFActive]
Block[{sign, 
  lst = {{k1, s1, i1, t1}, {k2, s2, i2, t2}, {k3, s3, i3, t3}, {k4, 
     s4, i4, t4}}, lstP,
  bin, col,
  s1, s2, s3, s4,
  t1, t2, t3, t4,
  out, factor = 1
  }, Do[(* For each setup of {s1,s2,s3,s4}, 
  take t1=t2=1 and t3=t4=2 so the operators 1,2 come from the bra 
  and 3,4 come from the ket*)
(* {t1,t2,t3,t4} specifies the side from which active fermions come from:
1 means the bra state and 2 means the ket state. *)
  {s1, s2, s3, s4} = exInfo[[1]];
  {t1, t2, t3, t4} = exInfo[[2]];
  
  out = DeleteCases[{Total[#[[;; , 1]]] // Simplify, #[[1, 2]]} & /@ 
     GatherBy[Reap[Do[
     (* For each permutation of the 4 particles *)
	(* First, one gets a sign from the signature of the permutation:
	1234 is +1 *)
         sign = Signature[perm];
         (* lst = {{k1,s1,i1,t1}...} is the external operator data 
         and the lstP changes the order of operators to that in perm *)
         lstP = lst[[perm]];
         (* The Wick contraction gives a spacial 4 pt function
		(x-yp)^-a(yp-z)^-b(x-ypp)^-ap(ypp-z)^-bp times the factors from spectators,
		and the variable bin stores {{a,b},{ap,bp}}  *)
         bin = {{0, 0}, {0, 0}};
         If[
          (* lsp[[1]] and lsp[[2]] contracts with yp and 
			lsp[[3]] and lsp[[4]] contracts with ypp. *)
		(* First, the spin of each particle in lsp[[i]] needs to match 
			the corresponding operator in the interaction. *)
          lstP[[1, 2]] == 1 && lstP[[2, 2]] == -1 && 
           lstP[[3, 2]] == 1 && lstP[[4, 2]] == -1,
           (* Compute a,b,ap,bp *)
          bin[[1, lstP[[1, 4]] ]] += lstP[[1, 1]] + 1;
          bin[[1, lstP[[2, 4]] ]] += lstP[[2, 1]] + 1;
          bin[[2, lstP[[3, 4]] ]] += lstP[[3, 1]] + 1;
          bin[[2, lstP[[4, 4]] ]] += lstP[[4, 1]] + 1;
          (* If FreeQ[bin,0], then (C.34) applies. 
          The Gamma(a)Gamma(b)Gamma(ap)Gamma(bp) on the denominator in (C.34) 
          always cancels Gamma(k+1) factors that drop out when Wick contracting 
          the active psi's to the interaction. But in (C.35)~(C.37) the denominators 
          are something else and won't cancel the Gamma(k+1) factors. The denominator 
          is explicitly computed in the above equations and in gauge[] so here we 
          need to multiply the Gamma(k+1) factors. *)
          If[FreeQ[bin, 0], factor = 1,
           factor = Product[Gamma[ lstP[[i, 1]] + 1 ], {i, 4}]  ];
          (*
		(-1)^Total[{t1,t2,t3,t4}] is the sign from moving the interaction term pass the 
		active fermions in the external states.
		factor is the Gamma(k1+1)Gamma(k2+1)Gamma(k3+1)Gamma(k4+1) factor 
		in (C.35)~(C.37).
		There are two color tensor structures, each with coefficient 1/2 and 1/(2Nc) 
		respectively.
		The (a,b,ap,bp) data is sent to gauge[] to compute (C.34)~(C.37).*)
          Sow[{(-1)^Total[{t1, t2, t3, t4}]*factor*
             sign*(-1/(2 Nc))*(gauge @@ Flatten[bin]),
            
            delta[lstP[[1, 3]], lstP[[2, 3]]]*
             delta[lstP[[3, 3]], lstP[[4, 3]]]}];
          
          Sow[{(-1)^Total[{t1, t2, t3, t4}]*factor*
             sign*(1/2)*(gauge @@ Flatten[bin]),
            
            delta[lstP[[1, 3]], lstP[[4, 3]]]*
             delta[lstP[[2, 3]], lstP[[3, 3]]]}],
          0],
         {perm, Permutations[Range[4]]}
         ]   ][[2, 1]], Last], {0, _}];
  
  NtoNFActive[{s1, s2, s3, s4}(*,{t1,t2,t3,t4}*)] = Function[
    {k1, k2, k3, k4, i1, i2, i3, i4, \[Lambda], \[Lambda]p}, 
    Evaluate[
    (* term[[1]] is the numerical factors, term[[2]] is the color tensor. 
    The spectators data and the color tensor are sent to AF *)
     Sum[
      term[[1]]*(AF[\[Lambda], \[Lambda]p, term[[2]]]),
      {term, out}]
     ]
    ],
    (* Iterate all possible spin setups. *)
  {exInfo, Tuples[{
      Permutations[{1, 1, -1, -1}],
      {{1, 1, 2, 2}}
      }] // DeleteDuplicates}
  ]
 ]


(*NtoNFActiveSaved[{s1_, s2_, s3_, s4_}][k1_, k2_, k3_, k4_, i1_, i2_, i3_, i4_, \[Lambda]_, \[Lambda]p_]:=
NtoNFActiveSaved[{s1, s2, s3, s4}][k1, k2, k3, k4, i1, i2, i3, i4, \[Lambda], \[Lambda]p]=
NtoNFActive[{s1, s2, s3, s4}][k1, k2, k3, k4, i1, i2, i3, i4, \[Lambda], \[Lambda]p]*)


(* ::Subsubsection:: *)
(*N to N+2*)


(*NtoN2FActive[{ s1, s2, s3, s4 }][ k1, k2, k3, k4, i1, i2, i3, i4, \[Lambda], \[Lambda]p ] computes 
the contribution to the monomial's matrix elements of the interaction 2n to 2n+2 matrix 
from a certain selection of the "active fermions" that contract with the interaction:
psidag T^a psi (1/d^2) psidag T^a psi = Int dy' dy''(psidag T^a psi)(y')(psidag T^a psi)(y'') 
{ s1, s2, s3, s4 } specifies the whether a particle is (if s=1) psi or (if s=-1) psidag .
{ k1, k2, k3, k4 } specifies the number of derivative k in d^k psi or d^k psidag of 
the active fermions.
{ i1, i2, i3, i4 } specifies the color indices of the active fermions.
\[Lambda] and \[Lambda]p are the spectators.

The definition of NtoN2FActive are automatically generated by running the 
following code, which iterates all possible cases and defines NtoN2FActive for each 
case.*)


ClearAll[temp, NtoN2FActive]
Block[{sign, 
  lst = {{k1, s1, i1, t1}, {k2, s2, i2, t2}, {k3, s3, i3, t3}, {k4, 
     s4, i4, t4}}, lstP,
  bin, col,
  s1, s2, s3, s4,
  t1, t2, t3, t4,
  out, factor = 1
  }, Do[
  (* For each setup of {s1,s2,s3,s4}, take t1=1 and t2=t3=t4=2 
  so the operators 1 comes from the bra and 2,3,4 come from the ket*)
(* {t1,t2,t3,t4} specifies the side from which active fermions come from:
1 means the bra state and 2 means the ket state. *)
  {s1, s2, s3, s4} = exInfo[[1]];
  {t1, t2, t3, t4} = exInfo[[2]];
  
  out = DeleteCases[{Total[#[[;; , 1]]] // Simplify, #[[1, 2]]} & /@ 
     GatherBy[Reap[Do[
     (* For each permutation of the 4 particles *)
	(* First, one gets a sign from the signature of the permutation:
	1234 is +1 *)
         sign = Signature[perm];
         (* lst = {{k1,s1,i1,t1}...} is the external operator data 
         and the lstP changes the order of operators to that in perm *)
         lstP = lst[[perm]];
         (* The Wick contraction gives a spacial 4 pt function
		(x-yp)^-a(yp-z)^-b(x-ypp)^-ap(ypp-z)^-bp times the factors from spectators,
		and the variable bin stores {{a,b},{ap,bp}}  *)
         bin = {{0, 0}, {0, 0}};
         If[
          (* lsp[[1]] and lsp[[2]] contracts with yp and 
		lsp[[3]] and lsp[[4]] contracts with ypp. *)
		(* First, the spin of each particle in lsp[[i]] needs to match 
		the corresponding operator in the interaction. *)
          lstP[[1, 2]] == 1 && lstP[[2, 2]] == -1 && 
           lstP[[3, 2]] == 1 && lstP[[4, 2]] == -1,
           (* Compute a,b,ap,bp *)
          bin[[1, lstP[[1, 4]] ]] += lstP[[1, 1]] + 1;
          bin[[1, lstP[[2, 4]] ]] += lstP[[2, 1]] + 1;
          bin[[2, lstP[[3, 4]] ]] += lstP[[3, 1]] + 1;
          bin[[2, lstP[[4, 4]] ]] += lstP[[4, 1]] + 1;
          (* If FreeQ[bin,0], then (C.34) applies. 
          The Gamma(a)Gamma(b)Gamma(ap)Gamma(bp) on the denominator in (C.34) 
          always cancels Gamma(k+1) factors that drop out when Wick contracting 
          the active psi's to the interaction. But in (C.35)~(C.37) the denominators 
          are something else and won't cancel the Gamma(k+1) factors. The denominator 
          is explicitly computed in the above equations and in gauge[] so here we 
          need to multiply the Gamma(k+1) factors. *)
          If[FreeQ[bin, 0], factor = 1,
           factor = Product[Gamma[ lstP[[i, 1]] + 1 ], {i, 4}]  ];
          (*
		(-1)^Total[{t1,t2,t3,t4}] is the sign from moving the interaction term pass 
		the active fermions in the external states.
		factor is the Gamma(k1+1)Gamma(k2+1)Gamma(k3+1)Gamma(k4+1) factor 
		in (C.35)~(C.37).
		There are two color tensor structures, each with coefficient 1/2 and 1/(2Nc) 
		respectively.
		The (a,b,ap,bp) data is sent to gauge[] to compute (C.34)~(C.37).
		*)
          Sow[{(-1)^Total[{t1, t2, t3, t4}]*factor*
             sign*(-1/(2 Nc))*(gauge @@ Flatten[bin]),
            
            delta[lstP[[1, 3]], lstP[[2, 3]]]*
             delta[lstP[[3, 3]], lstP[[4, 3]]]}];
          
          Sow[{(-1)^Total[{t1, t2, t3, t4}]*factor*
             sign*(1/2)*(gauge @@ Flatten[bin]),
            
            delta[lstP[[1, 3]], lstP[[4, 3]]]*
             delta[lstP[[2, 3]], lstP[[3, 3]]]}],
          0],
         {perm, Permutations[Range[4]]}
         ]   ][[2, 1]], Last], {0, _}];
  
  NtoN2FActive[{s1, s2, s3, s4}(*,{t1,t2,t3,t4}*)] = Function[
    {k1, k2, k3, k4, i1, i2, i3, i4, \[Lambda], \[Lambda]p}, 
    Evaluate[
    (* term[[1]] is the numerical factors, term[[2]] is the color tensor. 
    The spectators data and the color tensor are sent to AF *)
     Sum[
      term[[1]]*(AF[\[Lambda], \[Lambda]p, term[[2]]]),
      {term, out}]
     ]
    ],
  {exInfo, Tuples[{
      Permutations[{1, 1, -1, -1}],
      {{1, 2, 2, 2}}
      }] // DeleteDuplicates}
  ]
 ]


(*NtoN2FActiveSaved[{s1_, s2_, s3_, s4_}][k1_, k2_, k3_, k4_, i1_, i2_, i3_, i4_, \[Lambda]_, \[Lambda]p_]:=
NtoN2FActiveSaved[{s1, s2, s3, s4}][k1, k2, k3, k4, i1, i2, i3, i4, \[Lambda], \[Lambda]p]=
NtoN2FActive[{s1, s2, s3, s4}][k1, k2, k3, k4, i1, i2, i3, i4, \[Lambda], \[Lambda]p]*)


(* ::Subsection:: *)
(*Put together*)


(* ::Subsubsection:: *)
(*N to N*)


(*NtoNF[k,kp] sums over all possible contractions computed by NtoNFActive[] 
and returns the  2n to 2n matrix elements between a pair of monomials k and kp*)


NtoNF[k_, kp_] := NtoNF[k, kp] = Block[{n = Length[k],
     active
     }, Sum[
     (* Extract the active part *)
     active = Transpose[Join[
        Extract[k, {#} & /@ subset[[1]]],
        Extract[kp, {#} & /@ subset[[2]]]
        ]];
        (* signs from anti-commuting active fermions to one end *)
     (-1)^Total[subset, 2]*
        NtoNFActive[ active[[2]](* s1 ~ s4 *) ][
         ##, (* k1~k4, i1~i4 *)
         Delete[k, {#} & /@ subset[[1]]],(* spectator \[Lambda] *)
         Delete[kp, {#} & /@ subset[[2]]](* spectator \[Lambda]p *)
         ] & @@ Flatten[active[[{1, 3}]]],
         (* All possible ways to select the active part *)
     {subset, selectionNtoN[n]}
     ]
    ];


(* ::Subsubsection:: *)
(*N to N+2*)


(*NtoN2F[k,kp] sums over all possible contractions computed by NtoNFActive[] 
and returns the  2n to 2n+2 matrix elements between a pair of monomials k and kp*)


ClearAll[NtoN2F]
NtoN2F[k_, kp_] := NtoN2F[k, kp] = Block[{nR = Length[kp],
     active
     }, Sum[
     (* Extract the active part *)
     active = Transpose[Join[
        Extract[k, {#} & /@ subset[[1]]],
        Extract[kp, {#} & /@ subset[[2]]]
        ]];
        (* signs from anti-commuting active fermions to one end *)
     (-1)^(Total[subset, 2] + 3 nR - 1)*
     NtoN2FActive[ active[[2]] (* s1 ~ s4 *)][
         ##,(* k1~k4, i1~i4 *)
         Delete[k, {#} & /@ subset[[1]]],(* spectator \[Lambda] *)
         Delete[kp, {#} & /@ subset[[2]]](* spectator \[Lambda]p *)
         ] & @@ Flatten[active[[{1, 3}]]],
         (* All possible ways to select the active part *)
     {subset, selectionNtoN2[nR]}
     ]
    ];


(* ::Section:: *)
(*Gauge interaction: active part*)


(*The principal value integral that gives I(a,b,a',b'). The result is 
exactly the same as summarized in (C.1.4).*)


pvint[0, 0] := 0;
pvint[a_, b_] := 
  pvint[a, b] = (a HarmonicNumber[a] + b HarmonicNumber[b] - 1)/(
    a + b) - HarmonicNumber[a + b - 1];


ClearAll[gauge]
gauge[a_?NumberQ, b_?NumberQ, ap_?NumberQ, bp_?NumberQ] /; 
   Min[a, ap] > Min[b, bp] := gauge[b, a, bp, ap];
gauge[a_?NumberQ, b_?NumberQ, ap_?NumberQ, bp_?NumberQ] /; 
   Min[a, b] > Min[ap, bp] := gauge[ap, bp, a, b];
gauge[a_?NumberQ, b_?NumberQ, 0, bp_?NumberQ] := gauge[0, bp, a, b];
gauge[0, b_?NumberQ, ap_?NumberQ, bp_?NumberQ] /; b > 2 :=
  
  gauge[0, b, ap, bp] = Gamma[ap + b + bp - 3]/(
   Gamma[ap] Gamma[b + bp - 2] (b - 1) (b - 2));
gauge[0, 2, ap_?NumberQ, bp_?NumberQ] /; bp > 0 :=
  
  gauge[0, 2, ap, bp] = 
   Gamma[ap + bp - 1]/(
    Gamma[ap] Gamma[bp]) (-HarmonicNumber[-1 + bp] + 
      HarmonicNumber[-2 + ap + bp]);
gauge[0, 2, ap_?NumberQ, 0] :=
  
  gauge[0, 2, ap, 0] = Gamma[-1 + ap]/Gamma[ap];
gauge[a_?NumberQ, b_?NumberQ, ap_?NumberQ, bp_?NumberQ] /; 
   a > 0 && b > 0 && ap > 0 && bp > 0 := 
  gauge[a, b, ap, bp] = Gamma[a + b + ap + bp + -3] Sum[
     Binomial[ap - 1, m1] Binomial[bp - 1, m2] (-1)^(m1 + m2)
      pvint[a + m1 - 1, b + m2 - 1],
     {m1, 0, ap - 1}, {m2, 0, bp - 1}
     ];


(* ::Chapter:: *)
(*Mass produce matrix elements (numeric Nc)*)


(* ::Section:: *)
(*Gram matrix*)


(*gramMatrix[states], NtoNMatrix[states] and NtoN2Matrix[statesL,statesR] put 
together the monomial matrix elements and the monomials' coefficient inside each 
primary state for a group of primary states and gives the full primary states' matrix 
elements. 
The input is a list of primary operators generated by stateset[dim] (or two lists in 
NtoN2Matrix where the in-states and out-states are different groups)
The output is the matrix <O,p|M|O,p'>/(2Pi 2p delta(p-p')), where M is the Gram matrix, interaction 
2n to 2n matrix and the interaction 2n to 2n+2 matrix, respectively.*)


(* Get a sign from taking the conjugate of O(x): fermions anti-commute, so one gets 
a sign (-1)^l whenever there is a psidag d^l psi in the primary operator. *)
ClearAll[totalSign]
totalSign[state_] /; state[[4]] > 1 :=
  totalSign[state[[1]]] + totalSign[state[[2]]];
totalSign[state_] /; state[[4]] == 1 := state[[3]];


ClearAll[gramMatrix]
gramMatrix[states_] := Block[{state1, state2, length,tab},
   length = Length[states]; tab = Table[
     state1 = states[[idx1]];
     state2 = states[[idx2]];
     If[idx1 < idx2 || state1[[5]] != state2[[5]], 0,
      (-1)^totalSign[state1](*(-1)^state2[[4]]\[ImaginaryI]^(state1[[
       5]]+state2[[5]])*)Sum[
         term1[[1]]*term2[[1]]*Block[{i = 1},
         (* AF[\[Lambda],\[Lambda]p,tensor], where \[Lambda] is a list of {k,s,i} for each d^k psi_i^s: 
		s=1 means psi and s=-1 means psidag *)
           AF[Flatten[Reap[
               
               Map[ MapThread[Sow[{##}] &, {#, {-1, 1}, {i, i++}}] &, 
                term1[[2]] ]
               ][[2]], 1],
            Flatten[Reap[
               
               Map[ MapThread[Sow[{##}] &, {#, {-1, 1}, {i, i++}}] &, 
                term2[[2]] ]
               ][[2]], 1] , 1 ] ],
               (* term1 and term2 has the form {coefficient, monomial's k vector} *)
         {term1, monoExpand[state1]},
         {term2, monoExpand[state2]}
         ]/Gamma[state1[[5]] + state2[[5]]]
      ],
     {idx1, length},
     {idx2, length}
     ];  
     tab = tab + Transpose[
      ReplacePart[tab, {i_, i_} :> 0]
      ] ];


(* ::Section:: *)
(*gauge interaction*)


NtoNMatrix[states_] := Block[{tab,state1, state2, length},
   length = Length[states]; tab=Table[
     state1 = states[[idx1]];
     state2 = states[[idx2]];
     If[idx1 < idx2, 0,
      (-1)^totalSign[state1](*(-1)^state2[[4]]ii^(state1[[5]]+state2[[
       5]])*)Sum[
         term1[[1]]*term2[[1]]*Block[{i = 1},
         (* NtoNF[\[Lambda],\[Lambda]p], where \[Lambda] is a list of {k,s,i} for each d^k psi_i^s: 
		s=1 means psi and s=-1 means psidag *)
           NtoNF[Flatten[Reap[
               
               Map[ MapThread[Sow[{##}] &, {#, {-1, 1}, {i, i++}}] &, 
                term1[[2]] ]
               ][[2]], 1],
            Flatten[Reap[
               
               Map[ MapThread[Sow[{##}] &, {#, {-1, 1}, {i, i++}}] &, 
                term2[[2]] ]
               ][[2]], 1] ] ],
               (* term1 and term2 has the form {coefficient, monomial's k vector} *)
         {term1, monoExpand[state1]},
         {term2, monoExpand[state2]}
         ]/Gamma[state1[[5]] + state2[[5]] - 1](* norm factor \[CapitalGamma](Delta1+Delta2-1) *)
      ],
     {idx1, length},
     {idx2, length}
     ];
     tab = tab + Transpose[
      ReplacePart[
       tab, {i_, i_} :> 
        0]
      ] ];


ClearAll[NtoN2Matrix]
NtoN2Matrix[statesL_, statesR_] := 
  Block[{state1, state2, lengthL, lengthR},
   lengthL = Length[statesL];
   lengthR = Length[statesR]; Table[
     state1 = statesL[[idx1]];
     state2 = statesR[[idx2]];
     (-1)^totalSign[state1](*(-1)^state2[[4]]ii^(state1[[5]]+state2[[
      5]])*)Sum[
        term1[[1]]*term2[[1]]*Block[{i = 1},
        (* NtoN2F[\[Lambda],\[Lambda]p], where \[Lambda] is a list of {k,s,i} for each d^k psi_i^s: 
		s=1 means psi and s=-1 means psidag *)
          NtoN2F[Flatten[Reap[
              
              Map[ MapThread[Sow[{##}] &, {#, {-1, 1}, {i, i++}}] &, 
               term1[[2]] ]
              ][[2]], 1],
           Flatten[Reap[
              
              Map[ MapThread[Sow[{##}] &, {#, {-1, 1}, {i, i++}}] &, 
               term2[[2]] ]
              ][[2]], 1]  ] ],
              (* term1 and term2 has the form {coefficient, monomial's k vector} *)
        {term1, monoExpand[state1]},
        {term2, monoExpand[state2]}
        ]/Gamma[state1[[5]] + state2[[5]] - 1],(* norm factor \[CapitalGamma](Delta1+Delta2-1) *)
     {idx1, lengthL},
     {idx2, lengthR}
     ]];


(* ::Chapter:: *)
(*Run*)


file="QCD_N"<>ToString[Nc]<>"_D"<>ToString[\[CapitalDelta]max]


(*Generate primary operators below \[CapitalDelta]max, group by number of fermions 2n*)
primaries = GroupBy[
   Flatten[stateSet /@ Range[\[CapitalDelta]max], 1],
   #[[4]] &];


(*Compute the Gram matrix for each fermion number sector*)
timeGramMatrix = AbsoluteTiming[gramMatrices=gramMatrix/@primaries;][[1]];
Print[
	"The Gram Matrix took ",
	timeGramMatrix,
	" seconds"
]


indepSet=Block[{rowReduced,pos},Map[
	Function[{gram},
		rowReduced=gram//RowReduce//Transpose;
		Catch[
			pos=FirstPosition[#,x_?NumberQ/;x!=0,-1]&/@rowReduced//Flatten;
			Block[{i=0},
				Reap[MapIndexed[If[#1>i,i=#1;Sow[#2[[1]]]]&,pos]][[2]]//Flatten
			] ]
	],gramMatrices] ]//DeleteCases[{}];


primaries=Table[
	nPairs->primaries[nPairs][[indepSet[nPairs]]],
	{nPairs,Length[indepSet]}
]//Association;
gramMatrices=Table[
	nPairs->gramMatrices[nPairs][[indepSet[nPairs],indepSet[nPairs]]],
	{nPairs,Length[indepSet]}
]//Association;


Put[Definition[primaries],file]


PutAppend[Definition[gramMatrices],file]


(*Compute the 2n to 2n matrix for each fermion number sector*)
timeNtoNMatrix = AbsoluteTiming[NtoNMatrices=NtoNMatrix/@primaries;
(*"N to N"*)
][[1]];
Print[
	"The interaction N to N Matrix took ",
	timeNtoNMatrix,
	" seconds."
]
PutAppend[Definition[NtoNMatrices],file];


(*Compute the 2n to 2n+2 matrix for each fermion number sector, n=1 and n=2*)
timeNtoNPlus2Matrix = AbsoluteTiming[
	NtoN2Matrices = Table[
	   n -> NtoN2Matrix[ primaries[n], primaries[n + 1]],
	   {n, Keys[primaries][[;; -2]]}
	   ] // Association;(*"N to N+2"*)
   ][[1]];
Print[
	"The interaction N to N+2 Matrix took ",
	timeNtoNPlus2Matrix,
	" seconds."
];
PutAppend[Definition[NtoN2Matrices],file];

Print[
	"save file at ",
	file
]



