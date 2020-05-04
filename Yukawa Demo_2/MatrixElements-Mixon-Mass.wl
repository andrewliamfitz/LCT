(* ::Package:: *)

BeginPackage["mixonMassCode`"]


computeMixonMassMatrices::usage=
"computeMixonMassMatrices[suffix_,basisMixon_,fdr_]
computes the matrix elements of scalar and fermion mass terms
with respect to the mixon basis given as argument basisMixon_ 
and store them in folder fdr_.
The first argument suffix is only used to decide the output 
file name and does not affect the calculation."


matScalarMass::usage


matFermionMass::usage


Begin["`Private`"]


(* ::Section:: *)
(*External functions*)


(* computeMixonMassMatrices is the main wrapper function, which runs through the
elements of basisMixon_ and calls primBlockNtoN to make the mass term matrix elements 
between primaries. *)


computeMixonMassMatrices[suffix_,basisMixon_,fdr_]:=With[{t1=AbsoluteTime[]},
	Print["@ scalar mass:"];
	(* First construct matrix elements for the scalar mass term *)
	matScalarMass=With[{
	(* Read the number nBMax of boson and nFMax of fermion primaries in the mixon basis *)
		nBMax=Dimensions[basisMixon][[1]]-1,
		nFMax=Dimensions[basisMixon][[2]]-1},
		Table[
		(* The mass term must preserve the number of bosons and fermions, so the number of
		incoming bosons and fermions (nBL and nFL) must match the number of outgoing bosons
		and fermions (nBR and nFR) *)
			If[nBL==nBR&&nFL==nFR,
				Catch[ArrayFlatten[Outer[
				(* Apply primBlockNtoN to each block of matrix elements with a given
				incoming and outgoing boson and fermion number (nBL=nBR, nFL=nFR). 
				If there are no primaries in the block, return the empty set.
				The argument of primBlockNtoN (in this case, scalarMassMonomialBlock)
				is itself a function, specifying the particular "interaction" for the
				matrix elements *)
					primBlockNtoN[scalarMassMonomialBlock],
					If[Length[#]==0,Throw[{}],#]&@basisMixon[[nBL+1,nFL+1]],
					If[Length[#]==0,Throw[{}],#]&@basisMixon[[nBR+1,nFR+1]],
				1 ] ] ],
				(* If the boson & fermion numbers don't match,
				 set the matrix elements for the block to zero *)
				SparseArray[{},{stateCount[basisMixon[[nBL+1,nFL+1]]],
					stateCount[basisMixon[[nBR+1,nFR+1]]] }] 
			],
			{nBL,0,nBMax},
			{nBR,0,nBMax},
			{nFL,0,nFMax},
			{nFR,0,nFMax}
		]
	];
	(* Clean up the matrix *)
	matScalarMass=Replace[matScalarMass,{{}..}->{},{4}];
	Print["t = ",AbsoluteTime[]-t1];
	
	Print["@ fermion mass:"];
	(* Repeat this procedure for the fermion mass term *)
	matFermionMass=With[{
	(* Read the number nBMax of boson and nFMax of fermion primaries in the mixon basis *)
		nBMax=Dimensions[basisMixon][[1]]-1,
		nFMax=Dimensions[basisMixon][[2]]-1},
		Table[
		(* The mass term must preserve the number of bosons and fermions, so the number of
		incoming bosons and fermions (nBL and nFL) must match the number of outgoing bosons
		and fermions (nBR and nFR) *)
			If[nBL==nBR&&nFL==nFR,
				Catch[ArrayFlatten[Outer[
				(* Apply primBlockNtoN to each block of matrix elements with a given
				incoming and outgoing boson and fermion number (nBL=nBR, nFL=nFR). 
				If there are no primaries in the block, return the empty set.
				The argument of primBlockNtoN (in this case, fermionMassMonomialBlock)
				is itself a function, specifying the particular "interaction" for the
				matrix elements *)
					primBlockNtoN[fermionMassMonomialBlock],
					If[Length[#]==0,Throw[{}],#]&@basisMixon[[nBL+1,nFL+1]],
					If[Length[#]==0,Throw[{}],#]&@basisMixon[[nBR+1,nFR+1]],
				1 ] ] ],
				(* If the boson & fermion numbers don't match,
				 set the matrix elements for the block to zero *)
				SparseArray[{},{stateCount[basisMixon[[nBL+1,nFL+1]]],
					stateCount[basisMixon[[nBR+1,nFR+1]]] }] 
			],
			{nBL,0,nBMax},
			{nBR,0,nBMax},
			{nFL,0,nFMax},
			{nFR,0,nFMax}
		]
	];
	(* Clean up the matrix *)
	matFermionMass=Replace[matFermionMass,{{}..}->{},{4}];
	Print["t = ",AbsoluteTime[]-t1];
	
	(* Save the resulting matrix elements, with the filenames set by suffix_ and the directory set by fdr_ *)
	SetDirectory[fdr];
	Save["MatrixScalarMassMixonD"<>ToString[suffix],matScalarMass];
	Save["MatrixFermionMassMixonD"<>ToString[suffix],matFermionMass];
]


(* Function for counting the number of basis states with a given number of bosons and fermions *)
stateCount[lstOfLevels_]:=Total[Length[#states]&/@lstOfLevels]


(* ::Subsection:: *)
(*primary dimension factor*)


factor[\[CapitalDelta]_,\[CapitalDelta]p_]:=factor[\[CapitalDelta],\[CapitalDelta]p]=Sqrt[ Gamma[2\[CapitalDelta]]Gamma[2\[CapitalDelta]p] ] * (-1)^(\[CapitalDelta]-\[CapitalDelta]p) / Gamma[\[CapitalDelta]+\[CapitalDelta]p-1];


(* ::Section:: *)
(*Matrix contracting an array of primaries*)


(* For a given operator (here, scalarMassMonomialBlock or fermionMassMonomialBlock),
primBlockNtoN makes a function that makes the matrix elements.  This function acts on the in and out basis elements.
For instance, say you feed primBlock 
primBlock[basisMixon[[nBL+1,nFL+1]][[1]],basisMixon[[nBR+1,nFR+1]]][[1]]
with nBL=0, nBR=1, nFL=0, nFR=1.
Then the in and out states are just one fermion. 
In this case,
level1=basisMixon[[nBL+1,nFL+1]][[1]]=\[LeftAssociation]"nB"\[Rule]0,"degB"\[Rule]0,"nF"\[Rule]1,"degF"\[Rule]0,"l"\[Rule]0,"states"\[Rule]{{{{1.`}}}}\[RightAssociation]
and level2 is the same as level1.
The function created by primBlock calls monomialBlock to make the matrix elements for monomials, and
adds them together (after multiplying by some prefactors) in the combination dictated by the primary
in the arguments level1 and level2 *)


primBlockNtoN[contraction_]=Function[{level1,level2},
	With[{
		lL=level1["l"],lR=level2["l"],
		degBL=level1["degB"],degBR=level2["degB"],
		degFL=level1["degF"],degFR=level2["degF"],
		nB=level1["nB"],nF=level2["nF"]
	},
	
		SparseArray@Outer[
			Total[Table[
				Flatten[#1[[kL+1]]].
				contraction[
					nB,nF,{degBL+kL,degBR+kR},
					{degFL+lL-kL,degFR+lR-kR}
				].
				Flatten[#2[[kR+1]]],
			{kL,0,lL},{kR,0,lR}],2]&,
		level1["states"],
		level2["states"],
		1]*factor[nB+3/2nF+degBL+degFL+lL,nB+3/2nF+degBR+degFR+lR]
	]
];


(* ::Section:: *)
(*Matrix contracting an array of monomials*)


(*The following two functions (scalarMassMonomialBlock and fermionMassMonomialBlock) are wrappers
to compute the scalar and fermion mass term matrix elements to the monomials - at the end of the routine they
apply scalarMassMixonContraction or fermionMassMixonContraction, respectively, to the
bincounts a1,a2,b1,b2 of the in and out monomials.

The function monomialsBoson takes boson number nB and degree degB and produces a list of monomials - this
function defines a canonical ordering (that we always use) of monomials with the same particle number and degree.
Similarly for monomialsFermion.

The output of scalarMassMonomialBlock and fermionMassMonomialBlock are matrices of scalarMassMixonContraction and
fermionMassMixonContraction, respectively, applied
to an `in' list and an `out' list of all the bincounts of all the monomials produced by monomialsBoson and
monomialsFermion (and their combinations) *)


(* ::Subsection:: *)
(*scalar mass term*)


ClearAll[scalarMassMonomialBlock]
scalarMassMonomialBlock[nB_,nF_,{degB1_,degB2_},{degF1_,degF2_}]:=
scalarMassMonomialBlock[nB,nF,{degB1,degB2},{degF1,degF2}]=With[
	{
		a1List=cfBinCount[#,Max[degB1,degB2]+1]&/@monomialsBoson[nB,degB1],
		a2List=cfBinCount[#,Max[degB1,degB2]+1]&/@monomialsBoson[nB,degB2],
		b1List=cfBinCount[#,Max[degF1,degF2]+1]&/@monomialsFermion[nF,degF1],
		b2List=cfBinCount[#,Max[degF1,degF2]+1]&/@monomialsFermion[nF,degF2]
	},
	Outer[
		scalarMassMixonContraction,
		(* Here, we combine the table of boson bincounts and fermion bincounts to make tables of all
		the "mixon" bincounts*)
		Flatten[Outer[List,a1List,b1List,1],1],
		Flatten[Outer[List,a2List,b2List,1],1],
	1]//SparseArray
]


(* ::Subsection:: *)
(*fermion mass term*)


ClearAll[fermionMassMonomialBlock]
fermionMassMonomialBlock[nB_,nF_,{degB1_,degB2_},{degF1_,degF2_}]:=
fermionMassMonomialBlock[nB,nF,{degB1,degB2},{degF1,degF2}]=With[
	{
		b1List=cfBinCount[#,Max[degF1,degF2]+1]&/@monomialsFermion[nF,degF1],
		b2List=cfBinCount[#,Max[degF1,degF2]+1]&/@monomialsFermion[nF,degF2],
		a1List=cfBinCount[#,Max[degB1,degB2]+1]&/@monomialsBoson[nB,degB1],
		a2List=cfBinCount[#,Max[degB1,degB2]+1]&/@monomialsBoson[nB,degB2]
	},
	Outer[
		(* Here, we combine the table of boson bincounts and fermion bincounts to make tables of all
		the "mixon" bincounts*)
		fermionMassMixonContraction,
		Flatten[Outer[List,a1List,b1List,1],1],
		Flatten[Outer[List,a2List,b2List,1],1],
	1]//SparseArray
]


(* ::Section:: *)
(*Individual monomial elements*)


(* ::Subsection:: *)
(*Scalar mass term*)


(* 
	scalarMassScalarContraction[] computes the matrix element of the scalar mass term between two all-scalar monomials.
	
	Most of the work involved is efficiently doing the sum over all allowed contractions of the "interaction"
	with the external states, i.e. the sum over kvec and kvec' is too slow if we do it by brute force. But most of
	the contractions vanish, and many terms are equivalent since they are related by symmetry. So we instead
	look at the bin counts of the in and out states and ask when can individual k's be removed from the in and out states
	so that the remaining vectors are the same on both sides; and we group together equivalent terms and multiply
	by a symmetry factor.
	
	The inputs of scalarMassScalarContraction[] are the occupation number representation of the all-scalar monomials k and k',
	generated by cfBinCount[] (i.e. a=cfBinCount[k])
	a -> scalar k from in state
	ap -> scalar k' from out state	
 *)
scalarMassScalarContraction[{a__,0},{ap__,0}]:=scalarMassScalarContraction[{a},{ap}]
scalarMassScalarContraction[a_,ap_]:=scalarMassScalarContraction[a,ap]=Block[
	{
		diff,ki,kpj
	},
	diff=a-ap;
	Switch[
		(* The bin counts can change by +/-2 or by 0.  If it changes by 2, then this fixes which ki and kj' contract 
		with the mass term - i.e. the contraction is not "free".
		If it changes by 0, then the mass term can contract with any ki and kj' as long as they are equal - i.e. the
		contraction is "free".  
		*)
		Total[diff//Abs],
		(*Deal with the "free" case first, where we simply obtain a symmetry factor corresponding to the number of particles*)
		0,(ap//Total),
		(*If the difference in bin counts is +/-2, the Subscript[k, i] and Subscript[k, j]' are fixed, and we can compute the matrix element from eq. (7.41)
		in the paper*)
		2,
		ki=FirstPosition[diff,1]//First;
		kpj=FirstPosition[diff,-1]//First;
		Sqrt[ If[ki>kpj,kpj/ki,ki/kpj] * a[[ki]]*ap[[kpj]]  ],
		
		_,0
	]
]
SetAttributes[scalarMassScalarContraction,Orderless];


(* 
	scalarMassMixonContraction[] computes the matrix element of the scalar mass term between two mixed
	scalar-fermion monomials.
	
	Because the fermions are all "spectators", the fermion monomial bin counts of the in and out states must
	match, otherwise the matrix element vanishes. We then compute the contraction of the scalar monomials
	with the mass term using scalarMassScalarContraction[].
	
	The inputs of scalarMassMixonContraction[] are the occupation number representation of the scalar
	monomials kB and kB' and fermion monomials kF and kF', generated by cfBinCount[] (i.e. a=cfBinCount[kB])
	a -> scalar kB from in state
	b -> fermion kF from in state
	ap -> scalar kB' from out state
	bp -> fermion kF' from out state
 *)
scalarMassMixonContraction[{a_,b_},{ap_,bp_}]:=If[
	b!=bp,0,
	scalarMassScalarContraction[a,ap]
]


(* ::Subsection:: *)
(*fermion mass term*)


(* 
	fermionMassFermionContraction[] computes the matrix element of the fermion mass term between two all-fermion monomials.
	
	Most of the work involved is efficiently doing the sum over all allowed contractions of the "interaction"
	with the external states, i.e. the sum over kvec and kvec' is too slow if we do it by brute force. But most of
	the contractions vanish, and many terms are equivalent since they are related by symmetry. So we instead
	look at the bin counts of the in and out states and ask when can individual k's be removed from the in and out states
	so that the remaining vectors are the same on both sides; and we group together equivalent terms and multiply
	by a symmetry factor.
	
	The inputs of fermionMassFermionContraction[] are the occupation number representation of the all-fermion monomials k and k',
	generated by cfBinCount[] (i.e. b=cfBinCount[k])
	b -> fermion k from in state
	bp -> fermion k' from out state	
 *)
fermionMassFermionContraction[{b__,0},{bp__,0}]:=fermionMassFermionContraction[{b},{bp}]
fermionMassFermionContraction[b_,bp_]:=fermionMassFermionContraction[b,bp]=Block[
	{
		diff,ki,kpj,i,j
	},
	diff=b-bp;
	(1/2)*Switch[
		(* The bin counts can change by +/-2 or by 0.  If it changes by 2, then this fixes which ki and kj' contract 
		with the mass term - i.e. the contraction is not "free".
		If it changes by 0, then the mass term can contract with any ki and kj' as long as they are equal - i.e. the
		contraction is "free".  
		*)
		Total[diff//Abs],
		(*Deal with the "free" case first, where we simply obtain a symmetry factor corresponding to the number of particles*)
		0,(bp//Total),
		(*If the difference in bin counts is +/-2, the Subscript[k, i] and Subscript[k, j]' are fixed, and we can compute the matrix element from eq. (8.19)
		in the paper*)
		2,
		ki=FirstPosition[diff,1]//First;
		i=Total[Take[b,ki]];
		kpj=FirstPosition[diff,-1]//First;
		j=Total[Take[bp,kpj]];
		Sqrt[ If[ki<kpj,ki (ki+1)/(kpj(kpj+1)),kpj (kpj+1)/(ki(ki+1))]  ]*(-1)^(i-j),
		
		_,0
	]
]
SetAttributes[fermionMassFermionContraction,Orderless];


(* 
	fermionMassMixonContraction[] computes the matrix element of the fermion mass term between two mixed
	scalar-fermion monomials.
	
	Because the scalars are all "spectators", the scalar monomial bin counts of the in and out states must
	match, otherwise the matrix element vanishes. We then compute the contraction of the fermion monomials
	with the mass term using fermionMassFermionContraction[].
	
	The inputs of fermionMassMixonContraction[] are the occupation number representation of the scalar
	monomials kB and kB' and fermion monomials kF and kF', generated by cfBinCount[] (i.e. a=cfBinCount[kB])
	a -> scalar kB from in state
	b -> fermion kF from in state
	ap -> scalar kB' from out state
	bp -> fermion kF' from out state
 *)
fermionMassMixonContraction[{a_,b_},{ap_,bp_}]:=If[
	a!=ap,0,
	fermionMassFermionContraction[b,bp]
]


(* ::Section::Closed:: *)
(*Utility functions*)


(*
	c = cfBinCount[Kvec_,max_] computes the bin counts of vector Kvec={k1,...,kn},
	so that for each possible entry ki the ki'th element of c (c[[ki]]) is the number
	of copies of ki in Kvec. If Kvec does not contain ki, then c[[ki]]=0. The argument
	max_ sets the maximum value of ki to count the number of copies (i.e. the length of c)

	Ex: cfBinCount[{3,3,1,1,1},4] = {3,0,2,0} (i.e. c[[1]]=3, c[[2]]=0, c[[3]]=2, c[[4]]=0)

	The function does not distinguish whether the vector Kvec refers to a monomial in
	the scalar or fermion sector. So one has to separate a mixed scalar-fermion monomial
	into an all-scalar monomial and an all-fermion monomial and bin count each separately.
*)
cfBinCount=Compile[
	{{k,_Integer,1},{max,_Integer}},
	Module[
		{lst},
		lst=Table[0,{max}];
		Scan[
			lst[[#]]++&,k
		];
		lst
	],
	CompilationTarget->"C"
];


(*  
	The function monomialsBoson[nB_,degB_] produces a list of all monomials with a set number of
	bosons nB and degree degB - this function defines a canonical ordering (that we always use)
	of monomials with the same particle number and degree. Similarly for monomialsFermion[nF_,degF_].
*)
ClearAll[monomialsBoson]
monomialsBoson[n_,deg_]:=monomialsBoson[n,deg]=IntegerPartitions[deg+n,{n}];
ClearAll[monomialsFermion]
monomialsFermion[n_,deg_]:=monomialsFermion[n,deg]=(#+Reverse[Range[n]-1])&/@monomialsBoson[n,deg+n-n (n+1)/2]


(* ::Section:: *)
(*End*)


End[]


EndPackage[]
