(* ::Package:: *)

BeginPackage["susyQMinusCode`"]


computeQMinusMatrix::usage=
"computeQMinusMatrix[suffix_,basisN1SUSY_,fdr_]
computes the matrix elements of Q- term with respect to the 
N1 SUSY basis given as argument basisN1SUSY_ and store them in 
folder fdr_.
The first argument suffix is only used to decide the output 
file name and does not affect the calculation."


matQMinus::usage


Begin["`Private`"]


(* ::Section:: *)
(*External functions*)


(* computeQMinusMatrix is the main wrapper function, which runs through the
elements of the basis and calls primBlock to make the matrix elements 
between primaries.  *)


computeQMinusMatrix[suffix_,basisMixon_,fdr_]:=With[{t1=AbsoluteTime[]},
	matQMinus=With[{
		(* Read the number nBMax of boson and nFMax of fermion primaries in the mixon basis *)
		nBMax=Dimensions[basisMixon][[1]]-1,
		nFMax=Dimensions[basisMixon][[2]]-1},
		Table[
		(* The supercharge Q- can only change the boson number
		and the fermion number by +/-1.  By Hermiticity, we can assume a scalar is
		absorbed and a fermion is produced  *)
			If[nBL-1==nBR&&nFL+1==nFR,
				Catch[ArrayFlatten[Outer[
				(* Apply primBlock to each block of matrix elements with a given
				in and out fermion and boson number, nBL, nBR, nFL, & nFR. 
				If there are no primaries in the block, return the empty set. *)
					primBlock,
					If[Length[#]==0,Throw[{}],#]&@basisMixon[[nBL+1,nFL+1]],
					If[Length[#]==0,Throw[{}],#]&@basisMixon[[nBR+1,nFR+1]],
				1 ] ] ],
				(*  If the boson & fermion numbers don't change by +1 & -1,
				respectively, set the matrix elements for the block to zero*)
				SparseArray[{},{stateCount[basisMixon[[nBL+1,nFL+1]]],
					stateCount[basisMixon[[nBR+1,nFR+1]]] }] 
			],
			{nBL,0,nBMax},
			{nBR,0,nBMax},
			{nFL,0,nFMax},
			{nFR,0,nFMax}
		]
	];
	
	(* Fill in the remaining entries by using Hermiticity *)
	Block[{
		nBMax=Dimensions[basisMixon][[1]]-1,
		nFMax=Dimensions[basisMixon][[2]]-1,
		nBR,nFR,block
		},
		Do[
			nBR=nBL+1;
			nFR=nFL-1;
			block=matQMinus[[nBR+1,nBL+1,nFR+1,nFL+1]];
			matQMinus[[nBL+1,nBR+1,nFL+1,nFR+1]]=If[block!={},
				Transpose[block],{}],
			{nBL,0,nBMax-1},
			{nFL,1,nFMax}
		]
	];
	(*Clean up the matrix*)
	matQMinus=Replace[matQMinus,{{}..}->{},{4}];
	Print["t = ",AbsoluteTime[]-t1];
	
	SetDirectory[fdr];
	Save["MatrixQMinusD"<>ToString[suffix],matQMinus];
]


(* ::Section:: *)
(*Internal functions*)


(*  primBlock is a function that makes the Q- matrix elements.  This function acts on the in and out basis elements.
For instance, say you feed primBlock 
primBlock[basisMixon[[nBL+1,nFL+1]][[1]],basisMixon[[nBR+1,nFR+1]]][[1]]
with nBL=0, nBR=1, nFL=1, nFR=0.
Then the in state is one fermion and the out state is one boson. 
In this case,
level1=basisMixon[[nBL+1,nFL+1]][[1]]=\[LeftAssociation]"nB"\[Rule]0,"degB"\[Rule]0,"nF"\[Rule]1,"degF"\[Rule]0,"l"\[Rule]0,"states"\[Rule]{{{{1.`}}}}\[RightAssociation]
and 
level2=basisMixon[[nBR+1,nFR+1]][[1]]=\[LeftAssociation]"nB"\[Rule]1,"degB"\[Rule]0,"nF"\[Rule]0,"degF"\[Rule]0,"l"\[Rule]0,"states"\[Rule]{{{{1.`}}}}\[RightAssociation]
The function created by primBlock calls monomialBlock to make the matrix elements for monomials, and
adds them together (after multiplying by some prefactors) in the combination dictated by the primary
in the arguments level1 and level2 *)


primBlock=Function[{level1,level2},
	With[{
		dnB=-1,dnF=1,
		lL=level1["l"],lR=level2["l"],
		degBL=level1["degB"],degBR=level2["degB"],
		degFL=level1["degF"],degFR=level2["degF"],
		nBL=level1["nB"],nFL=level1["nF"]
	},
	(* Take the primary state in the `in' and `out' primary basis element (level1 and level2), 
	and sum over monomial coefficients ck,ck' times monomial matrix elements mkk'
	ck*mkk'*ck'
	ck = #1[[kL+1]]
	ck'= #2[[kR+1]]
	mkk'=monomialBlock[...]
	At the end, multiply by factor = Sqrt[ Gamma[2\[CapitalDelta]]Gamma[2\[CapitalDelta]p] ] * (-1)^(\[CapitalDelta]-\[CapitalDelta]p-1/2) / Gamma[\[CapitalDelta]+\[CapitalDelta]p-1], which
	combines the factors from the Fourier transforms of 2- and 3-point functions. *)
		SparseArray@Outer[
			Total[Table[
				Flatten[#1[[kL+1]]].
				monomialBlock[
					{nBL},{nFL},{degBL+kL,degBR+kR},
					{degFL+lL-kL,degFR+lR-kR}
				].
				Flatten[#2[[kR+1]]],
			{kL,0,lL},{kR,0,lR}],2]&,
		level1["states"],
		level2["states"],
		1]*factor[nBL+3/2nFL+degBL+degFL+lL,(nBL+dnB)+3/2(nFL+dnF)+degBR+degFR+lR]
	]
];


(* ::Section:: *)
(*Matrix contracting an array of monomials*)


(*This is a wrapper to apply Q- to the monomials.  

The function monomialsBoson takes boson number nB and degree degB and produces a list of monomials - this
function defines a canonical ordering (that we always use) of monomials with the same particle number and degree.
Similarly for monomialsFermion.

The output of monomialBlock is a matrix of qMinus applied
to an `in' list and an `out' list of all the bincounts of all the monomials produced by monomialsBoson and
monomialsFermion (and their combinations) *)


ClearAll[monomialBlock]
monomialBlock[{nBL_},{nFL_},{degB1_,degB2_},{degF1_,degF2_}]:=
monomialBlock[{nBL},{nFL},{degB1,degB2},{degF1,degF2}]=With[
	{
		a1List=cfBinCount[#,Max[degB1,degB2]+1]&/@monomialsBoson[nBL,degB1],
		a2List=cfBinCount[#,Max[degB1,degB2]+1]&/@monomialsBoson[(*nBR*)nBL-1,degB2],
		b1List=cfBinCount[#,Max[degF1,degF2]+1]&/@monomialsFermion[nFL,degF1],
		b2List=cfBinCount[#,Max[degF1,degF2]+1]&/@monomialsFermion[(*nFR*)nFL+1,degF2]
	},
	Outer[
		qMinus,
		(* Here, we combine the table of boson bincounts and fermion bincounts to make tables of all
		the "mixon" bincounts*)
		Flatten[Outer[List,a1List,b1List,1],1],
		Flatten[Outer[List,a2List,b2List,1],1],
	1]//SparseArray
]


(* ::Section:: *)
(*Monomial Contractions*)


(*
qMinus[] computes the matrix element of Q- with two monomials. 
	
	Most of the work involved is efficiently doing the sum over all allowed contractions of the interaction
	with the external state, i.e. the sum over kvec and kvec' is too slow if we do it by brute force. But most of
	the entries are empty, and many terms are equivalent since they are related by symmetry. So we instead
	look at the bincounts of the in and out states and ask when can k's be removed from the in and out states
	so that what remains is the same on both sides; and we group together equivalent terms and multiply
	by a symmetry factor.  The generating function factors g(ki,si) from appendix D are written in terms of the function "residue". 
	
	The inputs of yukawa[] are the occupation number representation of k and k'.
	a -> scalar k from in state
	b -> fermion k from in state
	ap -> scalar k' from out state
	bp -> fermion k' from out state*)


qMinus[{a_,b_},{ap_,bp_}]:=Block[
	{aBar,bpBar,k1,k2,s1=-1,s2=+1,residue,symFactor,perm},
	(* Set the bincount aBar for the boson contraction from the in state and bpBar for the fermion contraction from the out state.
	(By Hermiticity, we can assume WLOG that the contractions are in these directions)
	Because the boson and fermion numbers change by +/-1, the in and out monomials must differ by exactly one bincount
	in exactly one bin, so this fixes where the boson and fermion interactions are contracted - i.e. the contractions are
	not "free".   *)
	aBar=Ramp[a-ap];
	bpBar=Ramp[bp-b];
	
	If[Total[aBar]!=1||Total[bpBar]!=1,Return[0]];
	
	k1=cfBinReconstruct[aBar]//First;
	k2=cfBinReconstruct[bpBar]//First;
	(*Here is the (hatted) generating function for the Q- term*)
	residue=Sqrt[(*(1/2)*) k2 (k2+1)/k1]*Which[k1==k2+1,1,k1==k2,-1,True,0];
	
	(*The "symmetry factor" here is just the usual sqrt(n!) factor from the matrix elements of annihilation operators
	<n|a|n+1> for simple harmonic oscillator modes*)
	symFactor=Sqrt[a[[k1]]];
	perm=(-1)^(Total[Take[bp,k2]]-1);
	s1*residue*symFactor*perm
]


factor[\[CapitalDelta]_,\[CapitalDelta]p_]:=(-1)^(\[CapitalDelta]+\[CapitalDelta]p+1/2) (*\[ImaginaryI]^(3/2)*) (*(1/2)*) Sqrt[Gamma[2\[CapitalDelta]]Gamma[2\[CapitalDelta]p]]/Gamma[\[CapitalDelta]+\[CapitalDelta]p+1/2]


(* ::Subsection:: *)
(*Utility functions*)


stateCount[lstOfLevels_]:=Total[Length[#states]&/@lstOfLevels]


(* 
	c = cfBinCount[k vector] computes the bin counts of vector \vec{k} so that
	for each k in \vec{k} the k'th element of c, c[[k]] is the number of copies
	of k in \vec{k}. If \vec{k} does not have k, then c[[k]]=0.

	One can use this function to generate bin counts of a monomial \vec{k} to
	send in yukawa[]. The function does not care whether the k vector comes from
	the scalar or fermion sector. So one has to separate the monomial into scalar
	monomial times fermion monomial and bin count separately.
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
	Suppose 'c' is a bin count of some \vec{k} vector, cfBinReconstruct[c]
	reverses the bin count and reconstructs \vec{k}.

	The vector \vec{k} is built up so that for each k\[Element]\vec{k} (also
	means c[[k]]>0) the reconstructed \vec{k} contains exactly c[[k]] copies of
	k. 

	The reconstructed \vec{k} has fixed order: the smaller ones first and larger
	ones later.

	If we know 'c' contains only 0 and 1's, then the result of
	cfBinReconstruct[c] is equivalent to Mathematica's built in function
	Position[c,1] up to some bracket conventions. In this case,
	cfBinReconstruct[c] is 3~4 times faster than Position[c,1]. If 'c' can have
	elements greater than 1, then Position[] alone cannot handle it while
	cfBinReconstruct[c] alone can still handle the case with no slow down.
 *)
cfBinReconstruct=Compile[
	{
		{c,_Integer,1}
	},
	Module[
		{i=1,j=1,k=1,
			(* Total[c] is the total number of particles, 
			also the total length of \vec{k} *)
			length=Total[c],reconstruct
		},
		(* prepares an all-zero vector of total length of \vec{k}
			the zeros will be filled by the k's
			so 'reconstruct' will eventually be the \vec{k}
		*)
		reconstruct=Table[0,{length}];
		For[
			(* k iterates c[[k]]. 
			i is the position in vector 'reconstruct' that will be filled next 
			loop finishes when the vector is full
			*)
			k=1,i<=length,k++,
			For[
				(* Effectively this loop fills 
				reconstruct[[i]] through reconstruct[[i+c[[k]]-1]]
				by k,
				then push i to i+c[[k]] *)
				j=1,j<=c[[k]],j++,
				(* filling the i'th element of 'reconstruct' *)
				reconstruct[[i]]=k;i++
			]
		];
		reconstruct
	],
	CompilationTarget->"C",
	CompilationOptions->{"ExpressionOptimization" -> True}
]


ClearAll[monomialsBoson]
monomialsBoson[n_,deg_]:=monomialsBoson[n,deg]=IntegerPartitions[deg+n,{n}];
ClearAll[monomialsFermion]
monomialsFermion[n_,deg_]:=monomialsFermion[n,deg]=(#+Reverse[Range[n]-1])&/@monomialsBoson[n,deg+n-n (n+1)/2]


(* ::Section:: *)
(*End*)


End[]


EndPackage[]
