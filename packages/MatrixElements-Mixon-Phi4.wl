(* ::Package:: *)

(* ::Chapter::Closed:: *)
(*Utility functions*)


BeginPackage["utilities`"]


flattenMixonMatrix::usage


flattenMixonStates::usage


cfBinCount::usage


cfBinReconstruct::usage


monomialsBoson::usage


monomialsFermion::usage


Begin["`Private`"]


takeNonEmpty[mat_] := Block[
   	{flattened = Flatten[mat, {{1, 3}, {2, 4}}], idxNull, i = 0},
   	idxNull = Position[Diagonal[flattened], {}];
   	(*Delete[Transpose[Delete[flattened,idxNull]],idxNull]*)
   	
   Fold[Drop[#1, #2 - i, #2 - (i++)] &, flattened, idxNull]
   ];
flattenMixonMatrix[mat_] := Block[
   {matNonEmpty = mat//takeNonEmpty, dims,
    rows, cols, res},
   dims = Map[Dimensions, matNonEmpty, {2}];
   rows = Prepend[dims[[;; , 1, 1]] // Accumulate, 0];
   cols = Prepend[dims[[1, ;; , 2]] // Accumulate, 0];
   res = Sum[SparseArray[
      Band[{ (rows[[i]] + 1), (cols[[j]] + 1)}, {rows[[i + 1]], 
         cols[[j + 1]]}] -> matNonEmpty[[i, j]],
      {Last[rows], Last[cols]}],
     {i, Length[rows] - 1}, {j, Length[cols] - 1}
     ];
   res
   ];


flattenMixonStates[basisMixon_] := Block[
   {kets, projection},
   kets = 
    Flatten[If[Length[#states] > 1, 
        Table[ReplacePart[#, -1 -> {#states[[idx]]}], {idx, 
          Length[#states]}], #] & /@ Flatten[basisMixon]]
   ];


(* 
	c = cfBinCount[k vector] computes the bin counts of vector \vec{k} so that
	for each ki in \vec{k} the ki'th element of c, c[[ki]] is the number of copies
	of ki in \vec{k}. If \vec{k} does not have ki, then c[[ki]]=0.
	
	Ex: cfBinCount[{3,3,1,1,1},4] = {3,0,2,0} (i.e. c[[1]]=3, c[[2]]=0, c[[3]]=2, c[[4]]=0)

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


(*  
The function monomialsBoson takes boson number nB and degree degB and produces a list of monomials - this
function defines a canonical ordering (that we always use) of monomials with the same particle number and degree.
Similarly for monomialsFermion.
*)

ClearAll[monomialsBoson]
monomialsBoson[n_,deg_]:=monomialsBoson[n,deg]=IntegerPartitions[deg+n,{n}];
ClearAll[monomialsFermion]
monomialsFermion[n_,deg_]:=monomialsFermion[n,deg]=(#+Reverse[Range[n]-1])&/@monomialsBoson[n,deg+n-n (n+1)/2]


End[]
EndPackage[]


(* ::Chapter:: *)
(*Main Package*)


BeginPackage["mixonPhi4Code`",{"utilities`"}]


computePhi4Matrices::usage=
"computePhi4Matrices[\[CapitalDelta]max_,basisMixon_,fdr_]
computes the matrix elements of \[Phi]^4 term with respect to the 
mixon basis given as argument basisMixon_ and store them in 
folder fdr_.
Note that the first argument \[CapitalDelta]max is a lie: the computed 
matrix does not refer to this argument but uses all operators
in basisMixon_. The argument only decides the file name."


matPhi4NtoN::usage


matPhi4NtoN2::usage


Begin["`Private`"]


(* ::Section::Closed:: *)
(*External functions*)


(* computePhi4Matrices is the main wrapper function, which runs through the
elements of basisMixon_ and calls primBlockNtoNPlus to make the \[Phi]^4 matrix elements 
between primaries. *)


computePhi4Matrices[\[CapitalDelta]max_,basisMixon_,fdr_]:=With[{t1=AbsoluteTime[]},
	Print["@ NtoN:"];
	(* First construct the N-to-N matrix elements *)
	matPhi4NtoN=With[{
	(* Read the number nBMax of boson and nFMax of fermion primaries in the mixon basis *)
		nBMax=Dimensions[basisMixon][[1]]-1,
		nFMax=Dimensions[basisMixon][[2]]-1},
		Table[
		(* The N-to-N \[Phi]^4 interaction must preserve the number of bosons and fermions *)
			If[nBL==nBR&&nFL==nFR,
				Catch[ArrayFlatten[Outer[
				(* Apply primBlockNtoNPlus to each block of matrix elements with a given
				number of incoming and outgoing bosons and fermions (nBL=nBR, nFL=nFR). 
				If there are no primaries in the block, return the empty set.
				The argument of primBlockNtoNPlus (in this case, 0) is the change in
				boson number between the incoming and outgoing state *)
					primBlockNtoNPlus[0],
					If[Length[#]==0,Throw[{}],#]&@basisMixon[[nBL+1,nFL+1]],
					If[Length[#]==0,Throw[{}],#]&@basisMixon[[nBR+1,nFR+1]],1
				] ] ],
				(* If the boson & fermion numbers don't match, set the matrix
				elements for the block to zero *) 
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
	matPhi4NtoN=Replace[matPhi4NtoN,{{}..}->{},{4}];
	Print["t = ",AbsoluteTime[]-t1];
	
	Print["@ N to N+2:"];
	(* Next construct the matrix elements for N to N+2 particles, then we'll take the
	transpose to obtain N+2 to N *)
	matPhi4NtoN2=With[{
	(* Read the number nBMax of boson and nFMax of fermion primaries in the mixon basis *)
		nBMax=Dimensions[basisMixon][[1]]-1,
		nFMax=Dimensions[basisMixon][[2]]-1},
		Table[
		(* The N-to-N+2 \[Phi]^4 interaction must change the number of bosons by 2, 
		and preserve the number of fermions *)
			If[nBL+2==nBR&&nFL==nFR,
				Catch[ArrayFlatten[Outer[
				(* Apply primBlockNtoNPlus to each block of matrix elements with a given
				number of incoming and outgoing bosons and fermions (nBL+2=nBR, nFL=nFR). 
				If there are no primaries in the block, return the empty set.
				The argument of primBlockNtoNPlus (in this case, 2) is the change in
				boson number between the incoming and outgoing state *)
					primBlockNtoNPlus[2],
					If[Length[#]==0,Throw[{}],#]&@
						basisMixon[[nBL+1,nFL+1]],
					If[Length[#]==0,Throw[{}],#]&@
						basisMixon[[nBR+1,nFR+1]],
				1 ] ] ], 
				(* If the boson numbers don't differ by 2 or the fermion numbers
				don't match, set the matrix elements for the block to zero *) 
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
	matPhi4NtoN2=Replace[matPhi4NtoN2,{{}..}->{},{4}];
	(* Now use the transpose of the N to N+2 matrix elements to obtain the
	N+2 to N matrix elements*)
	Block[{
		nBMax=Dimensions[basisMixon][[1]]-1,
		nFMax=Dimensions[basisMixon][[2]]-1,
		nBR,nFR,block
		},
		Do[
			nBR=nBL-2;
			nFR=nFL;
			block=matPhi4NtoN2[[nBR+1,nBL+1,nFR+1,nFL+1]];
			matPhi4NtoN2[[nBL+1,nBR+1,nFL+1,nFR+1]]=If[block!={},
				Transpose[block],{}],
			{nBL,2,nBMax},
			{nFL,0,nFMax}
		]
	];
	
	Print["t = ",AbsoluteTime[]-t1];
	
	(* Save the resulting matrix elements, with the filenames set by \[CapitalDelta]max_ and the directory set by fdr_ *)
	SetDirectory[fdr];
	Save["MatrixPhi4NtoNMixonD"<>ToString[\[CapitalDelta]max],matPhi4NtoN];
	Save["MatrixPhi4NtoN2MixonD"<>ToString[\[CapitalDelta]max],matPhi4NtoN2];
]


(* Function for counting the number of basis states with a given number of bosons and fermions *)
stateCount[lstOfLevels_]:=Total[Length[#states]&/@lstOfLevels]


(* ::Section::Closed:: *)
(*Matrix contracting an array of primaries*)


(* primBlockNtoNPlus creates a function that makes the \[Phi]^4 matrix elements. This function acts
on the in and out basis elements.
For instance, say you feed primBlock 
primBlock[basisMixon[[nBL+1,nFL+1]][[1]],basisMixon[[nBR+1,nFR+1]]][[1]]
with nBL=nBR=2, nFL=0=nFR=0.
Then the in- and out-states are the first two-scalar states.
In this case,
level1=basisMixon[[nBL+1,nFL+1]][[1]]=\[LeftAssociation]"nB"\[Rule]2,"degB"\[Rule]0,"nF"\[Rule]0,"degF"\[Rule]0,"l"\[Rule]0,"states"\[Rule]{{{{1.`}}}}\[RightAssociation]
and level2 matches level1.
The function created by primBlock calls monomialBlock to make the matrix elements for monomials, and
adds them together (after multiplying by some prefactors) in the combination dictated by the primary
in the arguments level1 and level2 *)


primBlockNtoNPlus[dnB_]=Function[{level1,level2},
	With[{
		lL=level1["l"],lR=level2["l"],
		degBL=level1["degB"],degBR=level2["degB"],
		degFL=level1["degF"],degFR=level2["degF"],
		nB=level1["nB"],nF=level2["nF"]
	},
	
		SparseArray@Outer[
			Total[Table[
				Flatten[#1[[kL+1]]].
				monomialBlock[
					{nB,nB+dnB},nF,{degBL+kL,degBR+kR},
					{degFL+lL-kL,degFR+lR-kR}
				].
				Flatten[#2[[kR+1]]],
			{kL,0,lL},{kR,0,lR}],2]&,
		level1["states"],
		level2["states"],
		1]*factor[nB+3/2nF+degBL+degFL+lL,(nB+dnB)+3/2nF+degBR+degFR+lR]*
		factorM[4]
	]
];


(* ::Subsection::Closed:: *)
(*Prefactors for interaction*)


ClearAll[factor]
factor[\[CapitalDelta]_,\[CapitalDelta]p_]:=factor[\[CapitalDelta],\[CapitalDelta]p]=Sqrt[ Gamma[2\[CapitalDelta]]Gamma[2\[CapitalDelta]p] ] * (-1)^(\[CapitalDelta]-\[CapitalDelta]p) / Gamma[\[CapitalDelta]+\[CapitalDelta]p-1];


ClearAll[factorM]
factorM[m_]:=factorM[m]=(1/Sqrt[4\[Pi]])^(m-2) * (-1)^m (** m!*)


(* ::Section::Closed:: *)
(*Matrix contracting an array of monomials*)


(* monomialBlock is a wrapper to compute the \[Phi]^4 matrix elements for the monomials
 - at the end of the routine it applies monomialMixonContraction to the
bincounts a1,a2,b1,b2 of the in and out monomials.

The function monomialsBoson takes boson number nB and degree degB and produces a list of monomials - this
function defines a canonical ordering (that we always use) of monomials with the same particle number and degree.
Similarly for monomialsFermion.

The output of monomialBlock is a matrix of monomialMixonContraction applied to an
`in' list and an `out' list of all the bincounts of all the monomials produced by
monomialsBoson and monomialsFermion (and their combinations) *)


ClearAll[monomialBlock]
monomialBlock[{nBL_,nBR_},nF_,{degB1_,degB2_},{degF1_,degF2_}]:=
monomialBlock[{nBL,nBR},nF,{degB1,degB2},{degF1,degF2}]=With[
	{
		a1List=cfBinCount[#,Max[degB1,degB2]+1]&/@monomialsBoson[nBL,degB1],
		a2List=cfBinCount[#,Max[degB1,degB2]+1]&/@monomialsBoson[nBR,degB2],
		b1List=cfBinCount[#,Max[degF1,degF2]+1]&/@monomialsFermion[nF,degF1],
		b2List=cfBinCount[#,Max[degF1,degF2]+1]&/@monomialsFermion[nF,degF2]
	},
	Outer[
		monomialMixonContraction,
		Flatten[Outer[List,a1List,b1List,1],1],
		Flatten[Outer[List,a2List,b2List,1],1],
	1]//SparseArray
]


(* ::Section:: *)
(*Individual monomial elements*)


(* 
	monomialScalarContraction[] computes the matrix element of the \[Phi]^4 interaction
	between two all-scalar monomials.
	
	Most of the work involved is efficiently doing the sum over all allowed contractions
	of the interaction with the external states, i.e. the sum over kvec and kvec' is too
	slow if we do it by brute force. But most of the contractions vanish, and many terms
	are equivalent since they are related by symmetry. So we instead look at the bin counts
	of the in and out states and ask when can individual k's be removed from the in and out
	states so that the remaining vectors are the same on both sides; and we group together
	equivalent terms and multiply by a symmetry factor.
	
	The inputs of monomialScalarContraction[] are the occupation number representation of
	the all-scalar monomials k and k', generated by cfBinCount[] (i.e. kCount=cfBinCount[k])
	kCount -> scalar k from in state
	kpCount -> scalar k' from out state
	as well as the number of particles m_ involved in the interaction (here: m=4)
 *)
ClearAll[monomialScalarContraction]
monomialScalarContraction[m_][kCount_,kpCount_]:=monomialScalarContraction[m][kCount,kpCount]=Block[
	{
		max=Length[kCount],
		diff,d,cBar,cpBar,kl,kpl,kCommonCount,cBarFree,klFreeSet
	},
	diff=kCount-kpCount;
	d=(m-Total[Abs[diff]])/2;
	
	Switch[
		(* The bin counts can change by 0, 2, or 4.  If it changes by 4, then this fixes
		all ki and kj' which contract with \[Phi]^4 - i.e. the contraction is not "free".
		If it changes by 2, then one pair of contractions can consist of any ki and kj',
		as long as they are equal - i.e. one pair of contractions is "free". If the bin
		counts change by 0, then both pairs of contractions are "free".
		The parameter d=0,1,2 tells how many "free" contractions there are. *)
		d  (* number of free contractions k_i\[Equal]k'_j *),
		
		(* If d=0, the ki and kj' are fixed, and we can compute the resulting matrix element *)
		0,
		cBar=Ramp[diff];
		cpBar=Ramp[-diff];
		kl=cfBinReconstruct[cBar];
		kpl=cfBinReconstruct[cpBar];
		countingFactor[kCount,kpCount,cBar,cpBar]*binomialMinSum[kl,kpl]/Sqrt[(Times@@kl)*(Times@@kpl)],
		
		(* If d=1 or 2, some of the contractions are "free", so we must sum over the set
		of possible contractions*)
		_?Positive,
		cBar=Ramp[diff];
		cpBar=Ramp[-diff];
		kl=cfBinReconstruct[cBar];
		kpl=cfBinReconstruct[cpBar];
		kCommonCount=kCount-cBar;
		klFreeSet=DeleteDuplicatesBy[Subsets[kCommonCount//cfBinReconstruct,{d}],Sort];
		Sum[
			cBarFree=cfBinCount[klFree,max];
			countingFactor[
				kCount,
				kpCount,
				cBar+cBarFree,
				cpBar+cBarFree
			] * binomialMinSum[
				Join[kl,klFree],
				Join[kpl,klFree]
			]/Sqrt[(Times@@kl)*(Times@@kpl)*(Times@@klFree)^2],
			{klFree,klFreeSet}
		],
		
		(* Cases where the bin counts cannot match are set to zero *)
		_,0
	]
]


(* 
	monomialMixonContraction[] computes the matrix element of the \[Phi]^4 interaction between two mixed
	scalar-fermion monomials.
	
	Because the fermions are all "spectators", the fermion monomial bin counts of the in and out states must
	match, otherwise the matrix element vanishes. We then compute the contraction of the scalar monomials
	with the \[Phi]^4 interaction using monomialScalarContraction[].
	
	The inputs of monomialMixonContraction[] are the occupation number representation of the scalar
	monomials kB and kB' and fermion monomials kF and kF', generated by cfBinCount[] (i.e. a=cfBinCount[kB])
	a -> scalar kB from in state
	b -> fermion kF from in state
	ap -> scalar kB' from out state
	bp -> fermion kF' from out state
 *)
monomialMixonContraction[{a_,b_},{ap_,bp_}]:=If[
	b!=bp,0,
	monomialScalarContraction[4][a,ap]
];
SetAttributes[monomialScalarContraction,Orderless];


(* ::Subsection:: *)
(*Counting factors for matrix element*)


countingFactor[kCount_,kpCount_,cBar_,cpBar_]:=Product[
	Sqrt[Pochhammer[kCount[[\[Lambda]]]-cBar[[\[Lambda]]]+1,cBar[[\[Lambda]]]]*Pochhammer[kpCount[[\[Lambda]]]-cpBar[[\[Lambda]]]+1,cpBar[[\[Lambda]]]]]
	/ ( cBar[[\[Lambda]]]! cpBar[[\[Lambda]]]! ),
	{\[Lambda],Length[cBar]}
]


binomialMinSum[k_,kp_]:=Block[
	{\[Sigma],\[Sigma]p,n\[Sigma],n\[Sigma]p},
	{\[Sigma],n\[Sigma]}={Plus@@@#,(-1)^Length/@#}&@Drop[Subsets[k],1];
	{\[Sigma]p,n\[Sigma]p}={Plus@@@#,(-1)^Length/@#}&@Drop[Subsets[kp],1];
	n\[Sigma].Outer[Min,\[Sigma],\[Sigma]p].n\[Sigma]p
]


(* ::Section:: *)
(*End*)


End[]


EndPackage[]
