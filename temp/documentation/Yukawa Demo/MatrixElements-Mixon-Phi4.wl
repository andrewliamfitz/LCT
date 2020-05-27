(* ::Package:: *)

BeginPackage["phi4Code`"]


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


(* ::Section:: *)
(*External functions*)


computePhi4Matrices[\[CapitalDelta]max_,basisMixon_,fdr_]:=With[{t1=AbsoluteTime[]},
	Print["@ NtoN:"];
	matPhi4NtoN=With[{
		nBMax=Dimensions[basisMixon][[1]]-1,
		nFMax=Dimensions[basisMixon][[2]]-1},
		Table[
			If[nBL==nBR&&nFL==nFR,
				Catch[ArrayFlatten[Outer[
					primBlockNtoNPlus[0],
					If[Length[#]==0,Throw[{}],#]&@basisMixon[[nBL+1,nFL+1]],
					If[Length[#]==0,Throw[{}],#]&@basisMixon[[nBR+1,nFR+1]],1
				] ] ],
				SparseArray[{},{stateCount[basisMixon[[nBL+1,nFL+1]]],
					stateCount[basisMixon[[nBR+1,nFR+1]]] }] 
			],
			{nBL,0,nBMax},
			{nBR,0,nBMax},
			{nFL,0,nFMax},
			{nFR,0,nFMax}
		]
	];
	matPhi4NtoN=Replace[matPhi4NtoN,{{}..}->{},{4}];
	Print["t = ",AbsoluteTime[]-t1];
	
	Print["@ N to N+2:"];
	matPhi4NtoN2=With[{
		nBMax=Dimensions[basisMixon][[1]]-1,
		nFMax=Dimensions[basisMixon][[2]]-1},
		Table[
			If[nBL+2==nBR&&nFL==nFR,
				Catch[ArrayFlatten[Outer[
					primBlockNtoNPlus[2],
					If[Length[#]==0,Throw[{}],#]&@
						basisMixon[[nBL+1,nFL+1]],
					If[Length[#]==0,Throw[{}],#]&@
						basisMixon[[nBR+1,nFR+1]],
				1 ] ] ], 
				SparseArray[{},{stateCount[basisMixon[[nBL+1,nFL+1]]],
					stateCount[basisMixon[[nBR+1,nFR+1]]] }] 
			],
			{nBL,0,nBMax},
			{nBR,0,nBMax},
			{nFL,0,nFMax},
			{nFR,0,nFMax}
		]
	];
	matPhi4NtoN2=Replace[matPhi4NtoN2,{{}..}->{},{4}];
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
	
	SetDirectory[fdr];
	Save["MatrixPhi4NtoNMixonD"<>ToString[\[CapitalDelta]max],matPhi4NtoN];
	Save["MatrixPhi4NtoN2MixonD"<>ToString[\[CapitalDelta]max],matPhi4NtoN2];
]


stateCount[lstOfLevels_]:=Total[Length[#states]&/@lstOfLevels]


(* ::Section::Closed:: *)
(*Utility functions*)


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
(*Monomial contraction*)


(* assuming number of particles match np\[Equal]n+\[Delta] *)
ClearAll[monomialScalarContraction]
monomialScalarContraction[m_][kCount_,kpCount_]:=monomialScalarContraction[m][kCount,kpCount]=Block[
	{
		(*n=Length[k],np=Length[kp],*)
		(*kCount,kpCount,*)(*max=Max[k,kp],*)
		max=Length[kCount],
		diff,d,cBar,cpBar,kl,kpl,kCommonCount,cBarFree,klFreeSet
	},
	(*kCount=cfBinCount[k,max];
	kpCount=cfBinCount[kp,max];*)
	diff=kCount-kpCount;
	d=(m-Total[Abs[diff]])/2;
	
	(* n\[Rule]n+m forbidden by LC kinematics, 
	assuming this does not happen here *)
	Switch[
		d  (* number of free contractions k_i\[Equal]k'_j *),
		
		(* all k_i \[NotEqual] k'_j, only one contraction available *)
		0,
		cBar=Ramp[diff];
		cpBar=Ramp[-diff];
		kl=cfBinReconstruct[cBar];
		kpl=cfBinReconstruct[cpBar];
		countingFactor[kCount,kpCount,cBar,cpBar]*binomialMinSum[kl,kpl]/Sqrt[(Times@@kl)*(Times@@kpl)],
		
		(* some free contractions k_i\[Equal]k'_j *)
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
		
		(* impossible contraction *)
		_,0
	]
]


monomialMixonContraction[{a_,b_},{ap_,bp_}]:=If[
	b!=bp,0,
	monomialScalarContraction[4][a,ap]
];
SetAttributes[monomialScalarContraction,Orderless];


countingFactor[kCount_,kpCount_,cBar_,cpBar_]:=Product[
	(*Print[Sqrt[Pochhammer[kCount[[\[Lambda]]]-cBar[[\[Lambda]]]+1,cBar[[\[Lambda]]]]*Pochhammer[kpCount[[\[Lambda]]]-cpBar[[\[Lambda]]]+1,cpBar[[\[Lambda]]]]]
	/ ( cBar[[\[Lambda]]]! cpBar[[\[Lambda]]]! )];*)
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
(*Matrix contracting an array of monomials*)


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
(*Matrix contracting an array of primaries*)


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


ClearAll[factor]
factor[\[CapitalDelta]_,\[CapitalDelta]p_]:=factor[\[CapitalDelta],\[CapitalDelta]p]=Sqrt[ Gamma[2\[CapitalDelta]]Gamma[2\[CapitalDelta]p] ] * (-1)^(\[CapitalDelta]-\[CapitalDelta]p) / Gamma[\[CapitalDelta]+\[CapitalDelta]p-1];


ClearAll[factorM]
factorM[m_]:=factorM[m]=(1/Sqrt[4\[Pi]])^(m-2) * (-1)^m (** m!*)


(* ::Section:: *)
(*End*)


End[]


EndPackage[]
