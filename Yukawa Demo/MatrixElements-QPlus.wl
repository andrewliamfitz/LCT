(* ::Package:: *)

BeginPackage["susyQPlusCode`"]


computeQPlusMatrix::usage=
"computeQPlusMatrix[\[CapitalDelta]max_,basisN1SUSY_,fdr_]
computes the matrix elements of Q+ term with respect to the 
N1 SUSY basis given as argument basisN1SUSY_ and store them in 
folder fdr_.
Note that the first argument \[CapitalDelta]max is a lie: the computed 
matrix does not refer to this argument but uses all operators
in basisN1SUSY_. The argument only decides the file name."


matQPlusMass::usage


matQPlusInt::usage


Begin["`Private`"]


(* ::Section:: *)
(*External functions*)


computeQPlusMatrix[\[CapitalDelta]max_,basisMixon_,fdr_]:=With[{t1=AbsoluteTime[]},
	matQPlusMass=With[{
		nBMax=Dimensions[basisMixon][[1]]-1,
		nFMax=Dimensions[basisMixon][[2]]-1},
		Table[
			If[nBL-1==nBR&&nFL+1==nFR,
				Catch[ArrayFlatten[Outer[
					primBlock,
					If[Length[#]==0,Throw[{}],#]&@basisMixon[[nBL+1,nFL+1]],
					If[Length[#]==0,Throw[{}],#]&@basisMixon[[nBR+1,nFR+1]],
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
	
	(* nBL+1==nBR&&nFL-1==nFR *)
	Block[{
		nBMax=Dimensions[basisMixon][[1]]-1,
		nFMax=Dimensions[basisMixon][[2]]-1,
		nBR,nFR,block
		},
		Do[
			nBR=nBL+1;
			nFR=nFL-1;
			block=matQPlusMass[[nBR+1,nBL+1,nFR+1,nFL+1]];
			matQPlusMass[[nBL+1,nBR+1,nFL+1,nFR+1]]=If[block!={},
				Transpose[block],{}],
			{nBL,0,nBMax-1},
			{nFL,1,nFMax}
		]
	];
	matQPlusMass=Replace[matQPlusMass,{{}..}->{},{4}];
	Print["Q+ mass term ,t = ",AbsoluteTime[]-t1];
	
	matQPlusInt=With[{
		nBMax=Dimensions[basisMixon][[1]]-1,
		nFMax=Dimensions[basisMixon][[2]]-1},
		Table[
			If[(nBL==nBR||nBL==nBR+2)&&nFL+1==nFR,
				Catch[ArrayFlatten[Outer[
					primBlockInt,
					If[Length[#]==0,Throw[{}],#]&@basisMixon[[nBL+1,nFL+1]],
					If[Length[#]==0,Throw[{}],#]&@basisMixon[[nBR+1,nFR+1]],
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
	Block[{
		nBMax=Dimensions[basisMixon][[1]]-1,
		nFMax=Dimensions[basisMixon][[2]]-1,
		(*nBR,*)nFR,block
		},
		Do[
			(*nBR=nBL+1;*)
			nFR=nFL-1;
			block=matQPlusInt[[nBR+1,nBL+1,nFR+1,nFL+1]];
			matQPlusInt[[nBL+1,nBR+1,nFL+1,nFR+1]]=If[block!={},
				Transpose[block],{}],
			{nBL,0,nBMax},
			{nFL,1,nFMax},
			{nBR,Select[{nBL,nBL+2},#<=nBMax&]}
		]
	];
	matQPlusInt=Replace[matQPlusInt,{{}..}->{},{4}];
	Print["Q+ interaction term, t = ",AbsoluteTime[]-t1];
	
	SetDirectory[fdr];
	DeleteFile["MatrixQPlusMassD"<>ToString[\[CapitalDelta]max]];
	DeleteFile["MatrixQPlusIntD"<>ToString[\[CapitalDelta]max]];
	Save["MatrixQPlusMassD"<>ToString[\[CapitalDelta]max],matQPlusMass];
	Save["MatrixQPlusIntD"<>ToString[\[CapitalDelta]max],matQPlusInt];
]


(* ::Section:: *)
(*Internal functions*)


factor[\[CapitalDelta]_,\[CapitalDelta]p_]:=(-1)^(\[CapitalDelta]-\[CapitalDelta]p-1/2) (*\[ImaginaryI]^(3/2)*) (*(1/2)*) Sqrt[Gamma[2\[CapitalDelta]]Gamma[2\[CapitalDelta]p]]/Gamma[\[CapitalDelta]+\[CapitalDelta]p-1/2]


(* ::Subsection::Closed:: *)
(*mass term*)


primBlock=Function[{level1,level2},
	With[{
		dnB=-1,dnF=1,
		lL=level1["l"],lR=level2["l"],
		degBL=level1["degB"],degBR=level2["degB"],
		degFL=level1["degF"],degFR=level2["degF"],
		nBL=level1["nB"],nFL=level1["nF"]
	},
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
		qPlus,
		Flatten[Outer[List,a1List,b1List,1],1],
		Flatten[Outer[List,a2List,b2List,1],1],
	1]//SparseArray
]


qPlus[{a_,b_},{ap_,bp_}]:=Block[
	{aBar,bpBar,k1,k2,s1=-1,s2=+1,residue,symFactor,perm},
	aBar=Ramp[a-ap];
	bpBar=Ramp[bp-b];
	
	If[Total[aBar]!=1||Total[bpBar]!=1,Return[0]];
	
	k1=cfBinReconstruct[aBar]//First;
	k2=cfBinReconstruct[bpBar]//First;
	(*residue=Sqrt[(*(1/2)*) k2 (k2+1)/k1]*Which[k1==k2+1,1,k1==k2,-1,True,0];*)
	residue=If[k1<=k2,Sqrt[k1/(k2 (k2+1) )],0];
	
	symFactor=Sqrt[a[[k1]]];
	perm=(-1)^(Total[Take[bp,k2]]-1);
	(*s1**)residue*symFactor*perm
]


(* ::Subsection:: *)
(*interaction term*)


primBlockInt=Function[{level1,level2},
	With[{
		(*dnB=-1,*)dnF=1,
		lL=level1["l"],lR=level2["l"],
		degBL=level1["degB"],degBR=level2["degB"],
		degFL=level1["degF"],degFR=level2["degF"],
		nBL=level1["nB"],nBR=level2["nB"],
		nFL=level1["nF"]
	},
		SparseArray@Outer[
			Total[Table[
				Flatten[#1[[kL+1]]].
				monomialBlockInt[
					{nBL,nBR},{nFL},{degBL+kL,degBR+kR},
					{degFL+lL-kL,degFR+lR-kR}
				].
				Flatten[#2[[kR+1]]],
			{kL,0,lL},{kR,0,lR}],2]&,
		level1["states"],
		level2["states"],
		1]*factor[nBL+3/2nFL+degBL+degFL+lL,nBR+3/2(nFL+dnF)+degBR+degFR+lR]
	]
];


ClearAll[monomialBlockInt]
monomialBlockInt[{nBL_,nBR_},{nFL_},{degB1_,degB2_},{degF1_,degF2_}]:=
monomialBlockInt[{nBL,nBR},{nFL},{degB1,degB2},{degF1,degF2}]=With[
	{
		a1List=cfBinCount[#,Max[degB1,degB2]+1]&/@monomialsBoson[nBL,degB1],
		a2List=cfBinCount[#,Max[degB1,degB2]+1]&/@monomialsBoson[nBR,degB2],
		b1List=cfBinCount[#,Max[degF1,degF2]+1]&/@monomialsFermion[nFL,degF1],
		b2List=cfBinCount[#,Max[degF1,degF2]+1]&/@monomialsFermion[(*nFR*)nFL+1,degF2]
	},
	Outer[
		qPlusInt,
		Flatten[Outer[List,a1List,b1List,1],1],
		Flatten[Outer[List,a2List,b2List,1],1],
	1]//SparseArray
]


qPlusInt[{a_,b_},{ap_,bp_}]:=Block[
	{aBar,apBar,bpBar,k1,k2,k0,kbL,kbR,
		s0,s1,s2=+1,residues,symFactor,perm},
	aBar=Ramp[a-ap];
	apBar=Ramp[ap-a];
	bpBar=Ramp[bp-b];
	
	(*If[(Total[aBar+apBar]\[NotEqual]2)||Total[bpBar]!=1,Return[0]];*)
	If[Total[bpBar]!=1,Return[0]];
	k2=cfBinReconstruct[bpBar]//First;
	perm=(-1)^(Total[Take[bp,k2]]-1);
	
	Which[
		Total[aBar+apBar]==2,
		kbL=cfBinReconstruct[aBar];
		kbR=cfBinReconstruct[apBar];
		{k0,k1}=Join[kbL,kbR];
		{s0,s1}=Join[kbL*0+(-1),kbR*0+1];
		(*residue=Sqrt[(*(1/2)*) k2 (k2+1)/k1]*Which[k1==k2+1,1,k1==k2,-1,True,0];*)
		(*residues=(A0(residue[-(s0 k0 + s1 k1),k2]
			-A1 residue[-s0 k0,k2]
			-A1 residue[-s1 k1,k2])
			+A3 (residue[-(s1 k0 + s0 k1),k2]
			-A4 residue[-s1 k0,k2]
			-A4 residue[-s0 k1,k2]))/Sqrt[k0 k1 k2 (k2+1) ];*)
		residues=-(residue[-(s0 k0 + s1 k1),k2]
			- residue[-s0 k0,k2]
			- residue[-s1 k1,k2])/Sqrt[k0 k1 k2 (k2+1) ];
		
		symFactor=(Times@@Table[
				Sqrt[ Binomial[a[[k]],aBar[[k]] ]/(aBar[[k]]!) ],
				{k,DeleteDuplicates[kbL]}
			])*(Times@@Table[
				Sqrt[ Binomial[ap[[kp]],apBar[[kp]] ]/(apBar[[kp]]!) ],
				{kp,DeleteDuplicates[kbR]}
			]);
		(*s0*s1**)residues*symFactor*perm,
		
		Total[aBar+apBar]==0,
		(*Print["a\[Equal]ap"];*)
		(*2A6(Plus@@Total[Take[a,UpTo[k2]]])/Sqrt[k2 (k2+1) ]*perm,*)
		(Plus@@Total[Take[a,UpTo[k2]]])/Sqrt[k2 (k2+1) ]*perm,
		
		True,0
	]
];
residue[k1_,k2_]:=If[0<k1<=k2,k1,0];





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
