(* ::Package:: *)

BeginPackage["mixonMassCode`"]


computeMixonMassMatrices::usage=
"computeMixonMassMatrices[\[CapitalDelta]max_,basisMixon_,fdr_]
computes the matrix elements of scalar and fermion mass terms
with respect to the mixon basis given as argument basisMixon_ 
and store them in folder fdr_.
Note that the first argument \[CapitalDelta]max is a lie: the computed 
matrix does not refer to this argument but uses all operators
in basisMixon_. The argument only decides the file name."


matScalarMass::usage


matFermionMass::usage


Begin["`Private`"]


(* ::Section:: *)
(*External functions*)


computeMixonMassMatrices[\[CapitalDelta]max_,basisMixon_,fdr_]:=With[{t1=AbsoluteTime[]},
	Print["@ scalar mass:"];
	matScalarMass=With[{
		nBMax=Dimensions[basisMixon][[1]]-1,
		nFMax=Dimensions[basisMixon][[2]]-1},
		Table[
			If[nBL==nBR&&nFL==nFR,
				Catch[ArrayFlatten[Outer[
					primBlockNtoN[scalarMassMonomialBlock],
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
	matScalarMass=Replace[matScalarMass,{{}..}->{},{4}];
	Print["t = ",AbsoluteTime[]-t1];
	
	Print["@ fermion mass:"];
	matFermionMass=With[{
		nBMax=Dimensions[basisMixon][[1]]-1,
		nFMax=Dimensions[basisMixon][[2]]-1},
		Table[
			(*If[nBL==nBR&&nFL==nFR,Catch[ArrayFlatten[Outer[
					primBlockNtoN[fermionMassMonomialBlock],
					If[Length[#]==0,Throw[{}],#]&@basisMixon[[nBL+1,nFL+1]],
					If[Length[#]==0,Throw[{}],#]&@basisMixon[[nBR+1,nFR+1]],1
			] ] ], 0 ]*)
			If[nBL==nBR&&nFL==nFR,
				Catch[ArrayFlatten[Outer[
					primBlockNtoN[fermionMassMonomialBlock],
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
	matFermionMass=Replace[matFermionMass,{{}..}->{},{4}];
	Print["t = ",AbsoluteTime[]-t1];
	
	SetDirectory[fdr];
	Save["MatrixScalarMassMixonD"<>ToString[\[CapitalDelta]max],matScalarMass];
	Save["MatrixFermionMassMixonD"<>ToString[\[CapitalDelta]max],matFermionMass];
]


stateCount[lstOfLevels_]:=Total[Length[#states]&/@lstOfLevels]


(* ::Section:: *)
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


ClearAll[monomialsBoson]
monomialsBoson[n_,deg_]:=monomialsBoson[n,deg]=IntegerPartitions[deg+n,{n}];
ClearAll[monomialsFermion]
monomialsFermion[n_,deg_]:=monomialsFermion[n,deg]=(#+Reverse[Range[n]-1])&/@monomialsBoson[n,deg+n-n (n+1)/2]


(* ::Section:: *)
(*Individual monomial elements*)


(* ::Subsection:: *)
(*Scalar mass term*)


scalarMassScalarContraction[{a__,0},{ap__,0}]:=scalarMassScalarContraction[{a},{ap}]
scalarMassScalarContraction[a_,ap_]:=scalarMassScalarContraction[a,ap]=Block[
	{
		diff,ki,kpj
	},
	diff=a-ap;
	Switch[
		Total[diff//Abs],
		0,(ap//Total),
		2,
		ki=FirstPosition[diff,1]//First;
		kpj=FirstPosition[diff,-1]//First;
		Sqrt[ If[ki>kpj,kpj/ki,ki/kpj] * a[[ki]]*ap[[kpj]]  ],
		
		_,0
	]
]
SetAttributes[scalarMassScalarContraction,Orderless];


scalarMassMixonContraction[{a_,b_},{ap_,bp_}]:=If[
	b!=bp,0,
	scalarMassScalarContraction[a,ap]
]


(* ::Subsection:: *)
(*fermion mass term*)


fermionMassFermionContraction[{b__,0},{bp__,0}]:=fermionMassFermionContraction[{b},{bp}]
fermionMassFermionContraction[b_,bp_]:=fermionMassFermionContraction[b,bp]=Block[
	{
		diff,ki,kpj,i,j
	},
	diff=b-bp;
	(1/2)*Switch[
		Total[diff//Abs],
		0,(bp//Total),
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


fermionMassMixonContraction[{a_,b_},{ap_,bp_}]:=If[
	a!=ap,0,
	fermionMassFermionContraction[b,bp](*/(Times@@Factorial[a])*)
]


(* ::Section:: *)
(*Matrix contracting an array of monomials*)


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
		fermionMassMixonContraction,
		Flatten[Outer[List,a1List,b1List,1],1],
		Flatten[Outer[List,a2List,b2List,1],1],
	1]//SparseArray
]


(* ::Section:: *)
(*Dotting primary vectors to monomial elements*)


(* ::Subsection:: *)
(*primary dimension factor*)


factor[\[CapitalDelta]_,\[CapitalDelta]p_]:=factor[\[CapitalDelta],\[CapitalDelta]p]=Sqrt[ Gamma[2\[CapitalDelta]]Gamma[2\[CapitalDelta]p] ] * (-1)^(\[CapitalDelta]-\[CapitalDelta]p) / Gamma[\[CapitalDelta]+\[CapitalDelta]p-1];


(* ::Subsection:: *)
(*Matrix contracting an array of primaries*)


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
(*End*)


End[]


EndPackage[]
