(* ::Package:: *)

(* ::Section:: *)
(*Begin*)


BeginPackage["mixonBasisCode`"]


computeMixonBasis::usage=
"computeMixonBasis[\[CapitalDelta]max_,basisBoson_,basisFermion_,fdr_]
computes the mixon basis using Joao's alternating derivatives from
the calculated boson basis basisBoson_ and fermion basis 
basisFermion_ and store them into folder fdr_.
Note that the \[CapitalDelta]max_ argument, as well as the max dimension of the 
boson basis and fermion basis, should all be the same, or exceptions
may occur. "


basisMixon::usage


Begin["`Private`"]


(* ::Section:: *)
(*External function*)


computeMixonBasis[\[CapitalDelta]max_,basisBoson_,basisFermion_,fdr_]:=Block[
	{primaryStates,t1=AbsoluteTime[]},
	Print["@ : taking boson descendants"];
	takeBosonDescendants[\[CapitalDelta]max,basisBoson];
	Print["Time (s):", (AbsoluteTime[]-t1)];
	
	Print["@ : taking fermion descendants"];
	takeFermionDescendants[\[CapitalDelta]max,basisFermion];
	Print["Time (s):", (AbsoluteTime[]-t1)];
	
	Print["@ : gluing fermion and bosons"];
	basisMixon=Join[
		Reap[Do[
			primaryStates=basisBoson[[1,deg+1,n]];
			If[primaryStates!={}, Sow[{KroneckerProduct[#,{1}]},state[n,deg,0,0,0]]&/@primaryStates],
			{deg,0,\[CapitalDelta]max},{n,1,\[CapitalDelta]max-deg}
		],state[__],<|Thread[{"nB","degB","nF","degF","l"}->List@@#1],"states"->#2|>&][[2]] ,
		
		Reap[Do[
			primaryStates=basisFermion[[1,deg+1,n]];
			If[primaryStates!={}, Sow[{KroneckerProduct[{1},#]},state[0,0,n,deg,0]]&/@primaryStates],
			{deg,0,\[CapitalDelta]max},{n,1,Floor[2/3*(\[CapitalDelta]max-deg)]}
		],state[__],<|Thread[{"nB","degB","nF","degF","l"}->List@@#1],"states"->#2|>&][[2]] ,
		
		glueBosonsAndFermions[\[CapitalDelta]max]
	];
	basisMixon=GatherBy[SortBy[basisMixon,{#nB&,#nF&,#degB&,#degF&,#l&}],{#nB&,#nF&}];
	basisMixon=Insert[basisMixon,{},{1,1}];
	basisMixon=With[{maxNFPlus1=(Length/@basisMixon)//Max},
		PadRight[#,maxNFPlus1,{{}}]&/@basisMixon
	];
	
	Print["Time (s):", (AbsoluteTime[]-t1)];
	
	SetDirectory[fdr];
	Save["BasisMixonD"<>ToString[\[CapitalDelta]max],basisMixon]
	
];


(* ::Section:: *)
(*Load functions*)


(* ::Subsection::Closed:: *)
(*bin counting*)


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


(* ::Subsection::Closed:: *)
(*monomial vectors*)


ClearAll[monomialsBoson]
monomialsBoson[n_,deg_]:=monomialsBoson[n,deg]=IntegerPartitions[deg+n,{n}];
ClearAll[monomialsFermion]
monomialsFermion[n_,deg_]:=monomialsFermion[n,deg]=(#+Reverse[Range[n]-1])&/@monomialsBoson[n,deg+n-n (n+1)/2]


(* ::Subsection:: *)
(*Derivate operation from "encode and map" method*)


ClearAll[dBoson]
dBoson[n_,deg_]:=dBoson[n,deg]=Block[
	{kLow,kUp,
		aLow,
		map,mat,ap(*,eUp*)
	},
	kLow=monomialsBoson[n,deg]-1;
	kUp=monomialsBoson[n,deg+1]-1;
	aLow=cfBinCount[#,deg+2]&/@(kLow+1);
	(*eLow=bosonEncode/@kLow;*)
	(*eUp=bosonEncode/@kUp;*)
	(*MapThread[(map[#1]=#2)&,{eUp,Range[Length[eUp]]}];*)
	MapThread[(map[#1]=#2)&,{kUp,Range[Length[kUp]]}];
	mat=SparseArray[{},{kLow//Length,kUp//Length}];
	Do[With[{a=aLow[[i]],k=kLow[[i]]},
		(mat[[i,map[cfBinReconstruct[
			ap=a;ap[[#]]-=1;ap[[#+1]]++;ap
		]-1//Reverse  ]  ]]+=a[[#]]) &/@
			Flatten[Position[a,_?Positive,1]]
	],{i,Length[aLow]}];
	mat
]


ClearAll[dFermion]
dFermion[n_,deg_]:=dFermion[n,deg]=Block[
	{degB=deg+n-n (n+1)/2,
		kLow,kUp,
		aLow,
		map,mat,ap(*,eUp*)
	},
	kLow=monomialsBoson[n,degB]-1;
	kUp=monomialsBoson[n,degB+1]-1;
	aLow=cfBinCount[#,degB+2]&/@(kLow+1);
	(*eUp=bosonEncode/@kUp;*)
	(*MapThread[(map[#1]=#2)&,{eUp,Range[Length[eUp]]}];*)
	MapThread[(map[#1]=#2)&,{kUp,Range[Length[kUp]]}];
	mat=SparseArray[{},{kLow//Length,kUp//Length}];
	Do[With[{a=aLow[[i]],k=kLow[[i]]},
		(mat[[i,map[cfBinReconstruct[
			ap=a;ap[[#]]-=1;ap[[#+1]]++;ap
		]-1//Reverse  ]  ]]+=1) &/@
			Flatten[Position[a,_?Positive,1]]
	],{i,Length[aLow]}];
	mat
]


(* ::Subsection::Closed:: *)
(*state normalization factors*)


factorBoson[y_List]:=Sqrt[Times@@(#[[2]]!* #[[1]]^#[[2]]&/@Tally[y])]Times@@(Gamma/@y);


ClearAll[factorBosonAtLevel]
factorBosonAtLevel[n_,deg_]:=factorBosonAtLevel[n,deg]=factorBoson/@IntegerPartitions[n+deg,{n}]


factorFermion[k_List]:=(Times@@(Gamma/@k)) * Sqrt[Times@@(1/2 * k*(k+1))]


ClearAll[factorFermionAtLevel]
factorFermionAtLevel[n_,deg_]:=factorFermionAtLevel[n,deg]=factorFermion/@Select[IntegerPartitions[n+deg,{n}],DuplicateFreeQ]


(* ::Subsection::Closed:: *)
(*"Binomial" coefficients of Joao's alternating derivative*)


joaoCoeff[degL_,degR_,l_,k_]:=
	joaoCoeff[degL,degR,l,k]=
		((-1)^k Gamma[2degL+l]Gamma[2degR+l]) / 
		(k!(l-k)!Gamma[2degL+k]Gamma[2degR+l-k]);


(* ::Section:: *)
(*Compute*)


(* ::Subsection:: *)
(*take boson descendants*)


takeBosonDescendants[\[CapitalDelta]max_,basisBoson_]:=Block[
	{(*\[CapitalDelta]max=15,*)primaryStates},
	bosonBasisWithDescendants=Table[
		primaryStates=basisBoson[[1,deg+1,n]];
		If[primaryStates=={},{},MapThread[
			Function[{states,norm},Map[#*norm&,states]],
			{
				FoldList[
					#1.dBoson[n,#2]&,
					(#/factorBosonAtLevel[n,deg])&/@primaryStates,
					Range[deg,\[CapitalDelta]max-n-3/2,1]
			],
				factorBosonAtLevel[n,#]&/@Prepend[Range[deg+1,\[CapitalDelta]max-n-3/2+1,1],deg]
			}
		] ],
		{deg,0,\[CapitalDelta]max},{n,1,\[CapitalDelta]max-deg}
	]
];


(* ::Subsection:: *)
(*take fermion descendants*)


takeFermionDescendants[\[CapitalDelta]max_,basisFermion_]:=Block[
	{(*\[CapitalDelta]max=15,*)primaryStates},
	fermionBasisWithDescendants=Table[
	primaryStates=basisFermion[[1,deg+1,n]];
		If[primaryStates=={},{},MapThread[
			Function[{states,norm},Map[#*norm&,states]],
			{
				FoldList[
					#1.dFermion[n,#2]&,
					(#/factorFermionAtLevel[n,deg])&/@primaryStates,
					Range[deg,\[CapitalDelta]max-n*3/2-1,1]
				],
				factorFermionAtLevel[n,#]&/@Prepend[Range[deg+1,\[CapitalDelta]max-n*3/2-1+1,1],deg]
			}
		] ],
		{deg,0,\[CapitalDelta]max},{n,1,Floor[2/3*(\[CapitalDelta]max-deg)]}
	]
];


(* ::Subsection:: *)
(*glue bosons and fermions*)


normalize=(#/Sqrt[Total[Flatten[#]^2]]&)


glueBosonsAndFermions[\[CapitalDelta]max_]:=Block[
	{\[CapitalDelta]B,\[CapitalDelta]F,lMax},
	(*basisMixonsOnly=*)Reap[Do[
		\[CapitalDelta]B=degB+nB;
		\[CapitalDelta]F=degF+3/2*nF;
		lMax=Floor[\[CapitalDelta]max-\[CapitalDelta]B-\[CapitalDelta]F];
		
		Outer[
			Do[Sow[
				normalize@Table[joaoCoeff[\[CapitalDelta]B,\[CapitalDelta]F,l,k]*KroneckerProduct[#1[[k+1]] ,#2[[l-k+1]]],{k,0,l}],
			state[nB,degB,nF,degF,l]],{l,0,lMax}]&,
			If[#!={},Transpose[#],Continue[]]&@bosonBasisWithDescendants[[degB+1,nB]],
			If[#!={},Transpose[#],Continue[]]&@fermionBasisWithDescendants[[degF+1,nF]],
		1],
		{degB,0,\[CapitalDelta]max},
		{nB,1,\[CapitalDelta]max-degB},
		{degF,0,\[CapitalDelta]max-degB-nB},
		{nF,1,Floor[2/3*(\[CapitalDelta]max-degB-nB-degF)]}
	],state[__],<|Thread[{"nB","degB","nF","degF","l"}->List@@#1],"states"->#2|>&][[2]] 
];


(* ::Section:: *)
(*End*)


End[]


EndPackage[]
