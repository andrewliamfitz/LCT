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


(* ::Section:: *)
(*Usage and Function Descriptions*)


BeginPackage["scalarMatrixElementsPhiPow`",{"utilities`"}]


ComputeMatrixPhiPow::usage=
"ComputeMatrixPhiPow[m_,\[CapitalDelta]max_,basisBoson_] computes matrix elements of operator \[Phi]^m. It takes as input power m, 
\[CapitalDelta]max (which specifies to what \[CapitalDelta]max one wishes to compute the matrix elements to) and basisBoson, which is the 
scalar basis (the output of our scalar basis package). 
Note that \[CapitalDelta]max cannot be higher than the \[CapitalDelta]max that basisBoson was tabulated to. The output is a square matrix 
that correspond to the \[Phi]^m term of the Hamiltonian, computed up to the truncation \[CapitalDelta]max. This output
matrices of dnL \[Phi]'s contract to the left are stored in the variable fullMatrixPhiPow[{dnL,m-dnL}].";


fullMatrixPhiPow::usage


Begin["`Private`"]


(* ::Section:: *)
(*Main Functions for Computing \[Phi]^2 and \[Phi]^4 Matrix Elements*)


ClearAll[fullMatrixPhiPow]
fullMatrixPhiPow=<||>;


ComputeMatrixPhiPow[\[CapitalDelta]max_,basisBoson_,m_]:=Do[
	ComputeMatrixPhiContract[\[CapitalDelta]max,basisBoson,{dnL,m-dnL}],
	{dnL,1,Floor[m/2]}
]


ComputeMatrixPhiContract[\[CapitalDelta]max_,basisBoson_,{dnL_,dnR_}]:=Block[
{degListL,degListR,basis1,basis2,b1,e1,b2,e2,mat,lengthListL,lengthListR,lList,lTotal,
timezero=AbsoluteTime[],nDiff,fullMatrixPhiPowTemp
},
	
	fullMatrixPhiPowTemp=Table[0,{\[CapitalDelta]max},{\[CapitalDelta]max}];
	nDiff=dnR-dnL;
	Print["t=",AbsoluteTime[]-timezero];
	Print["@ nDiff=",nDiff];
	Do[
		Print["t=",AbsoluteTime[]-timezero];
		Print["@ n=",nR];
		lengthListL=Length/@basisBoson[[1,;;(\[CapitalDelta]max-(nR-nDiff)+1),nR-nDiff]];
		degListL=Select[
			Range[0,\[CapitalDelta]max-nR+nDiff],
			lengthListL[[#+1]]>0&
		];
		lengthListR=Length/@basisBoson[[1,;;(\[CapitalDelta]max-nR+1),nR]];
		degListR=Select[
			Range[0,\[CapitalDelta]max-nR],
			lengthListR[[#+1]]>0&
		];
		phiPowMonoContraction[nR,\[CapitalDelta]max,{dnL,dnR}];
		fullMatrixPhiPowTemp[[nR-nDiff,nR]]=1/(dnL!dnR!) (4\[Pi])^((2-dnL-dnR)/2) (Table[
			{b1,e1}=binCountLengthsScalar[nR-nDiff,\[CapitalDelta]max][[deg1+1]];
			{b2,e2}=binCountLengthsScalar[nR,\[CapitalDelta]max][[deg2+1]];
			basis1=basisBoson[[1,deg1+1,nR-nDiff]];
			basis2=basisBoson[[1,deg2+1,nR]];
			factor[deg1+nR-nDiff,deg2+nR]*(basis1 . mapMonoPhiPow[[b1;;e1,b2;;e2]] . Transpose[basis2]),
			{deg1,degListL},{deg2,degListR}]//ArrayFlatten//SparseArray);
		fullMatrixPhiPowTemp[[nR,nR-nDiff]]=fullMatrixPhiPowTemp[[nR-nDiff,nR]]//Transpose,
	{nR,dnR,\[CapitalDelta]max}
	];
	fullMatrixPhiPow[{dnL,dnR}] = fullMatrixPhiPowTemp;
];


(* ::Section:: *)
(*Functions for Computing Monomial  Matrix Elements*)


(* ::Subsection:: *)
(*Monomial Matrices*)


ClearAll[binomialCoeffLists]
binomialCoeffLists[n_,\[CapitalDelta]max_]:=binomialCoeffLists[n,\[CapitalDelta]max]=CoefficientList[
	Times@@MapIndexed[(1-v^#2[[1]])^#1&,#],v,\[CapitalDelta]max+1
][[2;;]]&/@binCountListsScalar[n,\[CapitalDelta]max]//SparseArray


ClearAll[contractionFactor]
contractionFactor[{dnL_,degMaxL_},{dnR_,degMaxR_}]:=Module[
	{
		basisL = binomialCoeffLists[dnL,degMaxL+dnL],
		basisR = binomialCoeffLists[dnR,degMaxR+dnR],
		minMat = SparseArray[{{i_,j_}:>Min[i,j]},{degMaxL+dnL,degMaxR+dnR}],
		factors,getFactor
	},
	getFactor[binCountList_] := Times@@MapIndexed[
		#2[[1]]^#1&,binCountList
	];
	factors = KroneckerProduct[
		getFactor/@binCountListsScalar[dnL,degMaxL+dnL],
		getFactor/@binCountListsScalar[dnR,degMaxR+dnR]
	]//Sqrt;
	basisL . minMat . Transpose[basisR]/factors
]


phiPowMonoContraction[nR_,\[CapitalDelta]max_,{dnL_,dnR_}]:=Block[
{
matL,matR,idxGroup,lL,lR,rowShort,
k,kp,a,ap,i,ip,cListGroup,contractionList,
map,temp,idxL,idxR,
nL,degMaxL,degMaxR
},
	(*lR=Length[binCountListsScalar[nR,\[CapitalDelta]max]];
	lL=Length[binCountListsScalar[nR-dnR+dnL,\[CapitalDelta]max]];*)
	
	(*Obtain annihilation maps*)
	matR=phiAnnihilationMap[nR-dnR,nR,\[CapitalDelta]max];
	nL = nR-dnR+dnL;
	matL=phiAnnihilationMap[nR-dnR,nL,\[CapitalDelta]max];
	
	degMaxL = \[CapitalDelta]max - nL;
	degMaxR = \[CapitalDelta]max - nR;
	mapMonoPhiPow = Flatten[
		Transpose[matL] . contractionFactor[{dnL,degMaxL},{dnR,degMaxR}],
		{{1},{2,3}} ] . Flatten[matR,{{1,3},{2}}]
]


(* ::Subsection:: *)
(*Defining the action of Subscript[a, k] (see section 7.6)*)


(*phiAnnihilateTwoMap[.] works by dotting phiAnnihilateMap[.] into phiAnnihilateMap[.].
We then tabulate the matrix representation of Subscript[a, k]^2 from this object.  *)
ClearAll[phiAnnihilationMap]
ClearAll[symmetrizeContractedKs]
phiAnnihilationMap[nL_,nR_,\[CapitalDelta]max_]/;nR>nL+1:=phiAnnihilationMap[nL,nR,\[CapitalDelta]max]=Block[
{listL,listR,kmax,degMaxR},
	(*determine occupation numbers at 2 levels below nR and at nR*)
	listL=binCountListsScalar[nL,\[CapitalDelta]max];
	listR=binCountListsScalar[nR,\[CapitalDelta]max];
	
	degMaxR = \[CapitalDelta]max - nR;
	kmax = \[CapitalDelta]max - (nL+1) + 1;
	(*{kmax,{nR-nL-1,degMaxR}}//Print;*)
	Flatten[Dot[
		Transpose[phiAnnihilationMap[nL,nL+1,\[CapitalDelta]max],{1,3,2}],
		phiAnnihilationMap[nL+1,nR,\[CapitalDelta]max]
	],{{1},{3},{2,4}}] . symmetrizeContractedKs[kmax,{nR-nL-1,degMaxR}]
]
phiAnnihilationMap[nL_,nR_,\[CapitalDelta]max_]/;nR==nL+1:=phiAnnihilationMap[nL,nR,\[CapitalDelta]max]=Block[
{
aLow,aUp,ap,mat,map,lst
},

	(*determine occupation number representation of monomials, note that 
	aLow is evaluated with the argument nR-1, since the overlap can be
	nonzero only if the states differ by 1.*)
	aLow=binCountListsScalar[nR-1,\[CapitalDelta]max];
	aUp=binCountListsScalar[nR,\[CapitalDelta]max];
	
	mat[_]=0;
	
	(*go through aLow and assign a position to each occupation number *)
	MapThread[(map[#1]=#2)&,{aLow,Range[Length[aLow]]}];
	
	(*tabulate the matrix*)
	lst=Reap[Do[With[{a=aUp[[i]]},
		(
			ap=a;ap[[#]]-=1;
			mat[ Sow[{map[ap],i,#}]]=N[Sqrt[a[[#]]]];
			(*mat[ Sow[{map[ap],i,2}]]=#;*)
		)&/@
		Flatten[Position[a,_?Positive,1]]
		],{i,Length[aUp]}] ][[2,1]];
		
	SparseArray[(#->mat[#])&/@lst,{aLow//Length,aUp//Length,\[CapitalDelta]max-nR+1}]
]
symmetrizeContractedKs[kmax_,{dnR_,degMaxR_}]:=Module[
	{
		basisR = MapIndexed[PadRight[#1,degMaxR+dnR+1]->#2[[1]]&,
					binCountListsScalar[dnR,degMaxR+dnR]
				]//Association,
		basisRPlus1 = binCountListsScalar[dnR+1,degMaxR+dnR+1],
		ap,pos
	},
	(*basisRPlus1//Print;*)
	(*basisR//Length//Print;
	basisRPlus1//Length//Print;*)
	Flatten[SparseArray[MapIndexed[
		(pos = Position[#1,Except[0],1,Heads->False]//Flatten;
		Table[
			ap = #1;ap[[j]]-=1;
			{j,basisR[ap],#2[[1]]}->1,
			{j,pos}
		])&,
		basisRPlus1
	]//Flatten,{kmax,Length[basisR],Length[basisRPlus1]}],1]

]


(* ::Section:: *)
(*Factors and number of states*)


(*Normalization factor of states*)
factor[\[CapitalDelta]_,\[CapitalDelta]p_]:=factor[\[CapitalDelta],\[CapitalDelta]p]=Sqrt[ Gamma[2\[CapitalDelta]]Gamma[2\[CapitalDelta]p] ] * (-1)^(\[CapitalDelta]-\[CapitalDelta]p) / Gamma[\[CapitalDelta]+\[CapitalDelta]p-1];


(*Number of states at a given particle sector and degree *)
ClearAll[numStates]
numStates[n_,bDeg_]:=With[
	{\[CapitalDelta]=n+bDeg},
	Coefficient[Normal@Series[x^n Product[1/(1-x^k),{k,2,n}],{x,0,\[CapitalDelta]}],x^\[CapitalDelta]]
];


ClearAll[binCountListsScalar,binCountLengthsScalar];
binCountListsScalar[n_,\[CapitalDelta]max_]:=binCountListsScalar[n,\[CapitalDelta]max]=cfBinCount[#,\[CapitalDelta]max]&/@Flatten[Reap[
binCountLengthsScalar[n,\[CapitalDelta]max]=Thread[{Most[#]+1,Rest[#]}]&@Prepend[Accumulate@Table[
Length@Sow[IntegerPartitions[\[CapitalDelta],{n}]],
{\[CapitalDelta],n,\[CapitalDelta]max,1}
],0]
 ][[2,1]],1];


(* ::Section:: *)
(*End*)


End[]


EndPackage[]
