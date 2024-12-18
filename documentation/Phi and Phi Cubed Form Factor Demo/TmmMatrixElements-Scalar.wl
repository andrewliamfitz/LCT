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


BeginPackage["scalarMatrixElements`",{"utilities`"}]


ComputeTmmNtoNMatrix::usage
ComputeTmmNtoNPlus2Matrix::usage
ComputeDphiNtoNPlus1Matrix::usage
fullTmmNtoNMatrix::usage
fullTmmNtoNPlus2Matrix::usage
fullDphiNtoNPlus1Matrix::usage


Begin["`Private`"]


(* ::Section:: *)
(*Main Functions for Computing (\[PartialD]\[Phi])^2 Matrix Elements*)


(*note that the argument \[CapitalDelta]max should be compatible with basisBoson*)

ComputeTmmNtoNMatrix[\[CapitalDelta]max_,basisBoson_]:=Block[
{degList,basis1,basis2,b1,e1,b2,e2,mat,lengthList,lList,lTotal,
timezero=AbsoluteTime[]
},
	
	(*define an empty array which will be populated by the matrix
	elements*)
	
	fullTmmNtoNMatrix=Table[0,{\[CapitalDelta]max},{\[CapitalDelta]max}];
	Do[
		Print["t=",AbsoluteTime[]-timezero];
		Print["@ n=",n];
		
		(*length of basis for each particle sector n; lengthList and degList
		help us determine which degrees appear at each particle sector and
		at each \[CapitalDelta]max. We can then interate over the degrees in degList when
		computing the matrix elements*)
		
		lengthList=Length/@basisBoson[[1,;;(\[CapitalDelta]max-n+1),n]];
		(*list of degrees for a given particle sector (note that degree = \[CapitalDelta]max-n)*)
		
		degList=Select[
			Range[0,\[CapitalDelta]max-n],
			lengthList[[#+1]]>0&
		];
		
		(*compute monomial mass matrix*)
		
		mat=TmmNtoN[n,\[CapitalDelta]max];

		(*and then determine the final mass matrix by dotting in basis states.
		binCountLengthsScalar is used to determine the correct dimensions of the
		monomial matrix elements, to accommodate different values of \[CapitalDelta]max.*)
		
		(* The prefactor of 2 in the next line is because dphi can contract in either direction *)

		fullTmmNtoNMatrix[[n,n]]=2 Table[
			{b1,e1}=binCountLengthsScalar[n,\[CapitalDelta]max][[deg1+1]];
			{b2,e2}=binCountLengthsScalar[n,\[CapitalDelta]max][[deg2+1]];
			basis1=basisBoson[[1,deg1+1,n]];
			basis2=basisBoson[[1,deg2+1,n]];
			(*factor[deg1+n,deg2+n]**)(basis1.mat[[b1;;e1,b2;;e2]].Transpose[basis2]),
		{deg1,degList},{deg2,degList}]//ArrayFlatten//SparseArray,
	{n,1,\[CapitalDelta]max}
	]
	
];


ComputeTmmNtoNPlus2Matrix[\[CapitalDelta]max_,basisBoson_]:=Block[
{degListL,degListR,basis1,basis2,b1,e1,b2,e2,mat,lengthListL,lengthListR,lList,lTotal,
timezero=AbsoluteTime[]
},
	
	(*initialize n-to-(n+2) matrix. Note that this is a square matrix,
	as it is the n-to-(n+2) contribution to the Hamiltonian. "Building
	block" matrices for each particle sector will not necessarily be
	square for the n-to-(n+2) matrix elements.*)
	
	
	fullTmmNtoNPlus2Matrix=Table[0,{\[CapitalDelta]max},{\[CapitalDelta]max}];

	(*and go through each sector, compute monomial matrix elements
	and dot into basis states to obtain the final matrix. Note that
	there are some slight differences from ComputePhi4NtoNMatrix[.]
	due to the fact that the n particle sector has a different number
	of states compared to the (n+2) particle sector.*)
	
	Do[
		Print["t=",AbsoluteTime[]-timezero];
		Print["@ n=",n];
		lengthListL=Length/@basisBoson[[1,;;(\[CapitalDelta]max-n+2+1),n-2]];
		degListL=Select[
			Range[0,\[CapitalDelta]max-n+2],
			lengthListL[[#+1]]>0&
		];
		lengthListR=Length/@basisBoson[[1,;;(\[CapitalDelta]max-n+1),n]];
		degListR=Select[
			Range[0,\[CapitalDelta]max-n],
			lengthListR[[#+1]]>0&
		];
		(* The minus sign here was determined by comparing final results 
		for form factors against Feynman diagrams.  Probably it comes from the fact
		 that dphi dphi for n\[Rule]n go in opposite directions, whereas for n\[Rule]n+2 they go
		 in the same direction, which causes a relative minus sign
		  *)
		TmmNtoNPlus2[n,\[CapitalDelta]max];
		fullTmmNtoNPlus2Matrix[[n-2,n]]=(*1/6 1/(4\[Pi])*) -(Table[
			{b1,e1}=binCountLengthsScalar[n-2,\[CapitalDelta]max][[deg1+1]];
			{b2,e2}=binCountLengthsScalar[n,\[CapitalDelta]max][[deg2+1]];
			basis1=basisBoson[[1,deg1+1,n-2]];
			basis2=basisBoson[[1,deg2+1,n]];
			(basis1.mapMonoTmmNtoNPlus2[[b1;;e1,b2;;e2]].Transpose[basis2]),
			{deg1,degListL},{deg2,degListR}]//ArrayFlatten//SparseArray);
		fullTmmNtoNPlus2Matrix[[n,n-2]]=fullTmmNtoNPlus2Matrix[[n-2,n]]//Transpose,
	{n,3,\[CapitalDelta]max}
	];
	
	
];


ComputeDphiNtoNPlus1Matrix[\[CapitalDelta]max_,basisBoson_]:=Block[
{degListL,degListR,basis1,basis2,b1,e1,b2,e2,mat,lengthListL,lengthListR,lList,lTotal,
timezero=AbsoluteTime[]
},
	
	(*initialize n-to-(n+1) matrix. Note that this is a square matrix,
	as it is the n-to-(n+1) contribution to the Hamiltonian. "Building
	block" matrices for each particle sector will not necessarily be
	square for the n-to-(n+1) matrix elements.*)
	
	
	fullDphiNtoNPlus1Matrix=Table[0,{\[CapitalDelta]max},{\[CapitalDelta]max}];

	(*and go through each sector, compute monomial matrix elements
	and dot into basis states to obtain the final matrix. Note that
	there are some slight differences from ComputePhi4NtoNMatrix[.]
	due to the fact that the n particle sector has a different number
	of states compared to the (n+1) particle sector.*)
	
	Do[
		Print["t=",AbsoluteTime[]-timezero];
		Print["@ n=",n];
		lengthListL=Length/@basisBoson[[1,;;(\[CapitalDelta]max-n+1+1),n-1]];
		degListL=Select[
			Range[0,\[CapitalDelta]max-n+1],
			lengthListL[[#+1]]>0&
		];
		lengthListR=Length/@basisBoson[[1,;;(\[CapitalDelta]max-n+1),n]];
		degListR=Select[
			Range[0,\[CapitalDelta]max-n],
			lengthListR[[#+1]]>0&
		];
		DphiNtoNPlus1[n,\[CapitalDelta]max];
		fullDphiNtoNPlus1Matrix[[n-1,n]]=(*1/6 1/(4\[Pi])*) (Table[
			{b1,e1}=binCountLengthsScalar[n-1,\[CapitalDelta]max][[deg1+1]];
			{b2,e2}=binCountLengthsScalar[n,\[CapitalDelta]max][[deg2+1]];
			basis1=basisBoson[[1,deg1+1,n-1]];
			basis2=basisBoson[[1,deg2+1,n]];
			(basis1.mapMonoDphiNtoNPlus1[[b1;;e1,b2;;e2]].Transpose[basis2]),
			{deg1,degListL},{deg2,degListR}]//ArrayFlatten//SparseArray);
		fullDphiNtoNPlus1Matrix[[n,n-1]]=fullDphiNtoNPlus1Matrix[[n-1,n]]//Transpose,
	{n,2,\[CapitalDelta]max}
	];
	
	
];


(* ::Section:: *)
(*Functions for Computing Monomial  Matrix Elements*)


(* ::Subsection:: *)
(*Defining the action of Subscript[a, k] (see section 7.6)*)


(*phiAnnihilationMap[.] determines the action of Subscript[a, k] on monomials.
It takes as input nR (total occupation number) and \[CapitalDelta]max. It outputs
a sparse array that is the representation of Subscript[a, k] on a set of monomials
labeled by their occupation number.*)
ClearAll[phiAnnihilateMap];
phiAnnihilateMap[nR_,\[CapitalDelta]max_]:=phiAnnihilateMap[nR,\[CapitalDelta]max]=Block[
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
			mat[ Sow[{map[ap],i,1}]]=N[Sqrt[a[[#]]]];
			mat[ Sow[{map[ap],i,2}]]=#;
		)&/@
		Flatten[Position[a,_?Positive,1]]
		],{i,Length[aUp]}] ][[2,1]];
		
	SparseArray[(#->mat[#])&/@lst,{aLow//Length,aUp//Length,2}]
]


(*phiAnnihilateTwoMap[.] works by dotting phiAnnihilateMap[.] into phiAnnihilateMap[.].
We then tabulate the matrix representation of Subscript[a, k]^2 from this object.  *)
phiAnnihilateTwoMap[nR_,\[CapitalDelta]max_]:=Block[
{aMat,aIdx,listL,listR,mat},
	(*determine occupation numbers at 2 levels below nR and at nR*)
	listL=binCountListsScalar[nR-2,\[CapitalDelta]max];
	listR=binCountListsScalar[nR,\[CapitalDelta]max];
	
	(*First we obtain the matrix given by dotting phiAnnihilateMap[nR-1,.] and phiAnnihilateMap[nR,.]*)
	aMat=phiAnnihilateMap[nR-1,\[CapitalDelta]max][[;;,;;,1]].phiAnnihilateMap[nR,\[CapitalDelta]max][[;;,;;,1]];
	
	(*Extract the positions where there are non-zero elements*)
	aIdx=aMat["NonzeroPositions"];
	
	(* *)
	mat=SparseArray[
		({#1,#2,2}->g@@cfBinReconstruct[
		listR[[#2]]-listL[[#1]]
		])&@@@aIdx,
		{Length[listL],Length[listR],2}
	];
mat[[;;,;;,1]]=aMat;
mat
]


(*phiAnnihilateThreeMap[.] is implemented in the same way as phiAnnihilateTwoMap[.],
with the only difference being that we now allow for matrix elements which differ by
3 in total occupation number.  *)
phiAnnihilateThreeMap[nR_,\[CapitalDelta]max_]:=Block[
{aMat,aIdx,listL,listR,mat},
	listL=binCountListsScalar[nR-3,\[CapitalDelta]max];
	listR=binCountListsScalar[nR,\[CapitalDelta]max];
	aMat=phiAnnihilateMap[nR-2,\[CapitalDelta]max][[;;,;;,1]].phiAnnihilateTwoMap[nR,\[CapitalDelta]max][[;;,;;,1]];
	aIdx=aMat["NonzeroPositions"];
	mat=SparseArray[
		({#1,#2,2}->g@@cfBinReconstruct[
		listR[[#2]]-listL[[#1]]
		])&@@@aIdx,
		{Length[listL],Length[listR],2}
	];
	mat[[;;,;;,1]]=aMat;
	mat
]


(* ::Subsection:: *)
(*Monomial Matrices*)


(*N to N Tmm term. Its output is a matrix that is the monomial N-to-N Tmm
term matrix elements.*)

TmmNtoN[nR_,\[CapitalDelta]max_]:=Block[
{
mat,idxGroup,l,mass,rowShort,
k,kp,a,ap,i,ip,cListGroup,contractionList,
map,temp
},
	(*Determine first the action of Subscript[a, k], which we will dot into the active part
	of the matrix elements from radial quantization*)
	l=Length[binCountListsScalar[nR,\[CapitalDelta]max]];
	mat=phiAnnihilateMap[nR,\[CapitalDelta]max];
	idxGroup=mat[[;;,;;,1]]["NonzeroPositions"];
	
	(*these next few lines help organize the procedure of taking
	the annihilation map and dotting it into the active part.
	cListGroup is a list of entries which includes the positions
	and nonzero values of the annihilation map.*)
	
	cListGroup=SplitBy[Join[
		idxGroup//Transpose,
		{
			Extract[mat[[;;,;;,1]],idxGroup],
			Extract[mat[[;;,;;,2]],idxGroup]
		}
	]//Transpose,First][[;;,;;,{2,3,4}]];
	
	(*Then construct the monomial matrix elements*)
	temp=Reap[
	Do[
		map[_]=0;
		Do[
			{i,a,k}=c1;
			{ip,ap,kp}=c2;

			map[Sow[{i,ip}]]+=(a*ap)Sqrt[N[k kp]];,
		{c1,cList},
		{c2,cList}
		] ,
	{cList,cListGroup}] ][[2,1]];
	
	SparseArray[(#->map[#])&/@temp,{l,l}]
]


(*Active contribution for n-to-(n+2) interaction*)



ClearAll[TmmContractNN2]
TmmContractNN2=Compile[{{k1p,_Real},{k2p,_Real}},Sqrt[k1p k2p],
CompilationTarget->"C",
CompilationOptions->{"ExpressionOptimization" -> True}
]


(*Active contribution for n-to-(n+1) interaction*)



ClearAll[DphiContractNN1]
DphiContractNN1=Compile[{{k1p,_Real}},Sqrt[k1p],
CompilationTarget->"C",
CompilationOptions->{"ExpressionOptimization" -> True}
]


(*The final monomial routine, TmmNtoNPlus2[.] follows the same structure
as the n-to-n case but computes the matrix elements for n-to-(n+2). Note
that the major difference in practice in the code is just accounting for
different dimensions of the matrices for the dotting procedure. *)

TmmNtoNPlus2[nR_,\[CapitalDelta]max_]:=Block[
{
matL,matR,idxGroup,lL,lR,rowShort,
k,kp,a,ap,i,ip,cListGroup,contractionList,
map,temp,idxL,idxR
},
	lR=Length[binCountListsScalar[nR,\[CapitalDelta]max]];
	lL=Length[binCountListsScalar[nR-2,\[CapitalDelta]max]];
	
	(*Obtain annihilation maps*)
	matR=phiAnnihilateTwoMap[nR,\[CapitalDelta]max];
	matL=SparseArray[IdentityMatrix[lL]];
	
	(*Extract positions and non-zero elements for left and right matrices*)
	cListGroup=Reap[Do[
		idxL=matL[[row,;;]]["NonzeroPositions"]//Flatten;
		idxR=matR[[row,;;,1]]["NonzeroPositions"]//Flatten;
		If[idxL!={}&&idxR!={},
		{
			{Join[
			idxL,
			matL[[row,idxL]]
			]},
			Join[
			{idxR},
			matR[[row,idxR]]//Transpose
			]//Transpose
		}//Sow
		],
		{row,Length[binCountListsScalar[nR-2,\[CapitalDelta]max]]}]
	][[2,1]];
	
	(* and then build the final monomial n-to-(n+2) matrix*)
	ClearAll[mapMonoTmmNtoNPlus2];
	map[__]=0;
	temp=(Transpose[matL[[;;,;;]]].matR[[;;,;;,1]])["NonzeroPositions"];
	Do[
		Do[
			{i,a}=c1;
			{ip,ap,kp}=c2;
			map[i,ip]+=(a*ap)TmmContractNN2[Sequence@@kp],
		{c1,cList[[1]]},
		{c2,cList[[2]]}
		],
	{cList,cListGroup}];
	mapMonoTmmNtoNPlus2=SparseArray[Thread[temp->(map@@@temp)],{lL,lR}];
]


(*The final monomial routine, DphiNtoNPlus1[.] follows the same structure
as the n-to-n case but computes the matrix elements for n-to-(n+1). Note
that the major difference in practice in the code is just accounting for
different dimensions of the matrices for the dotting procedure. *)

DphiNtoNPlus1[nR_,\[CapitalDelta]max_]:=Block[
{
matL,matR,idxGroup,lL,lR,rowShort,
k,kp,a,ap,i,ip,cListGroup,contractionList,
map,temp,idxL,idxR
},
	lR=Length[binCountListsScalar[nR,\[CapitalDelta]max]];
	lL=Length[binCountListsScalar[nR-1,\[CapitalDelta]max]];
	
	(*Obtain annihilation maps*)
	matR=phiAnnihilateMap[nR,\[CapitalDelta]max];
	matL=SparseArray[IdentityMatrix[lL]];
	
	(*Extract positions and non-zero elements for left and right matrices*)
	cListGroup=Reap[Do[
		idxL=matL[[row,;;]]["NonzeroPositions"]//Flatten;
		idxR=matR[[row,;;,1]]["NonzeroPositions"]//Flatten;
		If[idxL!={}&&idxR!={},
		{
			{Join[
			idxL,
			matL[[row,idxL]]
			]},
			Join[
			{idxR},
			matR[[row,idxR]]//Transpose
			]//Transpose
		}//Sow
		],
		{row,Length[binCountListsScalar[nR-1,\[CapitalDelta]max]]}]
	][[2,1]];
	
	(* and then build the final monomial n-to-(n+1) matrix*)
	ClearAll[mapMonoDphiNtoNPlus1];
	map[__]=0;
	temp=(Transpose[matL[[;;,;;]]].matR[[;;,;;,1]])["NonzeroPositions"];
	Do[
		Do[
			{i,a}=c1;
			{ip,ap,kp}=c2;
			map[i,ip]+=(a*ap)DphiContractNN1[Sequence@@kp],
		{c1,cList[[1]]},
		{c2,cList[[2]]}
		],
	{cList,cListGroup}];
	mapMonoDphiNtoNPlus1=SparseArray[Thread[temp->(map@@@temp)],{lL,lR}];
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
