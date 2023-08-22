(* ::Package:: *)

(* ::Chapter:: *)
(*Utility functions*)


BeginPackage["utilities`"]


flattenMixonMatrix::usage


flattenMixonStates::usage


cfBinCount::usage


cfBinReconstruct::usage


monomialsBoson::usage


monomialsFermion::usage


Begin["`Private`"]


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


(* ::Chapter:: *)
(*Main Package*)


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
(*Main Functions for Computing \[PartialD]\[Phi] and \[Phi]^3 Matrix Elements*)


ComputeDphiNtoNPlus1MatrixNmax[\[CapitalDelta]max_,nmax_,basisBoson_]:=Block[
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
			(basis1 . mapMonoDphiNtoNPlus1[[b1;;e1,b2;;e2]] . Transpose[basis2]),
			{deg1,degListL},{deg2,degListR}]//ArrayFlatten//SparseArray);
		fullDphiNtoNPlus1Matrix[[n,n-1]]=fullDphiNtoNPlus1Matrix[[n-1,n]]//Transpose,
	{n,2,Min[\[CapitalDelta]max,nmax]}
	];
	
	
];


ComputePhi3MatrixNmax[\[CapitalDelta]max_,nmax_,basisBoson_]:=Block[
{degListL,degListR,basis1,basis2,b1,e1,b2,e2,mat,lengthListL,lengthListR,lList,lTotal,
timezero=AbsoluteTime[]
},
	
	(*initialize n-to-(n+1) matrix. Note that this is a square matrix,
	as it is the n-to-(n+1) contribution to the Hamiltonian. "Building
	block" matrices for each particle sector will not necessarily be
	square for the n-to-(n+1) matrix elements.*)
	
	emptyAssoc=AssociationThread[{#}&/@(Append[Range[\[CapitalDelta]max*2],0])->0]//KeySort;
	fullPhi3Matrix=Table[emptyAssoc,{\[CapitalDelta]max},{\[CapitalDelta]max}];

	
	(*n-1->n part of the matrix*)
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
		dPhiCubedNtoNPlus1[n,\[CapitalDelta]max];
		fullPhi3Matrix[[n-1,n]]=(*1/6 1/(4\[Pi])*) (Table[
			{b1,e1}=binCountLengthsScalar[n-1,\[CapitalDelta]max][[deg1+1]];
			{b2,e2}=binCountLengthsScalar[n,\[CapitalDelta]max][[deg2+1]];
			basis1=basisBoson[[1,deg1+1,n-1]];
			basis2=basisBoson[[1,deg2+1,n]];
			factor[deg1+n-1,deg2+n]*(-1)^(deg1+deg2-1) (basis1 . mapMonodPhiCubedNtoNPlus1[[b1;;e1,b2;;e2]] . Transpose[basis2]),
			{deg1,degListL},{deg2,degListR}]//ArrayFlatten//SparseArray),
	{n,2,Min[\[CapitalDelta]max,nmax]}
	];
	
	(*n->n-1 part of the matrix*)
	Do[
		Print["t=",AbsoluteTime[]-timezero];
		Print["@ n=",n];
		lengthListL=Length/@basisBoson[[1,;;(\[CapitalDelta]max-n+1),n]];
		degListL=Select[
			Range[0,\[CapitalDelta]max-n],
			lengthListL[[#+1]]>0&
		];
		lengthListR=Length/@basisBoson[[1,;;(\[CapitalDelta]max-n+1+1),n-1]];
		degListR=Select[
			Range[0,\[CapitalDelta]max-n+1],
			lengthListR[[#+1]]>0&
		];
		dPhiCubedNPlus1toN[n-1,\[CapitalDelta]max];
		fullPhi3Matrix[[n,n-1]]=(*1/6 1/(4\[Pi])*) (Table[
			{b1,e1}=binCountLengthsScalar[n,\[CapitalDelta]max][[deg1+1]];
			{b2,e2}=binCountLengthsScalar[n-1,\[CapitalDelta]max][[deg2+1]];
			basis1=basisBoson[[1,deg1+1,n]];
			basis2=basisBoson[[1,deg2+1,n-1]];
			factor[deg1+n,deg2+n-1]*(-1)^(deg1+deg2-1)*(basis1 . mapMonodPhiCubedNPlus1toN[[b1;;e1,b2;;e2]] . Transpose[basis2]),
			{deg1,degListL},{deg2,degListR}]//ArrayFlatten//SparseArray),
	{n,2,Min[\[CapitalDelta]max,nmax]}
	];
	
	(*n-3->n part of the matrix*)
	Do[
		Print["t=",AbsoluteTime[]-timezero];
		Print["@ n=",n];
		lengthListL=Length/@basisBoson[[1,;;(\[CapitalDelta]max-n+3+1),n-3]];
		degListL=Select[
			Range[0,\[CapitalDelta]max-n+3],
			lengthListL[[#+1]]>0&
		];
		lengthListR=Length/@basisBoson[[1,;;(\[CapitalDelta]max-n+1),n]];
		degListR=Select[
			Range[0,\[CapitalDelta]max-n],
			lengthListR[[#+1]]>0&
		];
		dPhiCubedNtoNPlus3[n,\[CapitalDelta]max];
		fullPhi3Matrix[[n-3,n]]=(*1/6 1/(4\[Pi])*) (Table[
			{b1,e1}=binCountLengthsScalar[n-3,\[CapitalDelta]max][[deg1+1]];
			{b2,e2}=binCountLengthsScalar[n,\[CapitalDelta]max][[deg2+1]];
			basis1=basisBoson[[1,deg1+1,n-3]];
			basis2=basisBoson[[1,deg2+1,n]];
			1/3 factor[deg1+n-3,deg2+n]*(-1)^(deg1+deg2-1)*(basis1 . mapMonodPhiCubedNtoNPlus3[[b1;;e1,b2;;e2]] . Transpose[basis2]),
			{deg1,degListL},{deg2,degListR}]//ArrayFlatten//SparseArray),
	{n,4,Min[\[CapitalDelta]max,nmax]}
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
			mat[ Sow[{map[ap],i,1}]]=Sqrt[a[[#]]];
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
	aMat=phiAnnihilateMap[nR-1,\[CapitalDelta]max][[;;,;;,1]] . phiAnnihilateMap[nR,\[CapitalDelta]max][[;;,;;,1]];
	
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
	aMat=phiAnnihilateMap[nR-2,\[CapitalDelta]max][[;;,;;,1]] . phiAnnihilateTwoMap[nR,\[CapitalDelta]max][[;;,;;,1]];
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


ClearAll[DphiContractNN1]
DphiContractNN1=Compile[{{k1p,_Real}},Sqrt[k1p],
CompilationTarget->"C",
CompilationOptions->{"ExpressionOptimization" -> True}
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
	temp=(Transpose[matL[[;;,;;]]] . matR[[;;,;;,1]])["NonzeroPositions"];
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


(*N to N+1 dPhiCubed term. Its output is a matrix that is the monomial N-to-N+1 dPhiCubed
term matrix elements.*)

dPhiCubedNtoNPlus1[nR_,\[CapitalDelta]max_]:=Block[
{
matL,matR,idxGroup,lL,lR,rowShort,
k,kp,a,ap,i,ip,cListGroup,contractionList,
map,temp,idxL,idxR,binListL,binListR,rankList,delList
},
	binListR=binCountListsScalar[nR,\[CapitalDelta]max];
	binListL=binCountListsScalar[nR-1,\[CapitalDelta]max];
	lR=Length[binListR];
	lL=Length[binListL];
	
	emptyAssoc=AssociationThread[{#}&/@(Append[Range[\[CapitalDelta]max*2],0])->0];
	
	(*Obtain annihilation maps*)
	matR=phiAnnihilateTwoMap[nR,\[CapitalDelta]max];
	matL=phiAnnihilateMap[nR-1,\[CapitalDelta]max];
	
	(*Extract positions and non-zero elements for left and right matrices*)
	cListGroup=Reap[Do[
		idxL=matL[[row,;;,1]]["NonzeroPositions"]//Flatten;
		idxR=matR[[row,;;,1]]["NonzeroPositions"]//Flatten;
		If[idxL!={}&&idxR!={},
		{
			Join[
			{idxL},
			matL[[row,idxL]]//Transpose
			]//Transpose,
			Join[
			{idxR},
			matR[[row,idxR]]//Transpose
			]//Transpose
		}//Sow
		],
		{row,Length[binCountListsScalar[nR-2,\[CapitalDelta]max]]}]
	][[2,1]];
	
	(* and then build the final monomial n-to-(n+1) matrix*)
	ClearAll[mapMonodPhiCubedNtoNPlus1];
	map[__]=0;
	temp=(Transpose[matL[[;;,;;,1]]] . matR[[;;,;;,1]])["NonzeroPositions"];
	delList={};
	rankList=Range[\[CapitalDelta]max];
	Do[
		Do[
			{i,a,k}=c1;
			{ip,ap,kp}=c2;
			delIn=binListL[[i]] . rankList;
			delOut=binListR[[ip]] . rankList;
			(*Print["c1",c1,"c2",c2,"delIn",delIn,"delOut",delOut];*)
			AppendTo[delList,{i,ip,delIn+delOut-2}];
			(*map[i,ip]+=(a*ap)1/(Sqrt[Times@@kp]*Sqrt[k])*PadRight[CoefficientList[Phi3ResLookupTable[k,kp[[1]],kp[[2]],delIn+delOut-2],q],delIn+delOut-2]*)
			map[i,ip]+=(a*ap)1/(Sqrt[Times@@kp]*Sqrt[k])*PhiCubedResidueLookupTableB[k,-kp[[1]],-kp[[2]],delIn+delOut-2],
		{c1,cList[[1]]},
		{c2,cList[[2]]}
		],
	{cList,cListGroup}];
	delList=delList//DeleteDuplicates;
	(*Do[map[delList[[n,1]],delList[[n,2]]]=AssociationThread[Range[delList[[n,3]]],map[delList[[n,1]],delList[[n,2]]]],{n,1,delList//Length}]*);
	mapMonodPhiCubedNtoNPlus1=SparseArray[Thread[temp->(map@@@temp)],{lL,lR}];
]


(*N+1 to N dPhiCubed term. Its output is a matrix that is the monomial N+1-to-N dPhiCubed
term matrix elements.*)

dPhiCubedNPlus1toN[nR_,\[CapitalDelta]max_]:=Block[
{
matL,matR,idxGroup,lL,lR,rowShort,
k,kp,a,ap,i,ip,cListGroup,contractionList,
map,temp,idxL,idxR,binListL,binListR,rankList,delList
},
	binListR=binCountListsScalar[nR,\[CapitalDelta]max];
	binListL=binCountListsScalar[nR+1,\[CapitalDelta]max];
	lR=Length[binListR];
	lL=Length[binListL];
	
	emptyAssoc=AssociationThread[{#}&/@(Append[Range[\[CapitalDelta]max*2],0])->0];
	
	(*Obtain annihilation maps*)
	matR=phiAnnihilateMap[nR,\[CapitalDelta]max];
	matL=phiAnnihilateTwoMap[nR+1,\[CapitalDelta]max];
	
	(*Extract positions and non-zero elements for left and right matrices*)
	cListGroup=Reap[Do[
		idxL=matL[[row,;;,1]]["NonzeroPositions"]//Flatten;
		idxR=matR[[row,;;,1]]["NonzeroPositions"]//Flatten;
		If[idxL!={}&&idxR!={},
		{
			Join[
			{idxL},
			matL[[row,idxL]]//Transpose
			]//Transpose,
			Join[
			{idxR},
			matR[[row,idxR]]//Transpose
			]//Transpose
		}//Sow
		],
		{row,Length[binCountListsScalar[nR-1,\[CapitalDelta]max]]}]
	][[2,1]];
	
	(* and then build the final monomial n-to-(n-1) matrix*)
	ClearAll[mapMonodPhiCubedNPlus1toN];
	map[__]=0;
	temp=(Transpose[matL[[;;,;;,1]]] . matR[[;;,;;,1]])["NonzeroPositions"];
	delList={};
	rankList=Range[\[CapitalDelta]max];
	Do[
		Do[
			{i,a,k}=c1;
			{ip,ap,kp}=c2;
			delIn=binListL[[i]] . rankList;
			delOut=binListR[[ip]] . rankList;
			(*Print["c1",c1,"c2",c2,"delIn",delIn,"delOut",delOut];*)
			AppendTo[delList,{i,ip,delIn+delOut-2}];
			map[i,ip]+=(a*ap)1/(Sqrt[Times@@k]*Sqrt[kp])PhiCubedResidueLookupTableB[-kp,k[[1]],k[[2]],delIn+delOut-2],
		{c1,cList[[1]]},
		{c2,cList[[2]]}
		],
	{cList,cListGroup}];
	delList=delList//DeleteDuplicates;
	mapMonodPhiCubedNPlus1toN=SparseArray[Thread[temp->(map@@@temp)],{lL,lR}];
]


(*N-3 to N dPhiCubed term. Its output is a matrix that is the monomial N-to-N+1 dPhiCubed
term matrix elements.*)

dPhiCubedNtoNPlus3[nR_,\[CapitalDelta]max_]:=Block[
{
matL,matR,idxGroup,lL,lR,rowShort,
k,kp,a,ap,i,ip,cListGroup,contractionList,
map,temp,idxL,idxR,binListL,binListR,rankList,delList
},
	binListR=binCountListsScalar[nR,\[CapitalDelta]max];
	binListL=binCountListsScalar[nR-3,\[CapitalDelta]max];
	lR=Length[binListR];
	lL=Length[binListL];
	
	emptyAssoc=AssociationThread[{#}&/@(Append[Range[\[CapitalDelta]max*2],0])->0];
	
	(*Obtain annihilation maps*)
	matR=phiAnnihilateThreeMap[nR,\[CapitalDelta]max];
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
		{row,Length[binCountListsScalar[nR-3,\[CapitalDelta]max]]}]
	][[2,1]];
	
	(* and then build the final monomial n-to-(n+1) matrix*)
	ClearAll[mapMonodPhiCubedNtoNPlus3];
	map[__]=0;
	temp=(Transpose[matL[[;;,;;]]] . matR[[;;,;;,1]])["NonzeroPositions"];
	delList={};
	rankList=Range[\[CapitalDelta]max];
	Do[
		Do[
			{i,a}=c1;
			{ip,ap,kp}=c2;
			delIn=binListL[[i]] . rankList;
			delOut=binListR[[ip]] . rankList;
			(*Print["c1",c1,"c2",c2,"delIn",delIn,"delOut",delOut];*)
			AppendTo[delList,{i,ip,delIn+delOut-2}];
			(*Print[PadRight[CoefficientList[Phi3ResPlus3LookupTable[kp[[1]],kp[[2]],kp[[3]],delIn+delOut-2],q],delIn+delOut-2]];*)
			map[i,ip]+=(a*ap)1/(Sqrt[Times@@kp])*PhiCubedResidueLookupTableB[-kp[[1]],-kp[[2]],-kp[[3]],delIn+delOut-2],
		{c1,cList[[1]]},
		{c2,cList[[2]]}
		],
	{cList,cListGroup}];
	delList=delList//DeleteDuplicates;
	mapMonodPhiCubedNtoNPlus3=SparseArray[Thread[temp->(map@@@temp)],{lL,lR}];
]


(* ::Section:: *)
(*End*)


End[]


EndPackage[]
