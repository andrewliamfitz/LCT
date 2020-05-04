(* ::Package:: *)

(* ::Section::Closed:: *)
(*Main Functions for Computing \[Phi]^2 and \[Phi]^4 Matrix Elements*)


(*note that the argument \[CapitalDelta]max should be compatible with basisBoson*)

ComputeScalarMassMatrix[\[CapitalDelta]max_,basisBoson_]:=Block[
{degList,basis1,basis2,b1,e1,b2,e2,mat,lengthList,lList,lTotal,
timezero=AbsoluteTime[]
},

	(*lList keeps track of how many states at each particle sector
	there are. This is used to determine where in the final matrices
	the matrix elements of each particle sector appear. *)
	
	lList=Thread[{Prepend[Most[#]+1,1],#}]&@Accumulate[Table[
	Table[numStates[n,deg],{deg,0,\[CapitalDelta]max-n}]//Total, {n,1,\[CapitalDelta]max}] ];
	lTotal=lList[[-1,2]];
	
	(*define an empty array which will be populated by the matrix
	elements*)
	
	fullMassMatrix=SparseArray[{},{lTotal,lTotal}];
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
		
		mat=massNtoN[n,\[CapitalDelta]max];

		(*and then determine the final mass matrix by dotting in basis states.
		binCountLengthsScalar is used to determine the correct dimensions of the
		monomial matrix elements, to accommodate different values of \[CapitalDelta]max.*)

		fullMassMatrix[[
			lList[[n,1]];;lList[[n,2]],
			lList[[n,1]];;lList[[n,2]]
		]]=Table[
			{b1,e1}=binCountLengthsScalar[n,\[CapitalDelta]max][[deg1+1]];
			{b2,e2}=binCountLengthsScalar[n,\[CapitalDelta]max][[deg2+1]];
			basis1=basisBoson[[1,deg1+1,n]];
			basis2=basisBoson[[1,deg2+1,n]];
			factor[deg1+n,deg2+n]*(basis1.mat[[b1;;e1,b2;;e2]].Transpose[basis2]),
		{deg1,degList},{deg2,degList}]//ArrayFlatten,
	{n,1,\[CapitalDelta]max}
	]
	
];


(*Note that ComputePhi4NtoNMatrix[.] is implemented in a way that closely resembles
ComputeScalarMassMatrix[.]. The only major difference is that we compute the 
n-to-n matrices instead of the mass matrices. *)

ComputePhi4NtoNMatrix[\[CapitalDelta]max_,basisBoson_]:=Block[
{degList,basis1,basis2,b1,e1,b2,e2,mat,lengthList,lList,lTotal,
timezero=AbsoluteTime[]
},
	(*Again, lList keeps track of the dimensionality of the basis
	at different particle sectors.*)
	
	lList=Thread[{Prepend[Most[#]+1,1],#}]&@Accumulate[Table[
	Table[numStates[n,deg],{deg,0,\[CapitalDelta]max-n}]//Total, {n,1,\[CapitalDelta]max}] ];
	lTotal=lList[[-1,2]];
	
	(*Initialize the n-to-n matrix*)
	
	fullPhi4NtoNMatrix=SparseArray[{},{lTotal,lTotal}];
	
	(*and again go through each particle number sector, computing 
	the matrix elements *)
	Do[
		Print["t=",AbsoluteTime[]-timezero];
		Print["@ n=",n];
		lengthList=Length/@basisBoson[[1,;;(\[CapitalDelta]max-n+1),n]];
		degList=Select[
			Range[0,\[CapitalDelta]max-n],
			lengthList[[#+1]]>0&
		];
		
		(*compute the monomial n-to-n matrix elements, the output of which is
		the matrix mapMonoPhi4NtoN. Then, just as with the mass term matrix
		elements, dot in basis states to obtain the final n-to-n matrix elements.*)

		phi4NtoN[n,\[CapitalDelta]max];
		fullPhi4NtoNMatrix[[
			lList[[n,1]];;lList[[n,2]],
			lList[[n,1]];;lList[[n,2]]
		]]=1/4 1/(4\[Pi])*(Table[
			{b1,e1}=binCountLengthsScalar[n,\[CapitalDelta]max][[deg1+1]];
			{b2,e2}=binCountLengthsScalar[n,\[CapitalDelta]max][[deg2+1]];
			basis1=basisBoson[[1,deg1+1,n]];
			basis2=basisBoson[[1,deg2+1,n]];
			factor[deg1+n,deg2+n]*(basis1.mapMonoPhi4NtoN[[b1;;e1,b2;;e2]].Transpose[basis2]),
		{deg1,degList},{deg2,degList}]//ArrayFlatten),
	{n,2,\[CapitalDelta]max}
	]
];


(*ComputePhi4NtoNPlus2Matrix[.] follows the structure of ComputePhi4NtoNMatrix[.] and
ComputeScalarMassMatrix[.]. However, one difference is that the n-to-(n+2) 
matrices are not square and the differences between ComputePhi4NtoNPlus2Matrix[.] and
ComputePhi4NtoNMatrix[.] reflect this fact. *)

ComputePhi4NtoNPlus2Matrix[\[CapitalDelta]max_,basisBoson_]:=Block[
{degListL,degListR,basis1,basis2,b1,e1,b2,e2,mat,lengthListL,lengthListR,lList,lTotal,
timezero=AbsoluteTime[]
},
	(*Like before, lList keeps track of the dimensions of the basis
	for various particle sectors *)
	
	lList=Thread[{Prepend[Most[#]+1,1],#}]&@Accumulate[Table[
	Table[numStates[n,deg],{deg,0,\[CapitalDelta]max-n}]//Total, {n,1,\[CapitalDelta]max}] ];
	lTotal=lList[[-1,2]];
	
	(*initialize n-to-(n+2) matrix. Note that this is a square matrix,
	as it is the n-to-(n+2) contribution to the Hamiltonian. "Building
	block" matrices for each particle sector will not necessarily be
	square for the n-to-(n+2) matrix elements.*)
	
	fullPhi4NtoNPlus2Matrix=SparseArray[{},{lTotal,lTotal}];

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
		phi4NtoNPlus2[n,\[CapitalDelta]max];
		fullPhi4NtoNPlus2Matrix[[
			lList[[n-2,1]];;lList[[n-2,2]],
			lList[[n,1]];;lList[[n,2]]
		]]=1/6 1/(4\[Pi]) (Table[
			{b1,e1}=binCountLengthsScalar[n-2,\[CapitalDelta]max][[deg1+1]];
			{b2,e2}=binCountLengthsScalar[n,\[CapitalDelta]max][[deg2+1]];
			basis1=basisBoson[[1,deg1+1,n-2]];
			basis2=basisBoson[[1,deg2+1,n]];
			factor[deg1+n-2,deg2+n]*(basis1.mapMonoPhi4NtoNPlus2[[b1;;e1,b2;;e2]].Transpose[basis2]),
			{deg1,degListL},{deg2,degListR}]//ArrayFlatten),
	{n,3,\[CapitalDelta]max}
	];
	
	(*since the Hamiltonian is symmetric, to obtain the (n+2)-to-n matrix elements, we can just
	add the transpose of the n-to-(n+2) matrix.*)
	
	fullPhi4NtoNPlus2Matrix=fullPhi4NtoNPlus2Matrix+Transpose[fullPhi4NtoNPlus2Matrix];
];


(* ::Section::Closed:: *)
(*Functions for Computing Monomial  Matrix Elements*)


(* ::Subsection::Closed:: *)
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


(* ::Subsection::Closed:: *)
(*Monomial Matrices*)


(*Monomial mass term. Its output is a matrix that is the monomial mass
term matrix elements.*)

massNtoN[nR_,\[CapitalDelta]max_]:=Block[
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

			map[Sow[{i,ip}]]+=(a*ap)Sqrt[N[Min[k,kp]/Max[k,kp]]];,
		{c1,cList},
		{c2,cList}
		] ,
	{cList,cListGroup}] ][[2,1]];
	
	SparseArray[(#->map[#])&/@temp,{l,l}]
]


(*Interaction term active part from radial quantization*)
ClearAll[phi4ContractNN]
phi4ContractNN=Compile[{{k1,_Real},{k2,_Real},{k1p,_Real},{k2p,_Real}},(Min[k1,k1p]+Min[k1,k2p]-Min[k1,k1p+k2p]+Min[k1p,k2]-Min[k1p,k1+k2]+Min[k2,k2p]-Min[k2,k1p+k2p]-Min[k1+k2,k2p]+Min[k1+k2,k1p+k2p])/Sqrt[k1*k2*k1p*k2p],
CompilationTarget->"C",
CompilationOptions->{"ExpressionOptimization" -> True}
]


(*Monomial n-to-n interaction. Structurally, it is very similar to the mass term.
The only difference is that we call on the function phiAnnihilateTwoMap[.] and
of course the active part of the matrix element is different. The output is
the monomial n-to-n interaction matrix.*)

phi4NtoN[nR_,\[CapitalDelta]max_]:=Block[
{
mat,idxGroup,l,rowShort,
k,kp,a,ap,i,ip,cListGroup,contractionList,
out,temp,map,internalClock=AbsoluteTime[]
},
	(*Again set up the list of positions and values obtained from phiAnnihilateTwoMap[.] *)
	l=Length[binCountListsScalar[nR,\[CapitalDelta]max]];
	mat=phiAnnihilateTwoMap[nR,\[CapitalDelta]max];
	idxGroup=mat[[;;,;;,1]]["NonzeroPositions"];
	cListGroup=SplitBy[Join[
	idxGroup//Transpose,
	{
		Extract[mat[[;;,;;,1]],idxGroup],
		Extract[mat[[;;,;;,2]],idxGroup]
	}
	]//Transpose,First][[;;,;;,{2,3,4}]];
	
	(*Note that below we call the function phi4ContractNN[.] which
	gives us the monomial matrix element for n-to-n *)
	ClearAll[mapMonoPhi4NtoN];
	map[__]=0;
	temp=((Transpose[#].#)&@mat[[;;,;;,1]])["NonzeroPositions"];
	Do[Do[
		{i,a,k}=c1;
		{ip,ap,kp}=c2;
		map[i,ip]+=(a*ap)phi4ContractNN[Sequence@@k,Sequence@@kp];,
		{c1,cList},
		{c2,cList}
		],
	{cList,cListGroup}] ;mapMonoPhi4NtoN=SparseArray[Thread[temp->(map@@@temp)],{l,l}];
]


(*Active contribution for n-to-(n+2) interaction*)
ClearAll[phi4ContractNN2]
phi4ContractNN2=Compile[{{k1,_Real},{k1p,_Real},{k2p,_Real},{k3p,_Real}},(Min[k1,k1p]+Min[k1,k2p]-Min[k1,k1p+k2p]+Min[k1,k3p]-Min[k1,k1p+k3p]-Min[k1,k2p+k3p]+Min[k1,k1p+k2p+k3p])/Sqrt[k1*k1p*k2p*k3p],
CompilationTarget->"C",
CompilationOptions->{"ExpressionOptimization" -> True}
]


(*The final monomial routine, phi4NtoNPlus2[.] follows the same structure
as the n-to-n case but computes the matrix elements for n-to-(n+2). Note
that the major difference in practice in the code is just accounting for
different dimensions of the matrices for the dotting procedure. *)

phi4NtoNPlus2[nR_,\[CapitalDelta]max_]:=Block[
{
matL,matR,idxGroup,lL,lR,rowShort,
k,kp,a,ap,i,ip,cListGroup,contractionList,
map,temp,idxL,idxR
},
	lR=Length[binCountListsScalar[nR,\[CapitalDelta]max]];
	lL=Length[binCountListsScalar[nR-2,\[CapitalDelta]max]];
	
	(*Obtain annihilation maps*)
	matR=phiAnnihilateThreeMap[nR,\[CapitalDelta]max];
	matL=phiAnnihilateMap[nR-2,\[CapitalDelta]max];
	
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
		{row,Length[binCountListsScalar[nR-3,\[CapitalDelta]max]]}]
	][[2,1]];
	
	(* and then build the final monomial n-to-(n+2) matrix*)
	ClearAll[mapMonoPhi4NtoNPlus2];
	map[__]=0;
	temp=(Transpose[matL[[;;,;;,1]]].matR[[;;,;;,1]])["NonzeroPositions"];
	Do[
		Do[
			{i,a,k}=c1;
			{ip,ap,kp}=c2;
			map[i,ip]+=(a*ap)phi4ContractNN2[k,Sequence@@kp],
		{c1,cList[[1]]},
		{c2,cList[[2]]}
		],
	{cList,cListGroup}];
	mapMonoPhi4NtoNPlus2=SparseArray[Thread[temp->(map@@@temp)],{lL,lR}];
]


(* ::Section::Closed:: *)
(*Utility Functions*)


(*Normalization factor of states*)
factor[\[CapitalDelta]_,\[CapitalDelta]p_]:=factor[\[CapitalDelta],\[CapitalDelta]p]=Sqrt[ Gamma[2\[CapitalDelta]]Gamma[2\[CapitalDelta]p] ] * (-1)^(\[CapitalDelta]-\[CapitalDelta]p) / Gamma[\[CapitalDelta]+\[CapitalDelta]p-1];


(*Number of states at a given particle sector and degree *)
ClearAll[numStates]
numStates[n_,bDeg_]:=With[
	{\[CapitalDelta]=n+bDeg},
	Coefficient[Normal@Series[x^n Product[1/(1-x^k),{k,2,n}],{x,0,\[CapitalDelta]}],x^\[CapitalDelta]]
];


(* 
	c = cfBinCount[k vector] computes the bin counts of vector \vec{k} so that
	for each k in \vec{k} the k'th element of c, c[[k]] is the number of copies
	of k in \vec{k}. If \vec{k} does not have k, then c[[k]]=0.
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
];


ClearAll[binCountListsScalar,binCountLengthsScalar];
binCountListsScalar[n_,\[CapitalDelta]max_]:=binCountListsScalar[n,\[CapitalDelta]max]=cfBinCount[#,\[CapitalDelta]max]&/@Flatten[Reap[
binCountLengthsScalar[n,\[CapitalDelta]max]=Thread[{Most[#]+1,Rest[#]}]&@Prepend[Accumulate@Table[
Length@Sow[IntegerPartitions[\[CapitalDelta],{n}]],
{\[CapitalDelta],n,\[CapitalDelta]max,1}
],0]
 ][[2,1]],1];
