(* ::Package:: *)

(* ::Chapter:: *)
(*Compute*)


(* Get A table 
	basisBosonPre[[n,deg+1]]--> primary operators at (n,deg)
	pre-normed and pre-orthogonalized in exact integers,
	and another table
	basisBoson[[n,deg+1]]--> primary operators at (n,deg) 
	after nomalization and orthogonalization in numerical 
	values with precision 'prec'.
	
	To get orthogonal states from basisBosonPre, one needs 
	to multiply the monomial normalization and 
	orthogonalize it using orthogonalizeBasis[]. 
	The benefit of storing the un-orthogonalized basis
	is that the basis is purely integral, so the precision
	of the basis can be arbitrary. Since symbolic 
	orthogonalization takes forever one has to get the 
	numerical value at some precision. *)
computeBosonBasis[\[CapitalDelta]max_,prec_]:=With[
	{t1=AbsoluteTime[]},
	allJPolySets=Table[
		Print["t=",AbsoluteTime[]-t1];
		Print["n@ ",n];
		Table[
			JPolySet[n,deg],{deg,0,\[CapitalDelta]max-n}
		],
		{n,1,\[CapitalDelta]max}
	];
	Print["t=",AbsoluteTime[]-t1];
	
	basisBosonPre={Table[allJPolySets[[n,deg+1]],{deg,0,\[CapitalDelta]max},{n,1,\[CapitalDelta]max-deg}]};
	basisBoson={Table[orthogonalizeBasis[n,deg,prec][ allJPolySets[[n,deg+1]] ],{deg,0,\[CapitalDelta]max},{n,1,\[CapitalDelta]max-deg}]};
];


(* ::Subsection:: *)
(*Orthogonalize and normalize the basis*)


(* The code computes the orthonormal primary basis from the set of linear 
independent primary operator obtained from JPolySet[].
First multiply each monomial by its normalization factor given by factor[].
Then, take the numerical value at precision prec_ and orthogonalize it at to 
obtain the orthonormal primary basis that can later be used in matrix elements
computation. *)
orthogonalizeBasis[n_,deg_,prec_][vectors_]:=With[
	{factors = factorBoson/@IntegerPartitions[n+deg,{n}]//N[#,prec]&},
	N[factors*#&/@vectors,prec]//Orthogonalize
]


(* The normalization of the primary states *)
factorBoson[k_List]:=Sqrt[Times@@(#[[2]]!* #[[1]]^#[[2]]&/@Tally[k])]Times@@(Gamma/@k);


(* ::Subsection:: *)
(*Number of independent primary states at each level*)


(* 
numStates[n,deg] counts the number of independent primary states at each level.
A level is specified by 
	the number of particle: n
	and the degree: deg .
The number of states equals the number of partitions of deg objects into exactly n bins
*)
ClearAll[numStates]
numStates[n_,deg_]:=With[
	{\[CapitalDelta]=n+deg},
	Coefficient[Normal@Series[x^n Product[1/(1-x^k),{k,2,n}],{x,0,\[CapitalDelta]}],x^\[CapitalDelta]]
];


(* ::Section:: *)
(*Compute primary states recursively*)


(*
JPolySet[n,deg] computes the primary states at level (n,deg) recursively from 
lower levels using the \[OpenCurlyDoubleQuote]Double-trace\[CloseCurlyDoubleQuote] construction.
The output of JPolySet[n,deg] is a 2-dimensional array:
	each row represents a primary state
	each column represents a monomial
	each element represents the coefficient of the monomial in the primary state.
The main recursion iterates the lower level: (n-1,degP)
	the lower level has 1 less particle
	the degP is the degree of the lower level, which equals deg-n*integer for all
		possible integer
At each iteration, the code computes primary states, schematically,
	new state = sum_k^dl( PrimCoeff * \[PartialD]^k (low level state) \[PartialD]^(dl-k) (\[PartialD]\[Phi]) )
for all low level states, where the operation
	\[PartialD]^k (low level state) 
is computed as
	(low level state).dBoson[n-1,k+degP]
and the operation of attaching a \[PartialD]^(l-k) (\[PartialD]\[Phi]) is done by
	( \[PartialD]^k (low level state) ).appendOneScalarMap[n-1,k+degP,dl-k+1]
*)
ClearAll[JPolySet]
JPolySet[n_,deg_]:=JPolySet[n,deg]=Block[
{dl},Flatten[Reap[Do[
	(* iterate the lower level degP: start from deg and step by (-n) *)
	If[numStates[n-1,degP]!=0,(* if the lower level set is empty, skip the iteration*)
		dl=deg-degP; (*The difference between the degrees of the two levels *)
		Sow[ Total@FoldPairList[
			(* new state = sum_k^dl( PrimCoeff * \[PartialD]^k (low level state) \[PartialD]^(dl-k) (\[PartialD]\[Phi]) ) *)
			{
				PrimCoeffs[degP+(n-1),1,dl,#2]
				*#1.appendOneScalarMap[n-1,#2+degP,dl-#2+1],
				#1.dBoson[n-1,#2+degP]
			}&,
			JPolySet[n-1,degP],
			Range[0,dl]]
		]
	],{degP,deg,0,-n}
] ][[2]],2] ];
(* The only one particle primary state is \[PartialD]\[Phi] *)
JPolySet[1,Except[0]]={};
JPolySet[1,0]={{1}};


(* ::Subsection:: *)
(*Taking derivative of the lower dimensional primary states*)


(*
dBoson[n,deg] computes the action of taking the derivative of a 
polynomial state at level (n,deg) as a linear map between the space 
of monimials at level (n,deg) to the space of monimials at level 
(n,deg+1).
The output of dBoson[n,deg] is a matrix. For a state of or a list of 
states, V, 
V.dBoson[n,deg]
is the (list of) derivative state(s) in the target monomial space.
*)
ClearAll[dBoson]
dBoson[n_,deg_]:=dBoson[n,deg]=Block[
	{aUp,aLow,map,mat,ap},
	(* Map the monomials to the occupation number representation *)
	aLow=cfBinCount[#,deg+2]&/@monomialsBoson[n,deg];
	aUp=cfBinCount[#,deg+2]&/@monomialsBoson[n,deg+1];
	(* Map each monomial to its index of the vector in the target 
	monomial space, and save it as the map function *)
	MapThread[(map[#1]=#2)&,{aUp,Range[Length[aUp]]}];
	(* mat is the output matrix *)
	mat=SparseArray[{},{aLow//Length,aUp//Length}];
	(* 
	For each monomial a in aLow, 
		for each non-zero occupation number a[[#]], hit it with a derivative,
		and the resulting monomial is ap, which:
			ap[[#]] = a[[#]]-1
			a[[#+1]] = a[[#+1]]+1
	then add up all results ap. Store the transition coefficients in mat.
	*)
	Do[With[{a=aLow[[i]]},
		(mat[[i,map[
			ap=a;ap[[#]]-=1;ap[[#+1]]++;ap
		  ]  ]]+=a[[#]]) &/@
			Flatten[Position[a,_?Positive,1]]
	],{i,Length[aLow]}];
	mat
]


(* ::Subsection:: *)
(*Append a (\[PartialD]^k \[Phi]) to a state*)


(* 
appendOneScalarMap[n,deg,dk] computes the action of multiplying 
a \[PartialD]^(dk)\[Phi] to a polynomial state at level (n,deg) as a linear map 
between the space of monimials at level (n,deg) to the space of 
monimials at level (n+1,deg+dk-1).
The output of appendOneScalarMap[n,deg,dk] is a matrix. For a state 
of or a list of states, V, 
V.appendOneScalarMap[n,deg,dk]
is the (list of) derivative state(s) in the target monomial space.
*)
appendOneScalarMap[n_,deg_,dk_]:=Block[
	{
		kLow,kUp,
		aLow,
		map,mat,kp,s
	},
	(* The monomials of the original level an result level *)
	kLow=monomialsBoson[n,deg];
	kUp=monomialsBoson[n+1,deg+dk-1];
	(* Map each monomial to its index of the vector in the target 
	monomial space, and save it as the map function *)
	MapThread[(map[#1]=#2)&,{kUp,Range[Length[kUp]]}];
	(* mat is the output matrix *)
	mat=SparseArray[{},{kLow//Length,kUp//Length}];
	(* 
	For each monomial a in kLow, 
		for each non-zero occupation number k[[#]], hit it with \[PartialD]^(dk)\[Phi],
		and the resulting monomial is 
			-Sort[-Append[k,dk]]
	whose element in mat should add 1. Store the transition coefficients in mat.
	*)
	Do[With[{k=kLow[[i]]},
		mat[[i,map[-Sort[-Append[k,dk]] ]  ]]+=1
	],{i,Length[kLow]}];
	mat
]


(* ::Subsection:: *)
(*Coefficients in the "double-trace" construction*)


(* The coefficients in front of each term in 
	Joao's alternating derivative *)
PrimCoeffs[degL_,degR_,l_,k_]:=
	PrimCoeffs[degL,degR,l,k]=
		((-1)^k Gamma[2degL+l]Gamma[2degR+l]) / 
		(k!(l-k)!Gamma[2degL+k]Gamma[2degR+l-k]);


(* ::Subsection:: *)
(*Making a list of monomials at each level*)


(* The list monomials at each level. The order of monomials defines
the index of each monomial in the target vector space. *)
ClearAll[monomialsBoson]
monomialsBoson[n_,deg_]:=monomialsBoson[n,deg]=IntegerPartitions[deg+n,{n}];


(* ::Subsection:: *)
(*Bin Counting: translating monomial's k vector representation to occupation number representation*)


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
