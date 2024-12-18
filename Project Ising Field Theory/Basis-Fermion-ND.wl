(* ::Package:: *)

(* ::Chapter:: *)
(*Compute*)


(* The function computeFermionBasis[\[CapitalDelta]max_,prec_] computes the fermion basis.  

Input: 
\[CapitalDelta]max = max scaling dimension,  
prec = precision to use during orthogonalization
(optional)
SUSY \[Rule] True: truncate the scalar and fermion at the same degree. Effectively take
the dimension of \[PartialD]\[Psi] to be 1 when counting the dimension for truncation.
(Default False)

Output:    
Two tables, 'basisFermionPre' and 'basisFermion', organized as follows,
basisFermionPre[[1,deg+1,n]]--> primary operators at (n,deg)
	pre-monomial-normalization and pre-orthogonalization in exact integers.
basisFermion[[1,deg+1,n]]--> primary operators at (n,deg) after normalization
	and orthogonalization in numerical values with precision 'prec'. 
	
Note: 
To get orthogonal states from basisFermionPre, one needs to multiply the monomial 
normalization and orthogonalize it using orthogonalizeBasisFermion[]. The benefit of storing 
the un-orthogonalized basis is that the basis is purely integral, so the precision of 
the basis can be arbitrary. Since symbolic orthogonalization takes forever one has to 
get the numerical value at some precision.	*)

computeFermionBasis[\[CapitalDelta]max_,prec_,OptionsPattern[]]:=With[
	{t1=AbsoluteTime[]},
	\[CapitalDelta]f=1/2;
	allPrimarySetsFermion=Table[
		Print["t=",AbsoluteTime[]-t1];
		Print["n@ ",n];
		Table[
			PrimarySetFermion[n,bDeg[n,deg]],{deg,0,Floor[\[CapitalDelta]max-\[CapitalDelta]f*n]}
		],
		{n,1,Floor[\[CapitalDelta]max/\[CapitalDelta]f]}
	];
	Print["t=",AbsoluteTime[]-t1];
	
	basisFermionPre={Table[allPrimarySetsFermion[[n,deg+1]],{deg,0,\[CapitalDelta]max},{n,1,Floor[(\[CapitalDelta]max-deg)/\[CapitalDelta]f]}]};
	basisFermion={Table[orthogonalizeBasisFermion[n,deg,prec][ allPrimarySetsFermion[[n,deg+1]] ],{deg,0,\[CapitalDelta]max},{n,1,Floor[(\[CapitalDelta]max-deg)/\[CapitalDelta]f]}]};
];
Options[computeFermionBasis]={SUSY->False}
bDeg[n_,deg_]:=deg-lF[n];
lF[n_]:=n (n-1)/2;


(* ::Subsection:: *)
(*Orthogonalize and normalize the basis*)


(* This function computes the orthonormal primary basis from the set of linearly 
independent primary operators obtained from PrimarySetFermion[].
First multiply each monomial by its normalization factor given by factorFermion[].
Then, take the numerical value at precision 'prec' and orthogonalize it to 
obtain the orthonormal primary basis that can later be used in matrix element
computations. *)
orthogonalizeBasisFermion[n_,deg_,prec_][vectors_]:=With[
	{factors = factorFermion/@monomialsFermion[n,deg]},
	N[factors*#&/@vectors,prec]//Orthogonalize
]


(* The monomial normalization *)
factorFermion[k_List]:=(Times@@(Gamma/@(k+1))) (* * Sqrt[Times@@(1/2 * k*(k+1))]*)


(* ::Subsection:: *)
(*Number of independent primary states at each level*)


(* 
numStates[n,bDeg] counts the number of independent primary states at each level.
A level is specified by 
	the number of particle: n
	and bDeg := degree+n-n(n+1)/2
The number of states equals the number of partitions of bDeg objects into exactly n bins. 
The origin of bDeg and its relation to counting scalar primaries is explained in 
section 5.2 of the paper. 
*)
ClearAll[numStates]
numStates[n_,bDeg_]:=With[
	{\[CapitalDelta]=n+bDeg},
	Coefficient[Normal@Series[x^n Product[1/(1-x^k),{k,2,n}],{x,0,\[CapitalDelta]}],x^\[CapitalDelta]]
];


(* ::Text:: *)
(*bDeg := deg+n-n (n+1)/2*)


(* ::Section:: *)
(*Compute primary states recursively*)


(*
PrimarySetFermion[n,bDeg] computes the primary states at level (n,deg=bDeg-n+(n(n+1))/2) 
proceeding recursively from lower levels using the \[OpenCurlyDoubleQuote]Double-trace\[CloseCurlyDoubleQuote] construction.
The output of PrimarySetFermion[n,bDeg] is a 2-dimensional array:
	each row represents a primary state
	each column represents a monomial
	each element represents the coefficient of the monomial in the primary state.
The main recursion iterates the lower level: (n-1,degP)
	the lower level has 1 less particle
	the degP is the degree of the lower level, which equals deg-n*integer for all
		possible integer
At each iteration, the code computes primary states, schematically,
	new state = sum_k^dl( PrimCoeff * \[PartialD]^k (low level state) \[PartialD]^(dl-k) (\[PartialD]\[Psi]) )
for all low level states, where the operation
	\[PartialD]^k (low level state) 
is computed as
	(low level state).dFermion[n-1,k+degP]
and the operation of attaching a \[PartialD]^(l-k) (\[PartialD]\[Psi]) is done by
	( \[PartialD]^k (low level state) ).appendOneFermionMap[n-1,k+degP,dl-k+1]
*)
ClearAll[PrimarySetFermion]
PrimarySetFermion[n_,bDeg_]:=PrimarySetFermion[n,bDeg]=Module[
{
	deg=bDeg+n (n-1)/2,
	degP,dl},
Flatten[Reap[Do[
	If[numStates[n-1,bDegP]!=0,
		degP=(bDegP+lF[n-1]);
		(*Print[bDegP];
		Print[degP];*)
		dl=bDeg-bDegP+n-1;
		Sow[ Total@FoldPairList[
			{
				(*Print[{n,#2+degP}];*)
				PrimCoeffs[degP+1/2(n-1),1/2,dl,#2]
				*#1 . appendOneFermionMap[n-1,#2+degP,dl-#2],
				#1 . dFermion[n-1,#2+degP]
			}&,
			PrimarySetFermion[n-1,bDegP],
			Range[0,dl]]
		]
	],{bDegP,bDeg,0,-n}
] ][[2]],2] ];
PrimarySetFermion[1,Except[0]]={};
PrimarySetFermion[1,0]={{1}};
PrimarySetFermion[_,_?Negative]={};


(* ::Subsection:: *)
(*Taking derivative of the lower dimensional primary states*)


(*
dFermion[n,deg] computes the action of taking the derivative of a 
polynomial state at level (n,deg) as a linear map between the space 
of monimials at level (n,deg) to the space of monimials at level 
(n,deg+1).
The output of dFermion[n,deg] is a matrix. For a state of or a list of 
states, V, 
V.dFermion[n,deg]
is the (list of) derivative state(s) in the target monomial space.

Note:
dFermion[n,deg] is a map from monomialsFermion[n,deg] --\[Rule] monomialsFermion[n,deg+1].
Meanwhile, in the scalar basis code we defined
dBoson[n,deg] which is a map from monomialsBoson[n,deg] --\[Rule] monomialsBoson[n,deg+1].
There is a one-to-one correspondence between monomialsFermion[n,deg] and monomialsBoson[n,bDeg],
where bDeg = deg+n-n(n+1)/2 (see section 5.2 of the paper).
Thought of as matrices, dFermion[n,deg] is nearly identical to dBoson[n,bDeg], 
except that nonzero integer entries in dBoson[n,bDeg] are just 1 in dFermion[n,deg] due to 
Fermi statistics. 
*)
ClearAll[dFermion]
dFermion[n_,deg_]:=(*dFermion[n,deg]=*)Block[
	{bDeg=deg-lF[n],
		aLow,aUp,
		map,mat,ap
	},
	(* Map the monomials to the occupation number representation *)
	aLow=cfBinCount[#,bDeg+2]&/@monomialsBoson[n,bDeg];
	aUp=cfBinCount[#,bDeg+2]&/@monomialsBoson[n,bDeg+1];
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
		  ]  ]]+=1) &/@
			Flatten[Position[a,_?Positive,1]]
	],{i,Length[aLow]}];
	mat
]


(* ::Subsection:: *)
(*Append a (\[PartialD]^k \[Psi]) to a state*)


(* 
appendOneFermionMap[n,deg,dk] computes the action of multiplying 
a \[PartialD]^(dk)\[Psi] to a polynomial state at level (n,deg) as a linear map 
between the space of monimials at level (n,deg) to the space of 
monimials at level (n+1,deg+dk-1).
The output of appendOneFermionMap[n,deg,dk] is a matrix. For a state 
of or a list of states, V, 
V.appendOneFermionMap[n,deg,dk]
is the (list of) derivative state(s) in the target monomial space.
*)
appendOneFermionMap[n_,deg_,dk_]:=Block[
	{
		kLow,kUp,
		aLow,
		map,mat,kp,s
	},
	(* The monomials of the original level and result level *)
	kLow=monomialsFermion[n,deg];
	kUp=monomialsFermion[n+1,deg+dk];
	(* Map each monomial to its index of the vector in the target 
	monomial space, and save it as the map function *)
	MapThread[(map[#1]=#2)&,{kUp,Range[Length[kUp]]}];
	(* mat is the output matrix *)
	mat=SparseArray[{},{kLow//Length,kUp//Length}];
	(* 
	For each monomial a in kLow, 
		for each non-zero occupation number k[[#]], hit it with \[PartialD]^(dk)\[Psi],
		and the resulting monomial is 
			-Sort[-Append[k,dk]]
	whose element in mat should add s.
	s = {0,+1,-1} depending on the permutation sign needed to Sort the resulting 
	    monomial. 
	Store the transition coefficients in mat.
	*)
	Do[With[{k=kLow[[i]]},
		kp=Append[k,dk];
		s=Signature[-kp];
		(*Print[{kp,s}];*)
		If[s!=0,mat[[i,map[-Sort[-kp] ]  ]]+=s]
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
ClearAll[monomialsFermion]
monomialsFermion[n_,deg_]:=monomialsFermion[n,deg]=(#+Reverse[Range[n]-1]-1)&/@monomialsBoson[n,deg-n (n-1)/2]


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
