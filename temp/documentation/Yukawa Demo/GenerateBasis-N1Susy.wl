(* ::Package:: *)

(* ::Chapter:: *)
(*Output Basis Files*)


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
	The benefit of storing the pre-orthogonalized basis
	is that the basis is purely integral, so the precision
	of the basis can be arbitrary. Since symbolic 
	orthogonalization takes forever one has to get the 
	numerical value at some precision. *)
computeBosonBasis[\[CapitalDelta]max_,fdr_,prec_]:=With[
	{(*\[CapitalDelta]max=15,*)t1=AbsoluteTime[](*,prec=40*)},
	resPreTrans=Table[
		Print["t=",AbsoluteTime[]-t1];
		Print["n@ ",n];
		Table[
			joaoPolySet[n,deg],{deg,0,\[CapitalDelta]max-n}
		],
		{n,1,\[CapitalDelta]max}
	];
	Print["t=",AbsoluteTime[]-t1];
	
	basisBosonPre={Table[resPreTrans[[n,deg+1]],{deg,0,\[CapitalDelta]max},{n,1,\[CapitalDelta]max-deg}]};
	basisBoson={Table[orthogonalizeBasis[n,deg,prec][ resPreTrans[[n,deg+1]] ],{deg,0,\[CapitalDelta]max},{n,1,\[CapitalDelta]max-deg}]};
	
	SetDirectory[fdr];
	Save["./BasisBosonPreD"<>ToString[\[CapitalDelta]max],basisBosonPre];
	Save["./BasisBosonD"<>ToString[\[CapitalDelta]max],basisBoson];
	basisBoson
];


computeFermionBasis[\[CapitalDelta]Max_,fdr_,prec_]:=Block[{t1,nMin,degs,i},
	t1=AbsoluteTime[];
	(*\[CapitalDelta]Max=15;*)
	nMin=1; (*Starting particle sector*)
	degs=Reverse@Table[\[CapitalDelta]Max-i,{i,nMin,\[CapitalDelta]Max}];
	AbsoluteTiming[basisFermion=Reap[For[i=1,i<=Length@degs,i++,
	Print["@ :", i];
	Sow[genStatesDMax[nMin,\[CapitalDelta]Max-degs[[i]],degs[[i]],prec]];
	Print["Time (m):", (AbsoluteTime[]-t1)/60.];
	DownValues[\[CapitalOmega]]=DeleteCases[DownValues[\[CapitalOmega]],HoldPattern[Verbatim[HoldPattern][\[CapitalOmega][x_,y_/;ListQ[y]]] :> _]];
	]][[2]];];

	SetDirectory[fdr];
	Save["./BasisFermionD"<>ToString[\[CapitalDelta]Max],basisFermion];
	basisFermion
]


computeN1SUSYBasis[\[CapitalDelta]max_,fdr_,prec_]:=Block[
	{primaryStates,t1=AbsoluteTime[],basisBoson,basisFermion},
	Print["@ : Generating boson states"];
	basisBoson=computeBosonBasis[\[CapitalDelta]max,fdr,prec];
	Print["@ : Generating fermion states"];
	basisFermion=computeFermionBasis[\[CapitalDelta]max,fdr,prec];
	Print["@ : taking boson descendants"];
	takeBosonDescendants[\[CapitalDelta]max,basisBoson];
	Print["Time (s):", (AbsoluteTime[]-t1)];
	
	Print["@ : taking fermion descendants"];
	takeFermionDescendants[\[CapitalDelta]max,basisFermion];
	Print["Time (s):", (AbsoluteTime[]-t1)];
	
	Print["@ : gluing fermion and bosons"];
	basisN1SUSY=Join[
		Reap[Do[
			primaryStates=basisBoson[[1,deg+1,n]];
			If[primaryStates!={}, Sow[{KroneckerProduct[#,{1}]},state[n,deg,0,0,0]]&/@primaryStates],
			{deg,0,\[CapitalDelta]max},{n,1,\[CapitalDelta]max-deg}
		],state[__],<|Thread[{"nB","degB","nF","degF","l"}->List@@#1],"states"->#2|>&][[2]] ,
		
		Reap[Do[
			primaryStates=basisFermion[[1,deg+1,n]];
			If[primaryStates!={}, Sow[{KroneckerProduct[{1},#]},state[0,0,n,deg,0]]&/@primaryStates],
			{deg,0,\[CapitalDelta]max},{n,1,\[CapitalDelta]max-deg}
		],state[__],<|Thread[{"nB","degB","nF","degF","l"}->List@@#1],"states"->#2|>&][[2]] ,
		
		glueBosonsAndFermions[\[CapitalDelta]max]
	];
	basisN1SUSY=GatherBy[SortBy[basisN1SUSY,{#nB&,#nF&,#degB&,#degF&,#l&}],{#nB&,#nF&}];
	basisN1SUSY=Insert[basisN1SUSY,{},{1,1}];
	basisN1SUSY=With[{maxNFPlus1=(Length/@basisN1SUSY)//Max},
		PadRight[#,maxNFPlus1,{{}}]&/@basisN1SUSY
	];
	
	Print["Time (s):", (AbsoluteTime[]-t1)];
	
	SetDirectory[fdr];
	Save["basisN1SUSYD"<>ToString[\[CapitalDelta]max],basisN1SUSY]
];


(* ::Chapter:: *)
(*Shared functions*)


(* ::Section:: *)
(*state normalization factors*)


factorBoson[y_List]:=Sqrt[Times@@(#[[2]]!* #[[1]]^#[[2]]&/@Tally[y])]Times@@(Gamma/@y);


ClearAll[factorBosonAtLevel]
factorBosonAtLevel[n_,deg_]:=factorBosonAtLevel[n,deg]=factorBoson/@IntegerPartitions[n+deg,{n}]


factorFermion[k_List]:=(Times@@(Gamma/@k)) * Sqrt[Times@@(1/2 * k*(k+1))]


ClearAll[factorFermionAtLevel]
factorFermionAtLevel[n_,deg_]:=factorFermionAtLevel[n,deg]=factorFermion/@Select[IntegerPartitions[n+deg,{n}],DuplicateFreeQ]


(* ::Section:: *)
(*"Binomial" coefficients of Joao's alternating derivative*)


(* The coefficients in front of each term in 
	Joao's alternating derivative *)
joaoCoeff[degL_,degR_,l_,k_]:=
	joaoCoeff[degL,degR,l,k]=
		((-1)^k Gamma[2degL+l]Gamma[2degR+l]) / 
		(k!(l-k)!Gamma[2degL+k]Gamma[2degR+l-k]);


(* ::Chapter::Closed:: *)
(*Used in Pure Boson States*)


(*ClearAll["Global`*"];
HistoryLength=0;*)

(* Number of primaries expected at 
	number of particle: n
	degree: l (l=0 means \[PartialD]\[Phi]\[PartialD]\[Phi]..\[PartialD]\[Phi])
	This is not really required but just there to avoid 
	exceptions when expecting 0 states  *)
ClearAll[numStates]
numStates[n_,l_]:=With[
	{\[CapitalDelta]=n+l},
	Coefficient[Normal@Series[x^n Product[1/(1-x^k),{k,2,n}],{x,0,\[CapitalDelta]}],x^\[CapitalDelta]]
];



(* permutedMultinomial[ kp , kpp ]
	computes the same result as
		Sum[ Multinomial@@(y-kpp), {y,Permutations[kp]} ]
	but faster using recursion relation  *)
ClearAll[permutedMultinomial]
permutedMultinomial[kp_List,kpp_List]/;Length[kp]>=1:=permutedMultinomial[kp,kpp]=With[
	{
	kpi=DeleteDuplicates[kp],
	kpRest=Table[Drop[kp,{i}],{i,Length[kp]}]//DeleteDuplicates,
	s=Total[kp]-Total[kpp]
	},
	Array[
		Catch[ Binomial[s,If[#<0,Throw[0],#]&[kpi[[#]]-First[kpp]]]*
		permutedMultinomial[kpRest[[#]],Drop[kpp,1]] ]&,Length[kpi]
	]//Total
];
permutedMultinomial[kp_List,kpp_List]/;Length[kp]==0:=permutedMultinomial[kp,kpp]=1;

(* Suppose a primary operator 
	O' = c_{\kvec'} \[PartialD]^{\kvec'}\[Phi]
	is described by vector
	v' = {c_{k'_1}, c_{k'_2}, ...} .
	Then Joao's construction of attaching a \[PartialD]\[Phi] and taking
	alternating derivative to obtain a new primary O, is
	described by multiplying a matrix M(n,l,l') to v':
	v := M(n,l,l').v'  .
	The function 
		recMatTrans[n,l,lp] := M(n,l,lp)
	computes that matrix, where
		n is the particle number of the target primary O
		l is the degree of the target primary O
		lp is the degree of the (n-1) particle primary O'
	*)
ClearAll[recMatTrans]
recMatTrans[n_,l_,lp_]:=With[
	{
		ks=IntegerPartitions[l+n,{n}]-1,
		kps=IntegerPartitions[lp+n-1,{n-1}]-1,
		recPair=Function[{k,kp},With[{
			kDist=DeleteDuplicates@k//Reverse,
			kPoss=Table[Drop[k,{i}],{i,Length[k]}]//DeleteDuplicates//Reverse,
			dl=l-lp},
		Array[
			joaoCoeff[1,lp+n-1,dl,kDist[[#]]]*permutedMultinomial[kPoss[[#]],kp]&,
			FirstPosition[dl-kDist,_?NonPositive,{Length[kDist]},1]//First
		]//Total
		] ]
	},
	Outer[recPair,ks,kps,1]//Transpose
];

(* Since Joao's alternating derivative matrix
	recMatTrans[n,l,lp]
	only depends on n and degree but not the l vector,
	it makes sense to use the same matrix on the entire
	level (n,l). 
	Furthermore, the selection rule says to get the full
	set of primaries at level (n,l) one just need to 
	consider:
		(n,l) <-- (n-1,l)
		(n,l) <-- (n-1,l-n)
		(n,l) <-- (n-1,l-2n)
		...
	from only the primary states that we have already 
	found earlier. 
	The function
		joaoPolySet[n,deg]
	is defined recursively as collecting new states at 
	level (n,deg=l) in the above way. *)
ClearAll[joaoPolySet]
joaoPolySet[n_,deg_]:=joaoPolySet[n,deg]=Flatten[Reap[Do[
	If[numStates[n-1,degP]!=0,
		Sow[ joaoPolySet[n-1,degP].recMatTrans[n,deg,degP]  ]
	],{degP,deg,0,-n}
] ][[2]],2];
joaoPolySet[1,Except[0]]={};
joaoPolySet[1,0]={{1}};


(* The code computes the orthonormal primary basis from the set of linear 
independent primary operator obtained from joaoPolySet[].
First multiply each monomial by its normalization factor given by factor[].
Then, take the numerical value at precision prec_ and orthogonalize it at to 
obtain the orthonormal primary basis that can later be used in matrix elements
computation. *)
(*factorBoson[y_List]:=Sqrt[Times@@(#[[2]]! #[[1]]^#[[2]]&/@Tally[y])]Times@@(Gamma/@y);*)
orthogonalizeBasis[n_,deg_,prec_][vectors_]:=With[
	{factors = factorBoson/@IntegerPartitions[n+deg,{n}]},
	N[factors*#&/@vectors,prec]//Orthogonalize
]


(* ::Chapter:: *)
(*Used in Pure Fermions States*)


HnCoeff[n_,x_,\[Alpha]_,\[Beta]_,M_]:=(-1)^n Sqrt[(Gamma[\[Alpha]+1+x]/Gamma[\[Alpha]+1] Gamma[\[Beta]+1+M-x]/Gamma[\[Beta]+1])/(Gamma[\[Alpha]+\[Beta]+2+M]/Gamma[\[Alpha]+\[Beta]+2]) (2n+\[Alpha]+\[Beta]+1)/(\[Alpha]+\[Beta]+1) (Gamma[\[Alpha]+\[Beta]+1+n]/Gamma[\[Alpha]+\[Beta]+1] Gamma[\[Alpha]+1+n]/Gamma[\[Alpha]+1])/(Gamma[\[Beta]+1+n]/Gamma[\[Beta]+1] Gamma[\[Alpha]+\[Beta]+2+M+n]/Gamma[\[Alpha]+\[Beta]+2+M])];

Hn[n_,x_,\[Alpha]_,\[Beta]_,M_]:=Hn[n,x,\[Alpha],\[Beta],M]=Which[n<0,0,x<0,0,n>=0||x>=0,HnCoeff[n,x,\[Alpha],\[Beta],M]Sqrt[Binomial[M,x]Binomial[M,n]] HypergeometricPFQ[{-n,n+\[Alpha]+\[Beta]+1,-x},{\[Alpha]+1,-M},1]];

mag[larg_List,lim_]:=mag[larg,lim]=Plus@@(larg[[1;;lim]]);


ClearAll[\[CapitalOmega]]
\[CapitalOmega][\[ScriptL]_List,\[Lambda]_List/;Length@\[Lambda]>=2]:=\[CapitalOmega][\[ScriptL],\[Lambda]]=With[{n=Length@\[Lambda],\[Beta]=2},
	(-1)^(\[ScriptL][[n]]+\[ScriptL][[n-1]])*
	(
		(\[ScriptL][[-2]]!Gamma[\[ScriptL][[-2]]+2*mag[\[ScriptL],n-2]+\[Beta]*(n-1)+n-2+1]) /
		(\[ScriptL][[-1]]!Gamma[\[ScriptL][[-1]]+2*mag[\[ScriptL],n-1]+\[Beta]*n+n]) 
	)^(-1/2)*
	Sum[
		(-1)^( n-i )* (* The sign comes from fermion permutation *)
		(-1)^\[Lambda][[i]]*
		(\[Lambda][[i]]!Gamma[\[Lambda][[i]]+\[Beta]+1])^(-1/2)*
		\[CapitalOmega][Drop[\[ScriptL],-1],Drop[\[Lambda],{i}]]*
		Hn[ 
			\[ScriptL][[-2]], 
			Total[Drop[\[Lambda],{i}]]-mag[\[ScriptL],n-2],
			(*2mag[\[ScriptL],n-2]+2n-3*)
			2*mag[\[ScriptL],n-2]+\[Beta]*(n-1)+n-2,
			\[Beta],
			Total[\[Lambda]]-Total[Drop[\[ScriptL],-2]]
		],
	{i,1,Length[\[Lambda]]}]
];

\[CapitalOmega][\[ScriptL]_List,\[Lambda]_List/;Length@\[Lambda]<=1]:=\[CapitalOmega][\[ScriptL],\[Lambda]]=With[
	{k=First[\[Lambda]],l=First[\[ScriptL]],\[Beta]=2},
	(-1)^k * Sqrt[
	(l!Gamma[l+\[Beta]+1]) / (k!Gamma[k+\[Beta]+1])
	]
];


(*factorFermion[k_List]:=(Times@@(Gamma/@k)) * Sqrt[Times@@(1/2 * k*(k+1))]
*)
(* This is the number of bosonic state at number of boson n and boson degree 
bDeg. The number of states has a one to one correspondence with that of 
fermions at same particle number and fermion degree (the actual jacobi polynomial
degree) fDeg by
	bDeg = fDeg + n - n (n+1)/2
  *)
ClearAll[numStates]
numStates[n_,bDeg_]:=With[
	{\[CapitalDelta]=n+bDeg},
	Coefficient[Normal@Series[x^n Product[1/(1-x^k),{k,2,n}],{x,0,\[CapitalDelta]}],x^\[CapitalDelta]]
];
(*
	The minimal l set at number of fermion n_ and the "boson degree" bDeg_
	which the fermion level maps to. 
	The l vector is defined to be of length (n-1).
	The set is obtained by refering to all levels with one less fermions and
	bDeg less by (j*n) for any possible integer j and appending to
	l vector by the actual Jacobi polynomial degree difference.
*)
ClearAll[minimalLSet]
minimalLSet[n_,bDeg_]:=minimalLSet[n,bDeg]=Flatten[Reap[Do[
	If[numStates[n-1,bDegP]!=0,
		Sow[Append[#,bDeg-bDegP+n-1] &/@minimalLSet[n-1,bDegP] ]
	],{bDegP,bDeg,0,-n}
] ][[2]],2];
minimalLSet[1,Except[0]]={};
minimalLSet[1,0]={{}};
minimalLSet[_,_?Negative]={};


(*genStatesDMax::usage=
"genStatesDMax[nMin,nMax,deg,prec] generates the basis 
starting at nMin number of particles up to nMax 
at fixed *degree* deg. Note: by degree we mean the 
degree of the Jacobi (not including the prefactor 
of the product of the momenta).";*)

genStatesDMax[nMin_,nMax_,deg_,prec_]:=Module[
	{\[ScriptL]Ini,n,i,partitions,multFactor,omegas,temp,ortho,res},
	n=nMin;
	(* Just use the minimal l set *)
	\[ScriptL]Ini=Append[#,0]&/@minimalLSet[n,deg+n-n (n+1)/2];
	i=1;
	res=ConstantArray[{},nMax-nMin+1];
	
	While[n<=nMax,
		partitions=Select[PadRight[#,n]&/@IntegerPartitions[deg,n],DuplicateFreeQ];
		Clear[temp];
		temp=ConstantArray[{},Length@\[ScriptL]Ini];
		
		multFactor=factorFermion/@(partitions+1);
		res[[n-nMin+1]]=SetPrecision[Orthogonalize[Table[
			multFactor*(N[\[CapitalOmega][\[ScriptL]Ini[[i]],#],prec]&/@partitions),
			{i,1,Length[\[ScriptL]Ini]}
		] ],prec];
		
		n++;
		i=1;
		
		(* Just use the minimal l set *)
		\[ScriptL]Ini=Append[#,0]&/@minimalLSet[n,deg+n-n (n+1)/2];
	];
	Return[res];
];


(* ::Chapter:: *)
(*Used in Mixon States*)


(* ::Section:: *)
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


(* ::Section:: *)
(*monomial vectors*)


ClearAll[monomialsBoson]
monomialsBoson[n_,deg_]:=monomialsBoson[n,deg]=IntegerPartitions[deg+n,{n}];
ClearAll[monomialsFermion]
monomialsFermion[n_,deg_]:=monomialsFermion[n,deg]=(#+Reverse[Range[n]-1])&/@monomialsBoson[n,deg+n-n (n+1)/2]


(* ::Section:: *)
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
					Range[deg,\[CapitalDelta]max-n-1,1]
			],
				factorBosonAtLevel[n,#]&/@Prepend[Range[deg+1,\[CapitalDelta]max-n-1+1,1],deg]
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
					Range[deg,\[CapitalDelta]max-n-1,1]
				],
				factorFermionAtLevel[n,#]&/@Prepend[Range[deg+1,\[CapitalDelta]max-n-1+1,1],deg]
			}
		] ],
		{deg,0,\[CapitalDelta]max},{n,1,\[CapitalDelta]max-deg}
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
		(*lMax=Floor[\[CapitalDelta]max-\[CapitalDelta]B-\[CapitalDelta]F];*)
		lMax=Floor[\[CapitalDelta]max-(degB+nB)-(degF+nF)];
		
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
		{nF,1,\[CapitalDelta]max-degB-nB-degF}
	],state[__],<|Thread[{"nB","degB","nF","degF","l"}->List@@#1],"states"->#2|>&][[2]] 
];
