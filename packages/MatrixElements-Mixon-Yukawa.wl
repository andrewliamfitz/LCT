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


BeginPackage["yukawaCode`",{"utilities`"}]


computeYukawaMatrices::usage=
"computeYukawaMatrices[suffix_,basisMixon_,fdr_]
computes the matrix elements of Yukawa cubic term \[Phi]\[Psi](1/\[PartialD])\[Psi]
and the quartic term \[Phi]\[Psi](1/\[PartialD])\[Phi]\[Psi] with respect to the basis
given as argument basisMixon_ and store them in folder fdr_
The first argument suffix is only used to decide the output 
file name and does not affect the calculation."


matYukawaCubic::usage


matYukawaQuartic::usage


Begin["`Private`"]


(* ::Section::Closed:: *)
(*External functions*)


(* computeYukawaMatrices is the main wrapper function, which runs through the
elements of the basis and calls primBlock to make the matrix elements 
between primaries.  *)


computeYukawaMatrices[suffix_,basisMixon_,fdr_]:=With[{t1=AbsoluteTime[]},
	Print["@ Quartic:"];
	(* First construct matrix elements for the quartic Yukawa term *)	
	matYukawaQuartic=With[{
	(* Read the number nBMax of boson and nFMax of fermion primaries in the mixon basis *)
		nBMax=Dimensions[basisMixon][[1]]-1,
		nFMax=Dimensions[basisMixon][[2]]-1},
		Table[
		(* The Yukawa quartic interaction can only change the boson number
		and the fermion number by +/-2 or 0.  By Hermiticity, we can assume no
		fermions are produced by the interaction (Hermiticity relates their production
		to their absorption), and moreover that if the number of in fermions and
		the number of out fermions are the same then that no bosons are produced.  *)
			If[(nBL==nBR&&nFL==nFR)||
				(nBL+2==nBR&&nFL==nFR)||
				(nBL==nBR+2&&nFL+2==nFR)||
				(nBL==nBR&&nFL+2==nFR),
				Catch[ArrayFlatten[Outer[
				(* Apply primBlock to each block of matrix elements with a given
				in and out fermion and boson number, nBL, nBR, nFL, & nFR. 
				If there are no primaries in the block, return the empty set.
				The arguments of primBlock are Operator, \[Delta]nB, \[Delta]nF,
				where Operator is the interaction and \[Delta]nB, \[Delta]nF are the changes in boson
				and fermion number for the in vs out states.
				Note that the Operator argument (in this case, yukawaQuartic)
				is itself a function *)
					primBlock[yukawaQuartic,nBR-nBL,nFR-nFL],
					If[Length[#]==0,Throw[{}],#]&@basisMixon[[nBL+1,nFL+1]],
					If[Length[#]==0,Throw[{}],#]&@basisMixon[[nBR+1,nFR+1]],1
				] ] ],
				(*  If the boson & fermion numbers don't change by +/-2 or 0,
				 set the matrix elements for the block to zero*)
				SparseArray[{},{stateCount[basisMixon[[nBL+1,nFL+1]]],
					stateCount[basisMixon[[nBR+1,nFR+1]]] }] 
			],
			{nBL,0,nBMax},
			{nBR,0,nBMax},
			{nFL,0,nFMax},
			{nFR,0,nFMax}
		]
	];
	(* Clean up the matrix, and fill in the remaining entries by using Hermiticity *)
	matYukawaQuartic=Replace[matYukawaQuartic,{{}..}->{},{4}];
	Block[{
	(* Read the number nBMax of boson and nFMax of fermion primaries in the mixon basis *)
		nBMax=Dimensions[basisMixon][[1]]-1,
		nFMax=Dimensions[basisMixon][[2]]-1,
		block},
		Do[
			If[(nBL==nBR+2&&nFL==nFR)||
				(nBL+2==nBR&&nFL==nFR+2)||
				(nBL==nBR&&nFL==nFR+2),
				block=matYukawaQuartic[[nBR+1,nBL+1,nFR+1,nFL+1]];
				matYukawaQuartic[[nBL+1,nBR+1,nFL+1,nFR+1]]=If[block!={},
					Transpose[block],{}]
			],
			{nBL,0,nBMax},
			{nBR,0,nBMax},
			{nFL,0,nFMax},
			{nFR,0,nFMax}
		]
	];
	
	Print["t = ",AbsoluteTime[]-t1];
	
	Print["@ Cubic:"];
	(* Then construct matrix elements for the cubic Yukawa term *)
	matYukawaCubic=With[{
		nBMax=Dimensions[basisMixon][[1]]-1,
		nFMax=Dimensions[basisMixon][[2]]-1},
		Table[
		(* The Yukawa cubic interaction can only change the boson number by +/-1
		and the fermion number by +/-2 or 0.  By Hermiticity, we can assume that
		the boson number changes by +1. *)
			If[nBL==nBR+1&&MatchQ[nFL-nFR,-2|0|2],
				Catch[ArrayFlatten[Outer[
				(* Apply primBlock to each block of matrix elements with a given
				in and out fermion and boson number, nBL, nBR, nFL, & nFR. 
				If there are no primaries in the block, return the empty set.
				The arguments of primBlock are Operator, \[Delta]nB, \[Delta]nF,
				where Operator is the interaction and \[Delta]nB, \[Delta]nF are the changes in boson
				and fermion number for the in vs out states.
				Note that the Operator argument (in this case, yukawaCubic)
				is itself a function *)
					primBlock[yukawaCubic,-1,nFR-nFL],
					If[Length[#]==0,Throw[{}],#]&@
						basisMixon[[nBL+1,nFL+1]],
					If[Length[#]==0,Throw[{}],#]&@
						basisMixon[[nBR+1,nFR+1]],
				1 ] ] ], 
				(*  If the boson & fermion numbers don't change by +1 & +/-2 or 0,
				respectively, set the matrix elements for the block to zero*)
				SparseArray[{},{stateCount[basisMixon[[nBL+1,nFL+1]]],
					stateCount[basisMixon[[nBR+1,nFR+1]]] }] 
			],
			{nBL,0,nBMax},
			{nBR,0,nBMax},
			{nFL,0,nFMax},
			{nFR,0,nFMax}
		]
	];
	(* Clean up the matrix, and fill in the remaining entries by using Hermiticity *)
	matYukawaCubic=Replace[matYukawaCubic,{{}..}->{},{4}];
	Block[{
		nBMax=Dimensions[basisMixon][[1]]-1,
		nFMax=Dimensions[basisMixon][[2]]-1,
		nBR,nFR,block
		},
		Do[
			nBR=nBL+1;
			block=matYukawaCubic[[nBR+1,nBL+1,nFR+1,nFL+1]];
			matYukawaCubic[[nBL+1,nBR+1,nFL+1,nFR+1]]=If[block!={},
				Transpose[block],{}],
			{nBL,0,nBMax-1},
			{nFL,0,nFMax},{nFR,Select[{nFL-2,nFL,nFL+2},0<=#<=nFMax&]}
		]
	];
	
	Print["t = ",AbsoluteTime[]-t1];
	(* Save the resulting matrix elements to file, with the filenames set by suffix_ and the directory set by fdr_ *)
	SetDirectory[fdr];
	Save["MatrixYukawaCubicD"<>ToString[suffix],matYukawaCubic];
	Save["MatrixYukawaQuarticD"<>ToString[suffix],matYukawaQuartic];
]


(* Function for counting the number of basis states with a given number of bosons and fermions *)
stateCount[lstOfLevels_]:=Total[Length[#states]&/@lstOfLevels]


(* ::Section:: *)
(*Matrix contracting an array of primaries*)


(* For a given operator (here, yukawaQuartic or yukawawCubic) and change in boson and fermion number,
primBlock makes a function that makes the matrix elements.  This function acts on the in and out basis elements.
For instance, say computeYukawaMatices feeds primBlock 
primBlock[yukawaCubic,-1,0][basisMixon[[nBL+1,nFL+1]][[1]],basisMixon[[nBR+1,nFR+1]]][[1]]
with nBL=0, nBR=1, nFL=nFR=1.
Then the in state is one fermion and the out state is one fermion and one boson. 
In this case,
level1=basisMixon[[nBL+1,nFL+1]][[1]]=\[LeftAssociation]"nB"\[Rule]0,"degB"\[Rule]0,"nF"\[Rule]1,"degF"\[Rule]0,"l"\[Rule]0,"states"\[Rule]{{{{1.`}}}}\[RightAssociation]
and 
level2=basisMixon[[nBR+1,nFR+1]][[1]]=\[LeftAssociation]"nB"\[Rule]1,"degB"\[Rule]0,"nF"\[Rule]1,"degF"\[Rule]0,"l"\[Rule]0,"states"\[Rule]{{{{1.`}}}}\[RightAssociation] 
The function created by primBlock calls monomialBlock to make the matrix elements for monomials, and
adds them together (after multiplying by some prefactors) in the combination dictated by the primary
in the arguments level1 and level2 *)


primBlock[operator_,dnB_,dnF_]=Function[{level1,level2},
	With[{
		lL=level1["l"],lR=level2["l"],
		degBL=level1["degB"],degBR=level2["degB"],
		degFL=level1["degF"],degFR=level2["degF"],
		nB=level1["nB"],nF=level1["nF"]
	},
	(* Take the primary state in the `in' and `out' primary basis element (level1 and level2), 
	and sum over monomial coefficients ck,ck' times monomial matrix elements mkk'
	ck*mkk'*ck'
	ck = #1[[kL+1]]
	ck'= #2[[kR+1]]
	mkk'=monomialBlock[...]
	At the end, multiply by factor = Sqrt[ Gamma[2\[CapitalDelta]]Gamma[2\[CapitalDelta]p] ] * (-1)^(\[CapitalDelta]-\[CapitalDelta]p) / Gamma[\[CapitalDelta]+\[CapitalDelta]p-1], which
	combines the factors from the Fourier transforms of 2- and 3-point functions, and
	factorM, which accounts for some factors of 2 pi in the fields in the interaction term *)
		SparseArray@Outer[
			Total[Table[
				Flatten[#1[[kL+1]]].
				monomialBlock[operator,
					{nB,nB+dnB},{nF,nF+dnF},{degBL+kL,degBR+kR},
					{degFL+lL-kL,degFR+lR-kR}
				].
				Flatten[#2[[kR+1]]],
			{kL,0,lL},{kR,0,lR}],2]&,
		level1["states"],
		level2["states"],
		1]*factor[nB+3/2nF+degBL+degFL+lL,(nB+dnB)+3/2(nF+dnF)+degBR+degFR+lR]*
		factorM[operator]*factorPhase[degBL+degFL+lL,degBR+degFR+lR]
	]
];


ClearAll[factor]
factor[\[CapitalDelta]_,\[CapitalDelta]p_]:=factor[\[CapitalDelta],\[CapitalDelta]p]=Sqrt[ Gamma[2\[CapitalDelta]]Gamma[2\[CapitalDelta]p] ]  / Gamma[\[CapitalDelta]+\[CapitalDelta]p-1];
ClearAll[factorPhase]
factorPhase[deg_,degP_]:=(-1)^(deg-degP)


ClearAll[factorM]
factorM[yukawaCubic]=With[{m=3},(1/Sqrt[4\[Pi]])^(m-2) * (-1)^m ];
factorM[yukawaQuartic]=With[{m=4},(1/Sqrt[4\[Pi]])^(m-2) * (-1)^m];


(* ::Section::Closed:: *)
(*Matrix contracting an array of monomials*)


(*This is a wrapper to apply operators to the monomials - the operator argument of
monomialsBlock is a function, which is applied at the end of the routine to the
bincounts a1,a2,b1,b2 of the in and out monomials.

The function monomialsBoson takes boson number nB and degree degB and produces a list of monomials - this
function defines a canonical ordering (that we always use) of monomials with the same particle number and degree.
Similarly for monomialsFermion.

The output of monomialBlock is a matrix of "operator" (here, this will be yukawaCubic or yukawaQuartic) applied
to an `in' list and an `out' list of all the bincounts of all the monomials produced by monomialsBoson and
monomialsFermion (and their combinations) *)


ClearAll[monomialBlock]
monomialBlock[operator_,{nBL_,nBR_},{nFL_,nFR_},{degB1_,degB2_},{degF1_,degF2_}]:=
monomialBlock[operator,{nBL,nBR},{nFL,nFR},{degB1,degB2},{degF1,degF2}]=With[
	{
		a1List=cfBinCount[#,Max[degB1,degB2]+1]&/@monomialsBoson[nBL,degB1],
		a2List=cfBinCount[#,Max[degB1,degB2]+1]&/@monomialsBoson[nBR,degB2],
		b1List=cfBinCount[#,Max[degF1,degF2]+1]&/@monomialsFermion[nFL,degF1],
		b2List=cfBinCount[#,Max[degF1,degF2]+1]&/@monomialsFermion[nFR,degF2]
	},
	Outer[
		operator,
		(* Here, we combine the table of boson bincounts and fermion bincounts to make tables of all
		the "mixon" bincounts*)
		Flatten[Outer[List,a1List,b1List,1],1],
		Flatten[Outer[List,a2List,b2List,1],1],
	1]//SparseArray
]




(* ::Section:: *)
(*Monomial contractions*)


(* ::Subsection:: *)
(*Yukawa cubic operator contracting with monomials*)


(* 
	yukawaCubic[] computes the matrix element of yukawa
	\[Phi]\[Psi](1/\[PartialD])\[Psi] operator with two monomials. 
	
	Most of the work involved is efficiently doing the sum over all allowed contractions of the interaction
	with the external state, i.e. the sum over kvec and kvec' is too slow if we do it by brute force. But most of
	the entries are empty, and many terms are equivalent since they are related by symmetry. So we instead
	look at the bincounts of the in and out states and ask when can k's be removed from the in and out states
	so that what remains is the same on both sides; and we group together equivalent terms and multiply
	by a symmetry factor.  The generating function factors g(ki,si) are simple by comparison and are computed 
	as subroutines.
	
	The inputs of yukawa[] are the occupation number representation of k and k'.
	a -> scalar k from in state
	b -> fermion k from in state
	ap -> scalar k' from out state
	bp -> fermion k' from out state
	
 *)
yukawaCubic[{a_,b_},{ap_,bp_},OptionsPattern[]]:=Block[
	{
		aDiff=a-ap,bDiff=b-bp,da,db,
		aDiffAbs,bDiffAbs,
		aBar,apBar,bBar,bpBar,
		k1,k2,k3,s1,s2,s3,
		k\[Psi],k\[Psi]p,
		symFactor,perm,
		result,
		myPrint=If[OptionValue[debug],Print,skipPrint],
		debug1=OptionValue[debug],
		showDiagram1=OptionValue[showDiagram]
	},
	(* The change in bosons must be +/-1; if it is +1, swap it to -1 by Hermiticity.
	The change in fermions must be +/-2 or 0.  Check that these conditions are met. *)
	da=Total[-aDiff];db=Total[-bDiff];
	Which[
		da==1,
		Return[yukawaCubic[{ap,bp},{a,b},debug->debug1,showDiagram->showDiagram1]],
		da==-1&&(db==0||db==2||db==-2),
		myPrint["change of particle number is legal"];,
		True,
		myPrint["change of particle number is illegal"];
		Return[0]
	];
	(* Set the bincount aBar for the boson contraction from the in state.  
	Because the boson number changes by 1, the in and out monomials must differ by exactly one bincount
	in exactly one bin, so this fixes where the boson interaction is contracted - i.e. the contraction is
	not "free"  *)
	aBar=Ramp[aDiff];
	If[Total[aBar]!=1,Return[0]];
	k1=cfBinReconstruct[aBar]//First;
	s1=-1;
	symFactor=a[[k1]]//Sqrt;
	bDiffAbs=Abs[bDiff]//Total;
	
	(* The fermion bincounts can change by +/-2 or by 0.  If it changes by 2, then this fixes where the 
	fermion interaction is contracted - i.e. the contraction is not "free".
	If it changes by 0, then the fermion interaction can contract with any external fermion state as long
	as it contracts the same for the in and out monomial - i.e. the contraction is "free".  
	*)
	result=Flatten[Reap[Which[
		bDiffAbs==0,
		
		(* Deal with the free case first *)
		myPrint["\n|\[Delta]b|=0, fermion part contracing same k from both sides."];
		myPrint["--- Iterating all possible fermion k\[Element]",
		"\!\(\*OverscriptBox[\(k\),\(\[RightVector]\)]\)=",cfBinReconstruct[b]];
		Block[{k=1},Scan[(
			If[#!=0,
				Sow[ symFactor*yukawaCubicDiagram[k1,s1,k,-1,k,1] ];
				Sow[ -symFactor*yukawaCubicDiagram[k1,s1,k,1,k,-1] ];
			];
			k++;
		)&,b] ];
		myPrint["--- Iteration finished"],
		
		bDiffAbs==2,
		(* Next, if difference in bincount is +/-2, then bBar and bpBar are fixed *)
		myPrint["\n|\[Delta]b|=2, fermion part contracing a pair of different k."];
		bBar=Ramp[bDiff];
		bpBar=Ramp[-bDiff];
		k\[Psi]=cfBinReconstruct[bBar];
		k\[Psi]p=cfBinReconstruct[bpBar];
		myPrint["k=",k\[Psi],", k'=",k\[Psi]p];
		perm=(Times@@Table[
				(-1)^Total[Take[b,k]],{k,k\[Psi]}
		])*(Times@@Table[
				(-1)^Total[Take[bp,kp]],{kp,k\[Psi]p}
		])*If[Length[k\[Psi]]==1,1,-1];
		{k2,k3}=Join[k\[Psi]//Reverse,k\[Psi]p];
		{s2,s3}=Join[k\[Psi]*0-1,k\[Psi]p*0+1];
		Sow[ symFactor*perm*yukawaCubicDiagram[k1,s1,k2,s2,k3,s3] ];
		Sow[ symFactor*(-perm)*yukawaCubicDiagram[k1,s1,k3,s3,k2,s2] ];,
		
		True,
		myPrint["|\[Delta]b| \[NotEqual] 0 or 2, contraction is impossible."];
		Return[0]
	]][[2]],1]//Total;
	
	Return[result]
];
Options[yukawaCubic]={debug->False,showDiagram->False};


(*  This is the generating function factor g(ki,si) for the cubic Yukawa term *)
yukawaCubicDiagram=Function[
	{k1,s1,k2,s2,k3,s3},
	(-s3/Sqrt[k1 k2(k2+1) k3(k3+1)]) (-GY1[k3,k1,k2,s1 s3,s2 s3]/2)
]


(* ::Subsection:: *)
(*Yukawa Quartic operator contracting with monomials*)


(* 
	yukawaQuartic[] computes the matrix element of yukawa
	\[Phi]\[Psi](1/\[PartialD])\[Phi]\[Psi] operator with two monomials.

	Most of the work involved is efficiently doing the sum over all allowed contractions of the interaction
	with the external state, i.e. the sum over kvec and kvec' is too slow if we do it by brute force. But most of
	the entries are empty, and many terms are equivalent since they are related by symmetry. So we instead
	look at the bincounts of the in and out states and ask when can k's be removed from the in and out states
	so that what remains is the same on both sides; and we group together equivalent terms and multiply
	by a symmetry factor.  The generating function factors g(ki,si) are simple by comparison and are computed 
	as subroutines.
	

	The inputs of yukawa[] are the occupation number representation of k and k'.
	a -> scalar k from in state
	b -> fermion k from in state
	ap -> scalar k' from out state
	bp -> fermion k' from out state
 *)
yukawaQuartic[{a_,b_},{ap_,bp_},OptionsPattern[]]:=Block[
	{
		aDiff=a-ap,bDiff=b-bp,da,db,
		aDiffAbs,bDiffAbs,
		aBar,apBar,bBar,bpBar,
		flagScalarFree=False,flagFermionFree=False,
		k1,k2,k3,k4,s1,s2,s3,s4,
		k\[Phi],k\[Phi]p,k\[Psi],k\[Psi]p,
		symFactor,perm,
		scalarPiece,fermionPiece,
		myPrint=If[OptionValue[debug],Print,skipPrint],
		debug1=OptionValue[debug],
		showDiagram1=OptionValue[showDiagram]
	},
	(* 
		The first step is to take the difference between a and ap, and between b and
		bp, i.e. the difference between k and k'.  The difference is stored in 
		'aDiff' and 'bDiff'.

		We can skip the computation if the total change of boson number, 'da', and
		fermion number, 'db' are both 2 or both -2, since in LC quantization particles cannot be created from
		vacuum.

		We can also skip the computation for half of the elements since the element
		is invariant swapping k\[LeftRightArrow]k'. We need a rule for which half of
		the computation will be skipped. Here the rule is when da<0||(da==0&&db<0)
		the computation is skipped.
	*)
	da=Total[-aDiff];db=Total[-bDiff];
	myPrint["\!\(\*SubscriptBox[\(\[CapitalDelta]n\), \(a\)]\)=",da,
	",\!\(\*SubscriptBox[\(\[CapitalDelta]n\), \(b\)]\)=",db "."];
	Which[
		da<0||(da==0&&db<0),
		myPrint["\!\(\*SubscriptBox[\(\[CapitalDelta]n\), \(a\)]\)<0 or",
		"(\!\(\*SubscriptBox[\(\[CapitalDelta]n\), \(a\)]\)=0 and",
		"\!\(\*SubscriptBox[\(\[CapitalDelta]n\), \(b\)]\)<0), swapping",
		"k\[LeftRightArrow]k'.\n"];
		Return[yukawaQuartic[{ap,bp},{a,b},debug->debug1,showDiagram->showDiagram1]],
		da==2&&db==2,
		myPrint["Contraction (if possible) is zero mode."];
		Return[0]
	];

	(* 
		The following code checks the avalability of a contraction (separately for
		scalars and fermions, and the types of the contraction. ) 
		For scalars: first compute aDiffAbs as the total of abs(\[Delta]a). 
			- If aDiffAbs == 2, it means the total difference between a and ap is 2 (no
			matter whether the difference come from a or ap or both).  Then set
			flagScalarFree = False because this is the "non-free" case in the sense
			that the contraction is restricted to the difference between a and ap.
			- If aDiffAbs == 0, it means a === ap. Then the contraction is "free" in the
			sense that the contraction can be any of the k==k' in vec(k) and vec(k').
			Set flagScalarFree = True to raise the flag to iterate all possible k
			later.
			- If aDiffAbs is anything else then no contraction is available, return
			zero.
		The flagFermionFree part does the same for fermions.
	 *)
	aDiffAbs=Abs[aDiff]//Total;
	bDiffAbs=Abs[bDiff]//Total;
	myPrint["|\[Delta]a|=",aDiffAbs];
	myPrint["|\[Delta]b|=",aDiffAbs];
	flagScalarFree=Which[
		aDiffAbs==2,False,
		aDiffAbs==0,True,
		True,
		myPrint["|\[Delta]a| \[NotEqual] 0 or 2, contraction is impossible."];
		Return[0]		
	];
	flagFermionFree=Which[
		bDiffAbs==2,False,
		bDiffAbs==0,True,
		True,
		myPrint["|\[Delta]b| \[NotEqual] 0 or 2, contraction is impossible."];
		Return[0]		
	];
	
	(*  THESE EQUATION NUMBERS REFER TO PRIVATE NOTES - NEED TO MOVE THEM TO A PUBLIC README
	DOCUMENTATION FILE
		In this part we list out all needed information for each possible scalar
		contractions: the info required by (4.56) is the symmetry factor, k1, k3, s1
		and s3. The result is organized as 
			{symmetry factor, k1, s1, k3, s3}.
		The program sends to 'scalarPiece' an instance of the above list for each
		way to draw the scalar part of the diagram. Each list, when combined with
		the fermion part, becomes a term in (4.56).

		- If flagScalarFree==True, we iterate k. For each k, the program uses a_k and
		ap_k to compute the symmetry factor and sends two instances of the above
		list where the latter one has (k1,s1)\[LeftRightArrow](k3,s3).

		- If flagScalarFree==False, then aBar and apBar are fixed using (4.62):
			aBar=Ramp[aDiff] takes only the positive elements in the difference aDiff.
			It encodes all the k in the in-state to be contracted. 
			apBar=Ramp[-aDiff] takes only the (absolute value of) negative elements in
			the difference aDiff. It encodes all the k' in the out-state to be
			contracted. 
			To decode the k and k' from the occupation vector aBar and apBar, the
			program uses cfBinReconstruction:
				cfBinReconstruction(aBar) returns an ordered set of k whose bin count is
				aBar.
			For details of cfBinReconstruction see its own comments.
		Two instances will be sent with the second one being
			 (k1,s1)\[LeftRightArrow](k3,s3).

		The symmetry factor is computed in (4.66)
	 *)
	scalarPiece=Flatten[Reap[If[
		flagScalarFree,
		
		(* flagScalarFree==True, we iterate k *)
		myPrint["\n|\[Delta]a|=0, scalar part contracing same k from both sides."];
		myPrint["--- Iterating all possible scalar k\[Element]",
		"\!\(\*OverscriptBox[\(k\),\(\[RightVector]\)]\)=",cfBinReconstruct[a]];
		Block[{k=1},Scan[(
			If[#!=0,
				(* sending {symmetry factor, k1, s1, k3, s3} *)
				Sow[{2#,k,1,k,-1}];
				myPrint["    sending {\!\(\*SubscriptBox[OverscriptBox[\(S\), \(~\)],
				\(sym\)]\),\!\(\*SubsuperscriptBox[\(k\), \(1\), SubscriptBox[\(s\),
				\(1\)]]\),\!\(\*SubsuperscriptBox[\(k\), \(3\), SubscriptBox[\(s\),
				\(3\)]]\)}=",{2#,SuperscriptBox[k,"+"],SuperscriptBox[k,"-"]}//DisplayForm];
				(* sending (k1,s1)\[LeftRightArrow](k3,s3) *)
				Sow[{2#,k,-1,k,1}];
				myPrint["    sending {\!\(\*SubscriptBox[OverscriptBox[\(S\), \(~\)],
				\(sym\)]\),\!\(\*SubsuperscriptBox[\(k\), \(1\), SubscriptBox[\(s\),
				\(1\)]]\),\!\(\*SubsuperscriptBox[\(k\), \(3\), SubscriptBox[\(s\),
				\(3\)]]\)}=",{2#,SuperscriptBox[k,"-"],SuperscriptBox[k,"+"]}//DisplayForm];
			];
			k++;
		)&,a] ];
		myPrint["--- Iteration finished"],
		
		(* flagScalarFree==False, then aBar and apBar are fixed *)
		myPrint["\n|\[Delta]a|=2, scalar part contracing a pair of different k."];
		aBar=Ramp[aDiff];
		apBar=Ramp[-aDiff];
		k\[Phi]=cfBinReconstruct[aBar];
		k\[Phi]p=cfBinReconstruct[apBar];
		myPrint["k=",k\[Phi],", k'=",k\[Phi]p];
		symFactor=2*(Times@@Table[
			Sqrt[ Binomial[a[[k]],aBar[[k]] ]/(aBar[[k]]!) ],
			{k,DeleteDuplicates[k\[Phi]]}
		])*(Times@@Table[
			Sqrt[ Binomial[ap[[kp]],apBar[[kp]] ]/(apBar[[kp]]!) ],
			{kp,DeleteDuplicates[k\[Phi]p]}
		]);
		{k1,k3}=Join[k\[Phi],k\[Phi]p];
		{s1,s3}=Join[k\[Phi]*0-1,k\[Phi]p*0+1];
		(* sending {symmetry factor, k1, s1, k3, s3} *)
		Sow[{symFactor,k1,s1,k3,s3}];
		myPrint["    sending {\!\(\*SubscriptBox[OverscriptBox[\(S\), \(~\)],
		\(sym\)]\),\!\(\*SubsuperscriptBox[\(k\), \(1\), SubscriptBox[\(s\),
		\(1\)]]\),\!\(\*SubsuperscriptBox[\(k\), \(3\), SubscriptBox[\(s\),
		\(3\)]]\)}=",{symFactor,SuperscriptBox[k1,sgn[s1]],SuperscriptBox[k3,sgn[s3]]}//DisplayForm];
		(* sending (k1,s1)\[LeftRightArrow](k3,s3) *)
		Sow[{symFactor,k3,s3,k1,s1}];
		myPrint["    sending {\!\(\*SubscriptBox[OverscriptBox[\(S\), \(~\)],
		\(sym\)]\),\!\(\*SubsuperscriptBox[\(k\), \(1\), SubscriptBox[\(s\),
		\(1\)]]\),\!\(\*SubsuperscriptBox[\(k\), \(3\), SubscriptBox[\(s\),
		\(3\)]]\)}=",{symFactor,SuperscriptBox[k3,sgn[s3]],SuperscriptBox[k1,sgn[s1]]}//DisplayForm];
	]][[2]],1];
	
	(* 
		In this part we list out all needed information for each possible fermion
		contractions: the info required by (5.56) is the (-1)^permutation, k2, k4,
		s2 and s4. The result is organized as 
			{(-1)^permutation, k2, s2, k4, s4}.
		The program sends to 'fermionPiece' an instance of the above list for each
		way to draw the fermion part of the diagram. Each list, when combined with
		the scalar part, becomes a term in (5.56).

		- If flagFermionFree==True, we iterate k. Since b==bp the permutation is
		always even. For each k, the program sends one instance of the above list.

		- If flagFermionFree==False, then bBar and bpBar are fixed using (5.63). k2,
		s2, k4 and s4 can be determined by cfBinReconstruction[]. The details are
		the same as the scalar contraction. 
		The program uses b_k and bp_k to compute the permutation number according to
		(5.60). 
		One instance of the result will be sent to 'fermionPiece'.
	 *)
	fermionPiece=Flatten[Reap[If[
		flagFermionFree,
		
		(* If flagFermionFree==True, we iterate k *)
		myPrint["\n|\[Delta]b|=0, fermion part contracing same k from both sides."];
		myPrint["--- Iterating all possible fermion k\[Element]",
		"\!\(\*OverscriptBox[\(k\),\(\[RightVector]\)]\)=",cfBinReconstruct[b]];
		Block[{k=1},Scan[(
			(* {(-1)^permutation, k2, s2, k4, s4} *)
			If[#!=0,Sow[{1,k,1,k,-1}];
			
			myPrint["    sending {(-1\!\(\*SuperscriptBox[\()\),
			\(\[Sigma]\)]\),\!\(\*SubsuperscriptBox[\(k\), \(2\), SubscriptBox[\(s\),
			\(2\)]]\),\!\(\*SubsuperscriptBox[\(k\), \(4\), SubscriptBox[\(s\),
			\(4\)]]\)}=",{1,SuperscriptBox[k,"-"],SuperscriptBox[k,"+"]}//DisplayForm];
			];
			k++;
		)&,b] ];
		myPrint["--- Iteration finished"],
		
		(* If flagFermionFree==False, then bBar and bpBar are fixed *)
		myPrint["\n|\[Delta]b|=2, fermion part contracing a pair of different k."];
		bBar=Ramp[bDiff];
		bpBar=Ramp[-bDiff];
		k\[Psi]=cfBinReconstruct[bBar];
		k\[Psi]p=cfBinReconstruct[bpBar];
		myPrint["k=",k\[Psi],", k'=",k\[Psi]p];
		perm=(Times@@Table[
				(-1)^Total[Take[b,k]],{k,k\[Psi]}
		])*(Times@@Table[
				(-1)^Total[Take[bp,kp]],{kp,k\[Psi]p}
		])*If[Length[k\[Psi]]==1,1,-1];
		{k4,k2}=Join[k\[Psi]//Reverse,k\[Psi]p];
		{s4,s2}=Join[k\[Psi]*0-1,k\[Psi]p*0+1];
		myPrint["    sending {(-1\!\(\*SuperscriptBox[\()\),
		\(\[Sigma]\)]\),\!\(\*SubsuperscriptBox[\(k\), \(2\), SubscriptBox[\(s\),
		\(2\)]]\),\!\(\*SubsuperscriptBox[\(k\), \(4\), SubscriptBox[\(s\),
		\(4\)]]\)}=",{perm,SuperscriptBox[k2,sgn[s2]],SuperscriptBox[k4,sgn[s4]]}//DisplayForm];
		(* {(-1)^permutation, k2, s2, k4, s4} *)
		Sow[{perm,k2,s2,k4,s4}];
	]][[2]],1];
	

	(* 
		After obtaining the contraction info for both scalars and fermions, this
		subroutine put them together and spits out diagrams (and computes them). Any
		instances in 'scalarPiece' can merge with any instances in 'fermionPiece' so
		the diagrams list will be an outer product of lists 'scalarPiece' and
		'fermionPiece'. Each diagram then has full info:
			{symmetry factor, k1, s1, k3, s3} and {(-1)^permutation, k2, s2, k4, s4}
		from both pieces which can be plugged in as one term of (5.56).
		computeDiagram[options][scalar instance, fermion instance] plugs in the info
		of one diagram and computes (5.56) and gets a number.

		All the diagrams are then summed to give the final result of the sum in (5.56).
	 *)
	myPrint["\n--- Assembling Diagrams"];
	myPrint["    DIAGRAM \[Congruent] (-1\!\(\*SuperscriptBox[\()\),
	\(\[Sigma]\)]\) \!\(\*SubscriptBox[OverscriptBox[\(S\), \(~\)], \(sym\)]\) \[Times] \n",
	 "      ", FractionBox["-\!\(\*SubscriptBox[\(s\),
	\(1\)]\)\!\(\*SubscriptBox[\(s\), \(2\)]\)\!\(\*SubscriptBox[\(s\),
	\(3\)]\)\!\(\*SubscriptBox[\(s\), \(4\)]\)","\!\(\*SubscriptBox[\(k\),
	\(1\)]\)\!\(\*SubscriptBox[\(k\), \(3\)]\)2\!\(\*SubscriptBox[\(k\),
	\(2\)]\)(\!\(\*SubscriptBox[\(k\), \(2\)]\)+1)2\!\(\*SubscriptBox[\(k\),
	\(4\)]\)(\!\(\*SubscriptBox[\(k\), \(4\)]\)+1)"//SqrtBox]//DisplayForm,
	SubscriptBox[g,Row[{\[Phi],\[Psi],FractionBox[1,"\[PartialD]"],\[Phi],\[Psi]}]]//DisplayForm,
	"(\!\(\*SubsuperscriptBox[\(k\), \(1\), SubscriptBox[\(s\),
	\(1\)]]\),\!\(\*SubsuperscriptBox[\(k\), \(2\), SubscriptBox[\(s\),
	\(2\)]]\),\!\(\*SubsuperscriptBox[\(k\), \(3\), SubscriptBox[\(s\),
	\(3\)]]\),\!\(\*SubsuperscriptBox[\(k\), \(4\), SubscriptBox[\(s\),
	\(4\)]]\))"
	];
	Return[Total[Outer[yukawaQuarticDiagram[debug1,showDiagram1],fermionPiece,scalarPiece,1],2]]
];
Options[yukawaQuartic]={debug->False,showDiagram->False};


ClearAll[yukawaQuarticDiagram]
yukawaQuarticDiagram[debug_,showDiagram_][
	{perm_,k2_,s2_,k4_,s4_},
	{symFactor_,k1_,s1_,k3_,s3_}
]:=Block[
	{
		(* 
			'diagramResult' is symmetry factors times GY[], where GY[] is literally
			the g_{\[Phi]\[Psi](1/\[PartialD])\[Phi]\[Psi]} factor. See the comments of
			GY[]. 
		*)
		diagramResult=symFactor*perm*
		(-1/Sqrt[k1 k3 k2(k2+1) k4(k4+1)])*
		GY[k1,k2,k3,k4,s1,s2,s3,s4],
		myPrint=If[debug,Print,skipPrint]
	},
	(* This following part prints out debug info *)
	myPrint["\n    \[FilledSquare]{\!\(\*SubscriptBox[OverscriptBox[\(S\),
	\(~\)], \(sym\)]\),(-1\!\(\*SuperscriptBox[\()\),
	\(\[Sigma]\)]\),\!\(\*SubsuperscriptBox[\(k\), \(1\), SubscriptBox[\(s\),
	\(1\)]]\),\!\(\*SubsuperscriptBox[\(k\), \(2\), SubscriptBox[\(s\),
	\(2\)]]\),\!\(\*SubsuperscriptBox[\(k\), \(3\), SubscriptBox[\(s\),
	\(3\)]]\),\!\(\*SubsuperscriptBox[\(k\), \(4\), SubscriptBox[\(s\),
	\(4\)]]\)} = ",
		{symFactor,perm,
			SuperscriptBox[k1,sgn[s1]],
			SuperscriptBox[k2,sgn[s2]],
			SuperscriptBox[k3,sgn[s3]],
			SuperscriptBox[k4,sgn[s4]]
		}//DisplayForm
	];
	myPrint["      ",myDiagram[s1,s2,s3,s4][k1,k2,k3,k4],
		" = ",diagramResult
	];
	(* returning the result *)
	diagramResult
];


(* ::Section:: *)
(*Diagrams and g factors*)


(* ::Subsection:: *)
(*The summarized Yukawa factor Subscript[g, Y]*)


(* This function is the g_{\[Phi]\[Psi](1/\[PartialD])\[Phi]\[Psi]} factor.

	We moved out a factor (1/2) from GY1[] to here, so that compiled function GY1[] is purely integral.
	See the comments of GY1, GY2 and GYLog for details.
  *)
GY[k1_,k2_,k3_,k4_,s1_,s2_,s3_,s4_]:=Block[
	{
		k=s1 s2 k1 + k2,
		sk,l
	},
	-(If[k>=0,sk=1;l=k,sk=-1;l=-k-1];
	s1 k1( GY2[l,k3,k4,sk s2 s3,sk s2 s4]
	 - GY2[k1,k3,k4,s1 s3,s1 s4])
	-s1 (1/2)*GY1[k1,k3,k4,s1 s3,s1 s4]
	-s2 (1/2)*GY1[k2,k3,k4,s2 s3,s2 s4]
	+sk s2 (1/2)*GY1[l,k3,k4,sk s2 s3,sk s2 s4]
	(*-If[s1 s2<0&&k1<=k2, k1 GYLog[k3,k4,s3,s4],0 ]*)
	+If[s1 s2<0&&k1<=k2, k1 GYLog[k3,k4,s3,s4],0 ])
]



(* ::Subsection:: *)
(*The factors Subscript[g, Y,1], Subscript[g, Y,2], and Subscript[g, Y,log]*)


(* The GY1[] follows the corresponding table in appendix D.
	The factor (1/2) is moved out of GY1[] to keep the result integral.
	The function is compiled.
  *)
ClearAll[GY1]
GY1=Compile[
	{
		{k1,_Integer},{k3,_Integer},{k4,_Integer},
		{s3,_Integer},{s4,_Integer}
	},
	(*(1/2)**)Which[
		s3>0&&s4>0,0,
		s3<0&&s4>0,
		If[k1>=k3,(k1-k3) (1+k1-k3),0]
		+If[k4>=k3,(-k3+k4) (1-k3+k4) (1+k1+k4+2 k1 k4),0]
		+If[k4>=1+k3,-k1 (k3-k4) (1+k3-k4) (1+k4),0]
		+If[1+k4>=k3,-(1+k1) k4 (1-k3+k4) (2-k3+k4),0]
		+If[k1+k4>=k3,-(1+k4) (k1-k3+k4) (1+k1-k3+k4),0]
		+If[1+k1+k4>=k3,k4 (1+k1-k3+k4) (2+k1-k3+k4),0],
		s3>0&&s4<0,
		If[k1>=k4,(k1-k4) (1+k1-k4) (1+k4),0]
		+If[k1>=1+k4,-(-1+k1-k4) (k1-k4) k4,0]
		+If[k3>=k4,(1+k1) (k3-k4) (1+k3-k4) (1+k4),0]
		+If[k3>=1+k4,-(-1+k3-k4) (k3-k4) (k1+k4+2 k1 k4),0]
		+If[k3>=2+k4,k1 (-2+k3-k4) (-1+k3-k4) k4,0]
		+If[k1+k3>=k4,(-1-k4) (k1+k3-k4) (1+k1+k3-k4),0]
		+If[k1+k3>=1+k4,(-1+k1+k3-k4) (k1+k3-k4) k4,0],
		s3<0&&s4<0,
		-k1 (1+k1)
		+If[k1>=k3,(k1-k3) (1+k1-k3),0]
		+If[k1>=k4,(k1-k4) (1+k1-k4) (1+k4),0]
		+If[k1>=1+k4,-(-1+k1-k4) (k1-k4) k4,0]
		+If[k1>=k3+k4,-(k1-k3-k4) (1+k1-k3-k4) (1+k4),0]
		+If[k1>=1+k3+k4,(-1+k1-k3-k4) (k1-k3-k4) k4,0],
		True,0
	],
	CompilationTarget->"C",
	CompilationOptions->{
		"InlineExternalDefinitions" -> True,
		"ExpressionOptimization" -> True
	}
]


(* The GY2[] follows the corresponding table in appendix D.
	hsum[k,p] is the \[CapitalSigma](k,p) defined just above the table. The result of hsum[] is memoized.
	hsum[k,p] refers to myHarmonic[], a memoized version of HarmonicNumber[].
*)
ClearAll[GY2,hsum,myHarmonic]
myHarmonic[p_]:=myHarmonic[p]=(*(Sign[p])*)HarmonicNumber[Abs[p]];
hsum[k_,p_]:=hsum[k,p]=If[k>p,k-p-p(myHarmonic[k]-myHarmonic[p]),0];
GY2=Function[
	{k,k3,k4,s3,s4},
	Which[
		s3>0&&s4>0,0,
		s3<0&&s4>0,
		k-hsum[k,k3]
		+If[k4<=k3,-(1+k4) (k-hsum[k,k3-k4]),0]
		+If[1+k4<=k3,k4 (k-hsum[k,-1+k3-k4]),0],
		s3>0&&s4<0,
		k-(1+k4) hsum[k,k4]+k4 hsum[k,1+k4]
		+If[k3<=k4,-(1+k4) (k-hsum[k,-k3+k4]),0]
		+If[k3<=1+k4,k4 (k-hsum[k,1-k3+k4]),0],
		s3<0&&s4<0,
		k-hsum[k,k3]-(1+k4) hsum[k,k4]
		+k4 hsum[k,1+k4]+(1+k4) hsum[k,k3+k4]
		-k4 hsum[k,1+k3+k4],
		True,0
	]
]


(* The log factor GYLog[] is (-1) times the generating function Subscript[g, Y,log] as given in the corresponding table in appendix D *)


GYLog=Function[{k3,k4,s3,s4},Which[
	s3==-1&&s4==-1,
	k3 (-myHarmonic[k3]+myHarmonic[k3+k4]),
	s3==-1&&s4==1,
	-k3 myHarmonic[k3]+(k3-k4) (1+k4) myHarmonic[k3-k4]+k4 (-1+(1-k3+k4) myHarmonic[1-k3+k4]),
	s3==1&&s4==-1,
	k4+k3 myHarmonic[k3]+(1+k4) (-k3+k4) myHarmonic[k3-k4]+(-1+k3-k4) k4 myHarmonic[1-k3+k4],
	s3==1&&s4==1,k3 (myHarmonic[k3]-myHarmonic[k3+k4]),
	True,Print["exception"];Abort[];
] ];


(* ::Section::Closed:: *)
(*debug*)


sgn[1]="+";
sgn[-1]="-";


skipPrint[expr_]:=Null;
SetAttributes[skipPrint,HoldAll];


(* ::Section:: *)
(*End*)


End[]


EndPackage[]
