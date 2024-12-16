(* ::Package:: *)

(* ::Chapter:: *)
(*Shared code*)


(* ::Section::Closed:: *)
(*Utilities*)


sparseArrayFlatten[mat_] := Block[
      {matNonEmpty = mat, dims,
        rows, cols, res},
      dims = {
     (DeleteCases[{}] /@ Map[Dimensions, matNonEmpty, {2}])[[;; , 1, 
       1]],
     (DeleteCases[{}] /@ 
        Transpose[Map[Dimensions, matNonEmpty, {2}]])[[;; , 1, 2]]
     };
      rows = Prepend[dims[[1]] // Accumulate, 0];
      cols = Prepend[dims[[2]] // Accumulate, 0];
      res = Sum[SparseArray[
            
      Band[{ (rows[[i]] + 1), (cols[[j]] + 1)}, {rows[[i + 1]], 
                  cols[[j + 1]]}] -> matNonEmpty[[i, j]],
            {Last[rows], Last[cols]}],
          {i, Length[rows] - 1}, {j, Length[cols] - 1}
          ];
      res
      ];


(* ::Section:: *)
(*Integer partition and a basis*)


(* ::Input::Initialization:: *)
(*maxNumANS[kTot_]:=Floor[1/2+1/2Sqrt[1+4(2kTot-2)]];
maxNumANS[0]=1;*)


maxNumDeg[deg_]:=1/2 (1+Sqrt[1+8 deg]);


ClearAll[partitionsFermion]
partitionsFermion[n_,k_,s_]:=partitionsFermion[n,k,s]=Block[
{dl,set},
Flatten[Reap[Do[
	(*Print[{n-s,k-1,j}];*)
	set=partitionsFermion[n-s,k-1,j];
	If[Length[set]>0,
		Sow[ 
			(-Sort[-Append[#,k-1+s]])&/@set
		]
	],{j, Max[1,Floor[(n-s)/(k-1)]], Min[s,n-s-k+2] }
] ][[2]],2] ];
partitionsFermion[n_,k_,s_]/;s+k-1>n||n>k*s:={};
partitionsFermion[s_,1,s_]={{s}};
partitionsFermion[0,0,0]={{}};
partitionsFermion[n_,k_]:=Join@@Table[partitionsFermion[n,k,s],{s,Ceiling[n/k],n-k+1}]


ClearAll[aBasis]
aBasis[nA_, degB_, kMaxB_] := 
  aBasis[nA, degB, kMaxB] = 
   MapIndexed[#1 -> #2[[1]] &, 
     partitionsFermion[degB + nA, nA, kMaxB + 1] - 1] // Association;
aBasis[0, 0, 0] := <|{} -> 1|>;
aBasis[nA_, degF_] := Block[
    {degB = degF - lF[nA], idx = 0},
    MapIndexed[
     #1 -> #2[[1]] &,
     Join @@ Table[
       aBasis[nA, degB, kMaxB] // Keys,
       {kMaxB, Ceiling[degB/nA], degB}]
     ]
    ] // Association;
aBasis[0, 0] = aBasis[0, 0, 0];


lF[n_]:=n (n-1)/2;


ClearAll[mapPrependA$Aspace]
mapPrependA$Aspace[kF_, nA_, degB_, kMaxB_] := 
  mapPrependA$Aspace[kF, nA, degB, kMaxB] = Block[
    {basisLow = aBasis[nA, degB, kMaxB] // Keys,
     basisUp = aBasis[nA + 1, degB + kF - nA, kF - nA],
     kVecP, s, mat},
    mat = SparseArray[{}, {basisUp // Length, basisLow // Length}];
    Do[With[{kVec = basisLow[[i]]},
      		kVecP = Prepend[kVec, kF];
      		s = Signature[-kVecP];
      		If[s != 0, mat[[basisUp[-Sort[-kVecP] ] , i ]] += s]
      	], {i, Length[basisLow]}];
    mat
    ];


(* ::Chapter:: *)
(*Define Sigma*)


(* ::Section:: *)
(*C basis and factors*)


(*factorQ[k_] := Factorial2[2 k - 1]/(2^k Factorial[k])*)


ClearAll[cBasis]
cBasis::nonint = "The argument `1` is not integer.";
cBasis[kTot_] := cBasis[kTot] = (
    If[! IntegerQ[kTot], Message[cBasis::nonint, kTot]; Abort[]];
    Block[
     {idx = cBasis[kTot - 1][[-1]] + 1,
      set = IntegerPartitions[kTot]},
     Join[
      cBasis[kTot - 1],
      (# -> idx++) & /@ Select[set, DuplicateFreeQ] // Association,
      (Append[#, 0] -> idx++) & /@ Select[set, DuplicateFreeQ] // 
       Association
      ]
     ]);
cBasis[0] = <|{} -> 1, {0} -> 2|>;


ClearAll[mapPrependC]
mapPrependC[l_,kTotR_]:=mapPrependC[l,kTotR]=Block[
	{
		kLow=cBasis[kTotR]//Keys,
		kUp=cBasis[kTotR+l],
		kp,s,mat
	},
	mat=SparseArray[{},{kLow//Length,kUp//Length}];
	Do[With[{k=kLow[[i]]},
			kp=Prepend[k,l];
			s=Signature[-kp];
			If[s!=0,mat[[i,kUp[-Sort[-kp] ]  ]]+=s]
		],{i,Length[kLow]}];
	mat
];


ClearAll[embedInLargerCBasis]
embedInLargerCBasis[mat_, {kTotL2_, kTotR2_}] := Block[
   {
    dimL2 = cBasis[kTotL2] // Length,
    dimR2 = cBasis[kTotR2] // Length,
    dims = Dimensions[mat],
    mat2
    },
   mat2 = PadRight[mat, ReplacePart[dims,{1->dimL2, 2->dimR2}]]
   ];
embedInLargerCBasis[mat_, kTotR2_] := Block[
  {
   (*dimL2=cBasis[kTotL2]//Length,*)
   
   dimR2 = cBasis[kTotR2] // Length,
   dims = Dimensions[mat],
   mat2
   },
  mat2 = PadRight[mat, ReplacePart[dims,{1->Length[mat], 2->dimR2}]]
  ]


(* ::Section:: *)
(*Map z=\[Infinity] state basis to C basis*)


ClearAll[mapAOutToC]
mapAOutToC[num_,degB_,kMaxB_]:=mapAOutToC[num,degB,kMaxB]=Block[
	{mat,trans,kF,pow},
	kF=num-1+kMaxB;
	pow = kF+degB-kMaxB+lF[num-1]+Floor[num/2];
	mat=SparseArray[{},{
		Length@aBasis[num,degB,kMaxB],
		Length@cBasis[degB+lF[num]],
		pow + 1,
		pow + 1
	}];
	Do[
		(*Print[{num-1,degB-kMaxB,j},".",{kF,degB-kMaxB+lF[num-1]}];*)
		trans=mapPrependA$Aspace[kF,num-1,degB-kMaxB,j];
		If[trans=={}||aBasis[num-1,degB-kMaxB,j]==<||>||trans["NonzeroValues"]=={},Continue[]];
		mat+=PadRight[
				Transpose[
					(trans . Transpose[mapAOutToC[num-1,degB-kMaxB,j],{1,3,2}]) 
						. mapPrependAOutCspace[kF,degB-kMaxB+lF[num-1]],
					{1,3,2,4}
				],
				Dimensions[mat]
			],
		{j, Max[1,Floor[(degB+num-kMaxB-1)/(num-1)]]-1, Min[kMaxB+1,degB-kMaxB+1]-1}
	];
	Flatten[mat,{{1},{2},{3,4}}] . Flatten[tensorMonoProduct[pow+1,pow+1],1]
];
mapAOutToC[num_,degB_,kMaxB_]/;kMaxB+1+num-1>num+degB||num+degB>num*(kMaxB+1):={};
mapAOutToC[1,k_,k_]:=mapAOutToC[1,k,k]=Block[
	{basisC=cBasis[k],mat},
	mat=SparseArray[{},{1,Length[basisC],k+1}];
	Do[
		mat[[1,basisC[{k-l}]]]+=PadRight[-fCoeffList[l],k+1],
		{l,0,k}
	];
	mat
];
mapAOutToC[0,0,0]=SparseArray[{{{1}}}];
mapAOutToC[num_,degF_]:=mapAOutToC[num,degF]=Block[
	{degB=degF-lF[num]},
	Join@@Table[
		mapAOutToC[num,degB,kMax],
		{kMax,Ceiling[degB/num],degB}]
];
mapAOutToC[0,0]=PadRight[mapAOutToC[0,0,0],{mapAOutToC[0,0,0]//Length,cBasis[0]//Length,1}];


(* ::Subsection:: *)
(*map prepend c*)


ClearAll[mapPrependAOutCspace]
mapPrependAOutCspace[k_,kTotR_]:=mapPrependAOutCspace[k,kTotR]=Block[
	{regularPart,annihilationPart},
	regularPart=Sum[
		embedInLargerCBasis[
			TensorProduct[
				mapPrependC[l,kTotR],
				PadRight[-fCoeffList[k-l],k+kTotR+2]
			],
			{kTotR,kTotR+k}],
		{l,0,k}
	];
	annihilationPart=mapAnnihilateOneCOut[k,kTotR];
	regularPart+annihilationPart
]


ClearAll[mapAnnihilateOneCOut]
mapAnnihilateOneCOut[k_,kTotR_]:=Block[
	{
	monosBefore=cBasis[kTotR],
	monosAfter=cBasis[kTotR+k],
	highestPow = k+kTotR,
	commutatorAdditionalPowMax = 2,
	w,s,factor,mat,monoP
	},
	mat=SparseArray[{},{
		monosBefore//Length,
		monosAfter//Length,
		highestPow + 2,
		commutatorAdditionalPowMax + 1
	}];
	Do[With[{idx=monosBefore[mono]},
		monoP=Drop[mono,{j}];
		w=mono[[j]];
		s=(-1)^(j-1);
		(*factor=factorQ[w+k];*)
		If[1-w<=k&&w!=0,mat[[idx,monosAfter[monoP], (k+w-1)+1,3 ]] += s];
		mat[[idx,monosAfter[monoP], (k+w)+1,2 ]] += s*If[w==0,1/2,1];
		mat[[idx,monosAfter[monoP], (k+w+1)+1,1 ]] += s;
		(*mat[[idx,monosAfter[monoP]  ]]+=s*(factorQ[w+k+1]-factorQ[w+k])*)
	],{mono,monosBefore//Keys},{j,Length[mono]}];
	Flatten[mat,{{1},{2},{3,4}}] . Flatten[tensorFOutWithCommutator[highestPow+1],1]
]


ClearAll[tensorFOutWithCommutator]
tensorFOutWithCommutator[kmax_]:=tensorFOutWithCommutator[kmax]=SparseArray[
	{
		{i_,1,k_}:>-fCoeff[i-1,k-1],
		{i_,2,k_}:>fCoeff[i-1,k-1]+fCoeff[i-1,k-2],
		{i_,3,k_}:>-fCoeff[i-1,k-2]
	},
	{kmax+1,3,kmax+1}
]


fCoeff[m_,p_]:=Pochhammer[1/2,m-p]/Pochhammer[1,m-p] Pochhammer[1/2,p]/Pochhammer[1,p];


ClearAll[fCoeffList];
fCoeffList[m_]:=fCoeffList[m]=SparseArray[{{i_}:>fCoeff[m,i-1]},{m+1}];


ClearAll[tensorMonoProduct]
tensorMonoProduct[dimIn_,dimOut_]:=tensorMonoProduct[dimIn,dimOut]=SparseArray[
	{
		{i_,j_,k_}/;k==i+j-1:>1
	},
	{dimIn,dimIn,dimOut}
]


(* ::Section:: *)
(*Map z=0 state basis to C basis*)


ClearAll[mapAInToC]
mapAInToC[num_,degB_,kMaxB_]:=mapAInToC[num,degB,kMaxB]=Block[
	{mat,trans,kF,pow},
	kF=num-1+kMaxB;
	pow = kF+degB-kMaxB+lF[num-1]+Floor[num/2];
	mat=SparseArray[{},{
		Length@aBasis[num,degB,kMaxB],
		Length@cBasis[degB+lF[num]],
		pow + 1,
		pow + 1
	}];
	Do[
		(*Print[{num-1,degB-kMaxB,j},".",{kF,degB-kMaxB+lF[num-1]}];*)
		trans=mapPrependA$Aspace[kF,num-1,degB-kMaxB,j];
		If[trans=={}||aBasis[num-1,degB-kMaxB,j]==<||>||trans["NonzeroValues"]=={},Continue[]];
		mat+=PadRight[
				Transpose[
					(trans . Transpose[mapAInToC[num-1,degB-kMaxB,j],{1,3,2}]) 
						. mapPrependAInCspace[kF,degB-kMaxB+lF[num-1]],
					{1,3,2,4}
				],
				Dimensions[mat]
			],
		{j, Max[1,Floor[(degB+num-kMaxB-1)/(num-1)]]-1, Min[kMaxB+1,degB-kMaxB+1]-1}
	];
	If[EvenQ[num],
		Flatten[mat,{{1},{2},{3,4}}] . Flatten[tensorMonoProduct[pow+1,pow+1],1],
		Flatten[mat,{{1},{2},{3,4}}] . Flatten[tensorMonoProductOneLower[pow+1,pow+1],1]
	]
];
mapAInToC[num_,degB_,kMaxB_]/;kMaxB+1+num-1>num+degB||num+degB>num*(kMaxB+1):={};
mapAInToC[1,k_,k_]:=mapAInToC[1,k,k]=Block[
	{basisC=cBasis[k],mat},
	mat=SparseArray[{},{1,Length[basisC],k+1}];
	Do[
		mat[[1,basisC[{k-l}]]]+=PadRight[fCoeffList[l],k+1],
		{l,0,k}
	];
	mat
];
mapAInToC[0,0,0]=SparseArray[{{{1}}}];
mapAInToC[num_,degF_]:=mapAInToC[num,degF]=Block[
	{degB=degF-lF[num]},
	Join@@Table[
		mapAInToC[num,degB,kMax],
		{kMax,Ceiling[degB/num],degB}]
];
mapAInToC[0,0]=PadRight[mapAInToC[0,0,0],{mapAInToC[0,0,0]//Length,cBasis[0]//Length,1}];


ClearAll[mapPrependAInCspace]
mapPrependAInCspace[k_,kTotR_]:=mapPrependAInCspace[k,kTotR]=Block[
	{regularPart,annihilationPart},
	regularPart=Sum[
		embedInLargerCBasis[
			TensorProduct[
				mapPrependC[l,kTotR],
				PadRight[Prepend[fCoeffList[k-l],0],k+kTotR+2]
			],
			{kTotR,kTotR+k}],
		{l,0,k}
	];
	annihilationPart=mapAnnihilateOneCIn[k,kTotR];
	regularPart+annihilationPart
]


(*ClearAll[mapAnnihilateOneCIn]
mapAnnihilateOneCIn[k_,kTotR_]:=Block[
	{
	monosBefore=cBasis[kTotR],
	monosAfter=cBasis[kTotR+k],
	highestPow = k+kTotR,
	commutatorAdditionalPowMax = 2,
	w,s,factor,mat,monoP
	},
	mat=SparseArray[{},{
		monosBefore//Length,
		monosAfter//Length,
		highestPow + 2,
		commutatorAdditionalPowMax + 1
	}];
	Do[With[{idx=monosBefore[mono]},
		monoP=Drop[mono,{j}];
		w=mono[[j]];
		s=(-1)^(j-1);
		(*factor=factorQ[w+k];*)
		If[1-w<=k&&w!=0,mat[[idx,monosAfter[monoP], (k+w-1)+1,3 ]] += s];
		mat[[idx,monosAfter[monoP], (k+w)+1,2 ]] += s*If[w==0,1/2,1];
		mat[[idx,monosAfter[monoP], (k+w+1)+1,1 ]] += s;
		(*mat[[idx,monosAfter[monoP]  ]]+=s*(factorQ[w+k+1]-factorQ[w+k])*)
	],{mono,monosBefore//Keys},{j,Length[mono]}];
	Flatten[mat,{{1},{2},{3,4}}].Flatten[tensorFInWithCommutator[highestPow+1],1]
]*)


ClearAll[mapAnnihilateOneCIn]
mapAnnihilateOneCIn[k_,kTotR_]:=Block[
	{
	monosBefore=cBasis[kTotR],
	monosAfter=cBasis[kTotR+k],
	highestPow = k+kTotR,
	commutatorAdditionalPowMax = 2,
	w,s,factor,mat,monoP
	},
	mat=SparseArray[{},{
		monosBefore//Length,
		monosAfter//Length,
		highestPow + 2,
		commutatorAdditionalPowMax + 1
	}];
	Do[With[{idx=monosBefore[mono]},
		monoP=Drop[mono,{j}];
		w=mono[[j]];
		s=(-1)^(j-1);
		(*factor=factorQ[w+k];*)
		If[1-w<=k&&w!=0,mat[[idx,monosAfter[monoP], (k+w-1)+1,3 ]] += s];
		mat[[idx,monosAfter[monoP], (k+w)+1,2 ]] += s*If[w==0,1/2,1];
		mat[[idx,monosAfter[monoP], (k+w+1)+1,1 ]] += s;
		(*mat[[idx,monosAfter[monoP]  ]]+=s*(factorQ[w+k+1]-factorQ[w+k])*)
	],{mono,monosBefore//Keys},{j,Length[mono]}];
	Flatten[mat,{{1},{2},{3,4}}] . Flatten[-tensorFOutWithCommutator[highestPow+1],1]
]


ClearAll[tensorFInWithCommutator]
tensorFInWithCommutator[kmax_]:=tensorFInWithCommutator[kmax]=SparseArray[
	{
		{i_,1,k_}:>fCoeff[i-1,k-2],
		{i_,2,k_}:>-fCoeff[i-1,k-2]-fCoeff[i-1,k-1],
		{i_,3,k_}:>fCoeff[i-1,k-1]
	},
	{kmax+1,3,kmax+1}
]


ClearAll[tensorMonoProductOneLower]
tensorMonoProductOneLower[dimIn_,dimOut_]:=tensorMonoProductOneLower[dimIn,dimOut]=SparseArray[
	{
		{i_,j_,k_}/;k==i+j-2:>1
	},
	{dimIn,dimIn,dimOut}
]


(* ::Section:: *)
(*compute c contraction*)


ClearAll[memoisedSubsets]
memoisedSubsets[n_,m_]:=memoisedSubsets[n,m]=Subsets[Range[n],m](*DeleteCases[Subsets[Range[n],m],{}]*);


(* <\[Sigma]|Subscript[c, Subscript[\[ScriptL], 1]]...Subscript[c, Subscript[\[ScriptL], n]] Subscript[c, -Subscript[\[ScriptK], 1]]...Subscript[c, -Subscript[\[ScriptK], n']]|I> *)
ClearAll[cContractions]
cContractions[kTot_]:=cContractions[kTot]=Block[
	{
		basis=cBasis[kTot],
		cVecs=cBasis[kTot]//Keys,
		(*c0Factors,*)
		cVecRight,cVecLeft,mat,i,
		rules,val,idxLeft,idxRight,idxLeftP,idxRightP
	},
	(*mat=SparseArray[{(*Band[{1,1}]\[Rule]1*)},{Length[cVecs],Length[cVecs]}];*)
	mat=<||>;
	(*c0Factors=If[MemberQ[#,0],1/2,1]&/@cVecs;*)
	Do[
		cVecRight=cVecs[[j]];
		(*nc=Length[cVecRight];*)
		(*Block[{Missing=0&},
			mat[{j,j,Length[cVecRight]+1,1}]=c0Factors[[j]];
		];*)
		(*Sow[{j,j}->(-1)^nc*c0Factors[[j]] ];*)
		Do[
			cVecLeft=cVecRight;
			cVecLeft[[idxC[[Complement[idxC//Length//Range,idxCPlus]]] ]]--;
			cVecLeft[[idxC[[idxCPlus]] ]]++;
			(*{cVecLeft,cVecRight,idxC[[idxCPlus]],Complement[idxC,idxC[[idxCPlus]]]}//Print;*)
			i=basis[ -Sort[-cVecLeft] ];
			If[!MissingQ[i],
				Block[{Missing=0&},
					mat[{ i,j,Length[cVecRight]-Length[idxC]+1,Length[idxCPlus]+1}]
						+= Signature[-cVecLeft]*If[MemberQ[cVecLeft[[Complement[Range[Length[cVecRight]],idxC]]],0],1/2,1]
				]
			],
			{idxC,memoisedSubsets[Length@cVecRight,
					Length@cVecRight]   },
			{idxCPlus,memoisedSubsets[Length@idxC,Length@idxC
					(*Max[(kTot-Total[cVecRight]+Length@idxC)/2//Floor,0]*) ]   }
		],
		{j,Length[basis]}
	] ;
	
	(*rules=ArrayRules[mat][[;;-2]]//Association;*)
	(* for the ones that reduce to <Subscript[c, 0]> *)
	(*KeyValueMap[
		(
			{idxLeft,idxRight}=#1;
			val=#2;
			idxLeftP=Append[cVecs[[idxLeft]],0]//basis;
			idxRightP=Append[cVecs[[idxRight]],0]//basis;
			If[!MissingQ[idxLeftP],Block[{Missing=0&},
				mat[{ idxLeftP,idxRight}]+=(*1/Sqrt[2]*)((1-I)/2)(*\[ExponentialE]^(\[ImaginaryI] \[Phi])/Sqrt[2]*)(*\[ImaginaryI]/Sqrt[2]*)*val
			] ];
			If[!MissingQ[idxRightP],Block[{Missing=0&},
				mat[{ idxLeft,idxRightP}]+=(*1/Sqrt[2]*)((1-I)/2)(*\[ExponentialE]^(\[ImaginaryI] \[Phi]b)/Sqrt[2]*)(*\[ImaginaryI]/Sqrt[2]*)*val
			] ];
		)&,
	mat];*)
	Flatten[
		SparseArray[mat//Normal,{Length[cVecs],Length[cVecs],kTot+1,kTot+1}],
		{{1},{2},{3,4}}
	] . Flatten[tensorCommutatorProduct[kTot+1],1]
]


ClearAll[tensorCommutatorProduct]
tensorCommutatorProduct[pow_]:=tensorCommutatorProduct[pow]=SparseArray[
	{
		{i_,j_,k_}/;0<=k-j<=i-1:>(-1)^(i-1) Binomial[i-1,k-j]
	},
	{pow,pow,pow}
]


(* ::Section:: *)
(*Integrate out correlators*)


(*ClearAll[computeSigmaLCTMatrix]
computeSigmaLCTMatrix[basisFermion_,Dmax_]:=Module[
	{basisCleanUp=KeySelect[cleanUpBasis[basisFermion],EvenQ[#[[1]]]&]},
	Table[
		computeMatrixElementsAtLevel[basisCleanUp,levelL,levelR,Dmax],
		{levelL,Keys[basisCleanUp]},
		{levelR,Keys[basisCleanUp]}
	]//ArrayFlatten
]*)


ClearAll[cleanUpBasis]
cleanUpBasis[basisFermion_]:=MapIndexed[
	{#2[[2]],#2[[1]]-1}->#1&,
	basisFermion[[1]],{2}
]//Flatten//Association//DeleteCases[{}]


(*ClearAll[computeMatrixElementsAtLevel]
computeMatrixElementsAtLevel[basisCleanUp_,{nOut_,degFOut_},{nIn_,degFIn_},kTot_]/;nOut<nIn||(nOut==nIn&&degFOut<degFIn):=
	computeMatrixElementsAtLevel[basisCleanUp,{nIn,degFIn},{nOut,degFOut},kTot]//Transpose;
computeMatrixElementsAtLevel[basisCleanUp_,{nOut_,degFOut_},{nIn_,degFIn_},kTot_]:=
computeMatrixElementsAtLevel[basisCleanUp,{nOut,degFOut},{nIn,degFIn},kTot]=Module[
	{cBasisIn,cBasisOut,aBasisIn,aBasisOut,contraction,powMax,res,t0=AbsoluteTime[]},
	cBasisIn = embedInLargerCBasis[mapAInToC[nIn,degFIn],kTot];
	cBasisOut = embedInLargerCBasis[mapAOutToC[nOut,degFOut],kTot];
	aBasisIn = basisCleanUp[{nIn,degFIn}][[;;,orderFermionBasisCodeToSigmaCode[nIn,degFIn]]];
	aBasisOut = basisCleanUp[{nOut,degFOut}][[;;,orderFermionBasisCodeToSigmaCode[nOut,degFOut]]];
	powMax = kTot + 1 + Floor[Max[nOut,nIn]/2];
	contraction = PadRight[Transpose[
		Transpose[cBasisOut,{1,3,2}]
			. Transpose[cContractions[kTot],{1,3,2}]
			. Transpose[cBasisIn,{2,1,3}],
		{1,4,5,2,3}
	],{Length@cBasisOut,Length@cBasisIn,powMax,powMax,powMax}];
	contraction = Flatten[contraction,{{1},{2},{3},{4,5}}]
					. Flatten[tensorMonoProduct[powMax,powMax],1];
	contraction = Flatten[contraction,{{1},{2},{3,4}}] . Flatten[tensorCorrelatorIntegral[powMax],1];
	res = factorIntegral[nOut/2+degFOut,nIn/2+degFIn]*aBasisOut . contraction . Transpose[aBasisIn];
	Print[{{nOut,degFOut},{nIn,degFIn}},": ",AbsoluteTime[]-t0];
	res
]*)


ClearAll[computeSigmaLCTMatrix]
computeSigmaLCTMatrix[basisFermion_,Dmax_]:=Module[
	{
		basisCleanUp=KeySelect[cleanUpBasis[basisFermion],EvenQ[#[[1]]]&&#[[1]]/2+#[[2]]<=Dmax&],
		primaryMatrix,factorMatrix,mat
	},
	primaryMatrix = primaryBasisCleanUp[basisCleanUp,Dmax];
	factorMatrix = Table[factorIntegral[hl,hlp],{hl,0,Dmax},{hlp,0,Dmax}]//SparseArray;
	Flatten[
		Transpose[primaryMatrix,{1,3,2}]
			. computeMonomialMatrixElement[basisCleanUp//Keys,Dmax]
			. Transpose[primaryMatrix,{2,1,3}],
		{{1},{3},{2,4}}
	] . Flatten[factorMatrix]
]


factorIntegral[hl_,hlp_]:=factorIntegral[hl,hlp]=If[hl<1||hlp<1,0, 
	16 ((*4\[Pi]^2*)(-1)^(hl+hlp) Sqrt[Gamma[2hl]Gamma[2hlp]])/Gamma[hl+hlp-1] ];


ClearAll[tensorCorrelatorIntegral]
tensorCorrelatorIntegral[powMax_]:=tensorCorrelatorIntegral[powMax]=SparseArray[
	{
		{i_,j_}:>Abs[i-j]
	},
	{powMax,powMax}
]


ClearAll[orderFermionBasisCodeToSigmaCode]
orderFermionBasisCodeToSigmaCode[n_,deg_]:=orderFermionBasisCodeToSigmaCode[n,deg]=
	AssociationThread[monomialsFermion[n,deg],Range[Length[monomialsFermion[n,deg]]]]/@Keys[aBasis[n,deg]]


ClearAll[primaryBasisCleanUp]
primaryBasisCleanUp[basisCleanUp_,Dmax_]:=Table[Chop@ReplacePart[
		Table[0,Length[#],Length[#]],MapThread[Rule,{({#,#}&/@Range[Length[#]]),#[[;;,;;,;;,h+1]]}]
	]//ArrayFlatten,{h,0,Dmax}]&@KeyValueMap[
		TensorProduct[
			SparseArray[#2[[;;,orderFermionBasisCodeToSigmaCode@@(#1)]]],
			UnitVector[Dmax+1,#1[[1]]/2+#[[2]]+1]
		]&,
		KeySelect[basisCleanUp,EvenQ[#[[1]]]&&#[[1]]/2+#[[2]]<=Dmax&]
]//SparseArray//Transpose[#,{3,1,2}]&


(*debug[basisCleanUp_,{nOut_,degFOut_},{nIn_,degFIn_},kTot_]:=Module[
	{cBasisIn,cBasisOut,aBasisIn,aBasisOut,contraction,powMax},
	cBasisIn = embedInLargerCBasis[mapAInToC[nIn,degFIn],kTot];
	cBasisOut = embedInLargerCBasis[mapAOutToC[nOut,degFOut],kTot];
	aBasisIn = basisCleanUp[{nIn,degFIn}][[;;,orderFermionBasisCodeToSigmaCode[nIn,degFIn]]];
	aBasisOut = basisCleanUp[{nOut,degFOut}][[;;,orderFermionBasisCodeToSigmaCode[nOut,degFOut]]];
	powMax = kTot + 1 + Floor[Max[nOut,nIn]/2];
	contraction = PadRight[Transpose[
		Transpose[cBasisOut,{1,3,2}]
			.Transpose[cContractions[kTot],{1,3,2}]
			.Transpose[cBasisIn,{2,1,3}],
		{1,4,5,2,3}
	],{Length@cBasisOut,Length@cBasisIn,powMax,powMax,powMax}];
	contraction = Flatten[contraction,{{1},{2},{3},{4,5}}]
					.Flatten[tensorMonoProduct[powMax,powMax],1];
	contraction = Flatten[contraction,{{1},{2},{3,4}}].Flatten[tensorCorrelatorIntegral[powMax],1]
	(*factorIntegral[nOut/2+degFOut,nIn/2+degFIn]*aBasisOut.contraction.Transpose[aBasisIn]*)
]*)


(*ClearAll[debug2]
debug2[basisFermion_,Dmax_]:=Module[
	{basisCleanUp=KeySelect[cleanUpBasis[basisFermion],EvenQ[#[[1]]]&&#[[1]]/2+#[[2]]<=Dmax&]},
	Table[
		debug[basisCleanUp,levelL,levelR,Dmax],
		{levelL,Keys[basisCleanUp]},
		{levelR,Keys[basisCleanUp]}
	]//ArrayFlatten
]*)


(*computeMonomialMatrixElement[levels_,Dmax_]:=Module[
	{cBasisIn,cBasisOut,powMax,res,t0=AbsoluteTime[]},
	cBasisIn = embedInLargerCBasis[mapAInToC[#1,#2],Dmax]&@@@levels;
	cBasisOut = embedInLargerCBasis[mapAOutToC[#1,#2],Dmax]&@@@levels;
	powMax = Max[Dmax,Dimensions[#][[3]]-1&/@cBasisIn,Dimensions[#][[3]]-1&/@cBasisOut]+1;
	cBasisIn = Join@@(PadRight[#,ReplacePart[Dimensions[#],3->powMax]]&/@cBasisIn);
	cBasisOut = Join@@(PadRight[#,ReplacePart[Dimensions[#],3->powMax]]&/@cBasisOut);
	Flatten[
		Flatten[Transpose[
			Transpose[cBasisOut,{1,3,2}]
				.Transpose[cContractions[Dmax],{1,3,2}]
				.Transpose[cBasisIn,{2,1,3}],
			{1,4,5,2,3}
		],{{1},{2},{3},{4,5}}].Flatten[tensorMonoProduct[powMax,powMax],1],
	{{1},{2},{3,4}}].Flatten[tensorCorrelatorIntegral[powMax],1]
]*)


(*computeMonomialMatrixElement2[levels_,Dmax_]:=Module[
	{cBasisIn,cBasisOut,powMax,res,t0=AbsoluteTime[]},
	cBasisIn = embedInLargerCBasis[mapAInToC[#1,#2],Dmax]&@@@levels;
	cBasisOut = embedInLargerCBasis[mapAOutToC[#1,#2],Dmax]&@@@levels;
	powMax = Max[Dmax,Dimensions[#][[3]]-1&/@cBasisIn,Dimensions[#][[3]]-1&/@cBasisOut]+1;
	cBasisIn = Join@@(PadRight[#,ReplacePart[Dimensions[#],3->powMax]]&/@cBasisIn);
	cBasisOut = Join@@(PadRight[#,ReplacePart[Dimensions[#],3->powMax]]&/@cBasisOut);
	Flatten[
		Transpose[
			Flatten[
				Transpose[cBasisOut,{1,3,2}].cContractions[Dmax],
				{{1},{3},{2,4}}
			].Flatten[tensorMonoProduct[powMax,powMax],1],
			{1,3,2}
		].Transpose[cBasisIn,{2,1,3}],
		{{1},{3},{4,2}}
	].Flatten[tensorCorrelatorIntegral[powMax],1]
]*)


computeMonomialMatrixElement[levels_,Dmax_]:=Module[
	{cBasisIn,cBasisOut,powMax,contraction,t0=AbsoluteTime[],res},
	Print["computing in basis"];
	cBasisIn = embedInLargerCBasis[mapAInToC[#1,#2],Dmax]&@@@levels;
	Print[AbsoluteTime[]-t0];t0=AbsoluteTime[];
	Print["computing out basis"];
	cBasisOut = embedInLargerCBasis[mapAOutToC[#1,#2],Dmax]&@@@levels;
	Print[AbsoluteTime[]-t0];t0=AbsoluteTime[];
	powMax = 10+Max[Dmax,Dimensions[#][[3]]-1&/@cBasisIn,Dimensions[#][[3]]-1&/@cBasisOut]+1;
	cBasisIn = Join@@(PadRight[#,ReplacePart[Dimensions[#],3->powMax]]&/@cBasisIn)//N;
	cBasisOut = Join@@(PadRight[#,ReplacePart[Dimensions[#],3->powMax]]&/@cBasisOut)//N;
	Print["computing c contraction"];
	contraction = PadRight[#,ReplacePart[Dimensions[#],3->powMax]]&@N[cContractions[Dmax]];
	Print[AbsoluteTime[]-t0];t0=AbsoluteTime[];
	Print["computing the momentum matrix element"];
	res = Flatten[
		Flatten[
			cBasisOut . tensorMonoProduct[powMax,powMax],
			{{1},{4},{2,3}}
		] . Flatten[contraction,{{1,3},{2}}],
		{{1},{3,2}}
	] . Flatten[
		cBasisIn . tensorCorrelatorIntegral[powMax],
		{{2,3},{1}}
	];
	Print[AbsoluteTime[]-t0];
	res
]


(* ::Section:: *)
(*Spectral density of \[Sigma]*)


(*ClearAll[computeSigmaSpectralDensity]
computeSigmaSpectralDensity[basisFermion_,Dmax_]:=Module[
	{
		basisCleanUp=KeySelect[cleanUpBasis[basisFermion],EvenQ[#[[1]]]&&#[[1]]/2+#[[2]]<=Dmax&],
		primaryMatrix,primaryMatrixIn,factorMatrix,mat
	},
	primaryMatrix = primaryBasisCleanUp[basisCleanUp,Dmax];
	primaryMatrixIn = SparseArray[
		{{1,1}->1},
		{1,1}
	];
	factorMatrix = Table[factorOvlap[hl],{hl,0,Dmax}]//SparseArray;
	Flatten[
		Transpose[primaryMatrix,{1,3,2}]
			. computeMonomialSigmaSpectralDensity[basisCleanUp//Keys,Dmax]
			. Transpose[primaryMatrixIn,{2,1}],
		{{1},{3},{2}}
	] . factorMatrix
]*)


ClearAll[computeSigmaOvlap]
computeSigmaOvlap[basisFermion_,Dmax_]:=Module[
	{
		basisCleanUp=KeySelect[cleanUpBasis[basisFermion],EvenQ[#[[1]]]&&#[[1]]/2+#[[2]]<=Dmax&],
		primaryMatrix,factorVector,mat
	},
	primaryMatrix = primaryBasisCleanUp[basisCleanUp,Dmax];
	factorVector = Table[factorOvlap[hl],{hl,0,Dmax}]//SparseArray;
	(Transpose[primaryMatrix,{1,3,2}] .
		computeMonomialSigmaOvlap[basisCleanUp//Keys,Dmax]) .
		factorVector
]


ClearAll[factorOvlap]
factorOvlap[hl_]:=factorOvlap[hl]=If[hl<1,0, 
	(-1)^hl Sqrt[Gamma[2hl]]/Gamma[hl] ];


ClearAll[computeMonomialSigmaOvlap]
computeMonomialSigmaOvlap[levels_,Dmax_]:=Module[
	{cBasisOut,powMax,t0=AbsoluteTime[],res},
	(*Print["computing out basis"];*)
	Print["computing the sigma ovlap"];
	cBasisOut = embedInLargerCBasis[mapAOutToC[#1,#2],Dmax]&@@@levels;
	res = Join@@(#[[;;,1,1]]&/@cBasisOut);
	Print[AbsoluteTime[]-t0];
	res
]


(*computeMonomialSigmaSpectralDensity[levels_,Dmax_]:=Module[
	{cBasisIn,cBasisOut,powMax,oneVector,contraction,t0=AbsoluteTime[],res},
	Print["computing in basis"];
	cBasisIn = embedInLargerCBasis[mapAInToC[#1,#2],Dmax]&@@@{{0,0}};
	Print[AbsoluteTime[]-t0];t0=AbsoluteTime[];
	Print["computing out basis"];
	cBasisOut = embedInLargerCBasis[mapAOutToC[#1,#2],Dmax]&@@@levels;
	Print[AbsoluteTime[]-t0];t0=AbsoluteTime[];
	powMax = 10+Max[Dmax,Dimensions[#][[3]]-1&/@cBasisIn,Dimensions[#][[3]]-1&/@cBasisOut]+1;
	cBasisIn = Join@@(PadRight[#,ReplacePart[Dimensions[#],3->powMax]]&/@cBasisIn)//N;
	cBasisOut = Join@@(PadRight[#,ReplacePart[Dimensions[#],3->powMax]]&/@cBasisOut)//N;
	Print["computing c contraction"];
	contraction = PadRight[#,ReplacePart[Dimensions[#],3->powMax]]&@N[cContractions[Dmax]];
	Print[AbsoluteTime[]-t0];t0=AbsoluteTime[];
	Print["computing the momentum spectral density"];
	oneVector = Table[1,powMax]//SparseArray;
	(*oneVector//Dimensions//Print;
	cBasisOut//Dimensions//Print;
	contraction//Dimensions//Print;
	cBasisIn//Dimensions//Print;*)
	res = (cBasisOut . oneVector) . (contraction . oneVector) . Transpose[cBasisIn . oneVector];
	Print[AbsoluteTime[]-t0];
	res
]*)


(*ClearAll[tensorSpectralDensityFromPow]
tensorSpectralDensityFromPow[powMax_]:=tensorSpectralDensityFromPow[powMax]=SparseArray[
	{
		{i_,j_}:>1
	},
	{powMax,powMax}
]*)
