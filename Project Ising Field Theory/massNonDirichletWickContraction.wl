(* ::Package:: *)

(* ::Section:: *)
(*Fermion Mass term*)


(* ::Subsection:: *)
(*Clean up basis levels *)


ClearAll[cleanUpBasis]
cleanUpBasis[basisFermion_]:=MapIndexed[
{#2[[2]],#2[[1]]-1}->#1&,
basisFermion[[1]],{2}
]//Flatten//Association//DeleteCases[{}]


(* ::Subsection:: *)
(*Monomial contraction*)


ClearAll[AF]
AF[{}, {}] = 1;
AF[\[Lambda]1_List, \[Lambda]2_List(*/;Length@\[Lambda]2>=2*)] := 
AF[\[Lambda]1, \[Lambda]2] = Block[{n = Length[\[Lambda]2], num}, Sum[
	(-1)^(n - i)*
	(*(-1)^(i-1)**)
	Gamma[\[Lambda]1[[1]] + \[Lambda]2[[i]] + 1] AF[Drop[\[Lambda]1, {1}], Drop[\[Lambda]2, {i}]], 
	{i, Range[n] }]
];


ClearAll[massFRegulated]
massFRegulated[k_, kp_] := massFRegulated[k, kp]=
With[{n = Length[k]}, Sum[
	If[k[[i]]==0&&kp[[j]]==0,0,
		(*(-1)^(n - 1 - i - j)*)
		(-1)^(i-j) Gamma[k[[i]] + kp[[j]]]*
		AF[Drop[k, {i}], Drop[kp, {j}]]
	],
	{i, Range[n]}, {j, Range[n]}
] ]


ClearAll[massFND]
massFND[k_, kp_] := massFND[k, kp] = 
With[{n = Length[k]}, Sum[
	If[k[[i]]==0&&kp[[j]]==0,
		(*(-1)^(n - 1 - i - j)*)
		(-1)^(i-j) AF[Drop[k, {i}], Drop[kp, {j}]],
		0
	],
	{i, Range[n]}, {j, Range[n]}
] ]


(* ::Subsection:: *)
(*monomial matrices*)


ClearAll[matFMR]
matFMR[n_,deg1_,deg2_]/;deg1>=deg2:=Module[
{basis1,basis2},
Outer[
massFRegulated[#1,#2]&,
monomialsFermion[n,deg1],
monomialsFermion[n,deg2],1
]

];
matFMR[n_,deg1_,deg2_]/;deg1<deg2:=matFMR[n,deg2,deg1]//Transpose;


ClearAll[matFMND]
matFMND[n_,deg1_,deg2_]/;deg1>=deg2:=Module[
{basis1,basis2},
Outer[
massFND[#1,#2]&,
monomialsFermion[n,deg1],
monomialsFermion[n,deg2],1
]

];
matFMND[n_,deg1_,deg2_]/;deg1<deg2:=matFMND[n,deg2,deg1]//Transpose;


(* ::Subsection:: *)
(*Primary matrices*)


ClearAll[computeMassRegulated]
computeMassRegulated[basisFermionEmptyFree_]:=Module[
{
nCases,basisN,degCases,\[CapitalDelta]1,\[CapitalDelta]2
},
nCases=Keys[basisFermionEmptyFree][[;;,1]]//Union;
Table[
Print["@n = ",n];
basisN=KeySort@KeySelect[basisFermionEmptyFree,#[[1]]==n&];
basisN=KeyValueMap[
#1->#2 . DiagonalMatrix[1/factorFermion/@(monomialsFermion@@#1)]&,
basisN
]//Association;
degCases=Keys[basisN][[;;,2]];
-Signature[Range[n]//Reverse]*Table[
\[CapitalDelta]1=deg1+n/2;\[CapitalDelta]2=deg2+n/2;
basisN[{n,deg1}] . matFMR[n,deg1,deg2] . Transpose[basisN[{n,deg2}]]*
Sqrt[Gamma[2\[CapitalDelta]1]Gamma[2\[CapitalDelta]2]]/Gamma[\[CapitalDelta]1+\[CapitalDelta]2-1],
{deg1,degCases},{deg2,degCases}
]//ArrayFlatten,
{n,Select[nCases,EvenQ]}
]

]


ClearAll[computeMassNDFinite]
computeMassNDFinite[basisFermionEmptyFree_]:=Module[
{
nCases,basisN,degCases,\[CapitalDelta]1,\[CapitalDelta]2
},
nCases=Keys[basisFermionEmptyFree][[;;,1]]//Union;
Table[
Print["@n = ",n];
basisN=KeySort@KeySelect[basisFermionEmptyFree,#[[1]]==n&];
basisN=KeyValueMap[
#1->#2 . DiagonalMatrix[1/factorFermion/@(monomialsFermion@@#1)]&,
basisN
]//Association;
degCases=Keys[basisN][[;;,2]];
-Signature[Range[n]//Reverse]*Table[
\[CapitalDelta]1=deg1+n/2;\[CapitalDelta]2=deg2+n/2;
basisN[{n,deg1}] . matFMND[n,deg1,deg2] . Transpose[basisN[{n,deg2}]]*
(-HarmonicNumber[\[CapitalDelta]1+ \[CapitalDelta]2 - 2])*
Sqrt[Gamma[2\[CapitalDelta]1]Gamma[2\[CapitalDelta]2]]/Gamma[\[CapitalDelta]1+\[CapitalDelta]2-1],
{deg1,degCases},{deg2,degCases}
]//ArrayFlatten,
{n,Select[nCases,EvenQ]}
]

]


ClearAll[computeMassNDSingular]
computeMassNDSingular[basisFermionEmptyFree_]:=Module[
{
nCases,basisN,degCases,\[CapitalDelta]1,\[CapitalDelta]2
},
nCases=Keys[basisFermionEmptyFree][[;;,1]]//Union;
Table[
Print["@n = ",n];
basisN=KeySort@KeySelect[basisFermionEmptyFree,#[[1]]==n&];
basisN=KeyValueMap[
#1->#2 . DiagonalMatrix[1/factorFermion/@(monomialsFermion@@#1)]&,
basisN
]//Association;
degCases=Keys[basisN][[;;,2]];
Signature[Range[n]//Reverse]*Table[
\[CapitalDelta]1=deg1+n/2;\[CapitalDelta]2=deg2+n/2;
basisN[{n,deg1}] . matFMND[n,deg1,deg2] . Transpose[basisN[{n,deg2}]]*
(-1)
Sqrt[Gamma[2\[CapitalDelta]1]Gamma[2\[CapitalDelta]2]]/Gamma[\[CapitalDelta]1+\[CapitalDelta]2-1],
{deg1,degCases},{deg2,degCases}
]//ArrayFlatten,
{n,Select[nCases,EvenQ]}
]

]


(* ::Subsection:: *)
(*assemble whole matrix*)


ClearAll[computeMassMatrices]
computeMassMatrices[basisFermionEmptyFree_]:=Module[
{matRegulated,matNDSingular},
matRegulated=computeMassRegulated[basisFermionEmptyFree]+computeMassNDFinite[basisFermionEmptyFree]//BlockDiagonalMatrix;
matNDSingular=computeMassNDSingular[basisFermionEmptyFree]//BlockDiagonalMatrix;
<|"massFinite"->matRegulated,"massSingular"->matNDSingular|>
]
