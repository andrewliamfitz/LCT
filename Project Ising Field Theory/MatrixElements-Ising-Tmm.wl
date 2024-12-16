(* ::Package:: *)

(* ::Section:: *)
(*Virasoro Basis*)


cIsing=1/2;
ClearAll[inner];
inner[{_?Negative,z___}]=0;
inner[{x___,_?NonNegative}]=0;
inner[{}]=1;
inner[{x___,y1_,y2_,z___}]/;y1>y2:=inner[{x,y1,y2,z}]=inner[{x,y2,y1,z}]+If[
y1+y2==0,(2y1*(-Plus[z]+(*hSig*)0)+cIsing/12 (y1^3-y1))inner[{x,z}],
(y1-y2)*inner[{x,(y1+y2),z}]
];


nullLevels[Dmax_]:=Module[
	{c=1/2,p=3,r=1,s=1,E0,series,nCut,factors,level,degmax,leadingExp},
	(* Shifting away the ground level *)
	E0=((p r - (p + 1) s)^2 - 1)/(4 p (p + 1)) - (c-1)/24;
	(* An estimate of the max n in the character q expansion. *)
	nCut=Max[
		Ceiling[(
			2 Sqrt[p (1 + p)] Sqrt[p^2 (1 + p)^2 (10 Dmax + E0)] + 
			p (1 + p) (s + p (-r + s)))/(2 p^2 (1 + p)^2) // Abs],
		Ceiling[-((
			2 Sqrt[p (1 + p)] Sqrt[p^2 (1 + p)^2 (10 Dmax + E0)] + 
			p (1 + p) (s + p (r + s)))/(2 p^2 (1 + p)^2)) // Abs]
	];
	series=Sum[
		q^((2p (p+1) n +p r-(p+1) s)^2/(4p (p+1))-E0)
		- q^((2p (p+1) n +p r+(p+1) s)^2/(4p (p+1))-E0),
	{n,-nCut,nCut}];
	level=0;
	factors=1;
	Reap[While[level<=Dmax,
		Sow[level=Exponent[series-factors,q,List]//Min];
		factors=factors*(1-q^level);
	]][[2,1]]
]


ClearAll[monomialsMinimal]
monomialsMinimal[deg_,Dmax_]:=monomialsMinimal[deg,Dmax]=Select[
	IntegerPartitions[deg],
	FreeQ[#,Alternatives@@nullLevels[Dmax]]&
]


loadGramMatrixDmax[Dmax_]:=Module[
{},
	gram=<||>;
	Do[
		gram[deg]=Table[
			If[j<=i,(* only compute the lower triangle *)
				inner[ Flatten[{
					Reverse[ monomialsMinimal[deg,Dmax][[i]] ],
					-monomialsMinimal[deg,Dmax][[j]]
				}] ],
				(*else*)0
			],
			{i,Length[monomialsMinimal[deg,Dmax]]},
			{j,Length[monomialsMinimal[deg,Dmax]]}
		];
		(* copy lower triangle to upper triangle *)
		gram[deg]=gram[deg]+Transpose[gram[deg]]-DiagonalMatrix[Diagonal[gram[deg]]],
		{deg,2,Dmax}
	]
]


loadQuasiPrimaryDmax[Dmax_,prec_]:=Module[
	{LPlusOneMat,nsp},
	quasiPrimaries=<||>;
	Do[
		LPlusOneMat=Table[
			inner[ Flatten[{
				Reverse[ monomialsMinimal[deg-1,Dmax][[i]] ],{+1},
				-monomialsMinimal[deg,Dmax][[j]]
			}] ],
			{i,Length[monomialsMinimal[deg-1,Dmax]]},
			{j,Length[monomialsMinimal[deg,Dmax]]}
		];
		(* If there is no lower states for L_{+1} action to lower
		to, then every state in this level is quasiprimary *)
		If[Length[monomialsMinimal[deg-1,Dmax]]==0,
			nsp=IdentityMatrix[Length[monomialsMinimal[deg,Dmax]]],
			nsp=NullSpace[LPlusOneMat]
		];
		quasiPrimaries[deg]=Orthogonalize[
			nsp,
			(* Too expensive to keep all sqrts. Orthogonalize with
			finite but higher precision. *)
			#1 . N[gram[deg],prec] . #2&
		]
		,
		{deg,2,Dmax}
	]
]


(* ::Section:: *)
(*Tmm*)


computeFullTmm[degMax_]:=Monitor[Module[
{statesL,statesR,primL,primR},
quasiPrimariesNonZeroKeys=Select[quasiPrimaries,Length[#]>0&]//Keys;
Table[
statesL=monomialsMinimal[degL,degMax];
statesR=monomialsMinimal[degR,degMax];
primL=quasiPrimaries[degL];
primR=quasiPrimaries[degR];
primL . Table[
(*matElemMono[stateL,stateR]*)
inner[ Join[Reverse[stateL],{degR-degL},(-stateR)] ],
{stateL,statesL},
{stateR,statesR}
] . Transpose[primR]

,
{degL,Select[quasiPrimariesNonZeroKeys,#<=degMax&]},
{degR,Select[quasiPrimariesNonZeroKeys,#<=degMax&]}
]
],{degL,degR,stateL,stateR}];


computeFullTmmMonomial[degMax_]:=Monitor[Module[
{statesL,statesR,primL,primR},
quasiPrimariesNonZeroKeys=Select[quasiPrimaries,Length[#]>0&]//Keys;
Table[
statesL=monomialsMinimal[degL,degMax];
statesR=monomialsMinimal[degR,degMax];
Table[
(*matElemMono[stateL,stateR]*)
inner[ Join[Reverse[stateL],{degR-degL},(-stateR)] ],
{stateL,statesL},
{stateR,statesR}
]

,
{degL,Select[quasiPrimariesNonZeroKeys,#<=degMax&]},
{degR,Select[quasiPrimariesNonZeroKeys,#<=degMax&]}
]
],{degL,degR,stateL,stateR}];
