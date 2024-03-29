(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: FMCartesianSchoutenBruteForce2															*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2023 Vladyslav Shtabovenko
*)

(* :Summary:	Applies Schouten's identity									*)

(* ------------------------------------------------------------------------ *)


FMCartesianSchoutenBruteForce2::usage =
"FMCartesianSchoutenBruteForce2[expr] applies 3D Schouten identity repetedly to simplify
the given expression as soons as possible.";
AllowZeroGain::usage ="";
Begin["`Package`"]
End[]

Begin["`FMCartesianSchoutenBruteForce2`Private`"]

Options[FMCartesianSchoutenBruteForce2] = {
	FCI 			-> False,
	Expand			-> True,
	Collect			-> True,
	Head			-> None,
	AllowZeroGain	-> False,
	Except			-> {}
};

checkSchouten[x_, repRule_]:=
Block[{lenBefore,lenAfter,resBefore,resAfter},
	resBefore = x;
	lenBefore = Length[resBefore];
	resAfter = ExpandAll[
		FMCartesianSchouten2[x/. CartesianPair[a__]^z_ :> CartesianPair[a] pow[CartesianPair[a],z-1],repRule[[2]]] /. pow -> Power ];
	lenAfter = Length[resAfter];

	If[ Simplify[resBefore-resAfter]===0,
		0,
		lenBefore-lenAfter
	]
];

FMCartesianSchoutenBruteForce2[expr_, vars_List, OptionsPattern[]] :=
	Block[{ex, res,pat,head, sublists, combos, maxRed = 3, cs, gain=0,repRule,list},
		If[	OptionValue[FCI],
			ex = expr,
			ex = FCI[expr]
		];

		If[	FreeQ[ex,CartesianPair],
			Return[ex]
		];

		ex = Expand[ex];

		sublists = Subsets[vars, {8}];

		sublists = Permutations[#, {8}] & /@ sublists;

		sublists = Flatten[sublists, 1];

		combos = {
		(CartesianPair[CartesianMomentum[#[[1]]], CartesianMomentum[#[[2]]]]*
		CartesianPair[CartesianMomentum[#[[3]]], CartesianMomentum[#[[4]]]]*
		CartesianPair[CartesianMomentum[#[[5]]], CartesianMomentum[#[[6]]]]*
		CartesianPair[CartesianMomentum[#[[7]]], CartesianMomentum[#[[8]]]]), #} & /@ sublists;

		combos = Union[combos, SameTest -> (#1[[1]] === #2[[1]] &)] /. {0, _} -> Unevaluated[Sequence[]];

		combos = Union[combos] /. {0,_} -> Unevaluated[Sequence[]];

		combos  = combos /.{x_,_}/;FreeQ[ex,x] :>  Unevaluated[Sequence[]];

		Print["Length before except ", Length[combos]];

		combos = If[	MemberQ[OptionValue[Except],#[[2]]],
			Unevaluated@Sequence[],
			{#[[1]],#[[2]]}
		]& /@ combos;

		Print["Length after except ", Length[combos]];

		(*combos = If[ MatchQ[#[[1]], -1 * z1_CartesianPair z2_CartesianPair z3_CartesianPair z4_CartesianPair],
			{Expand[-1*#[[1]]],Expand[-1*#[[2]]]},
			{#[[1]],#[[2]]}
		]& /@ combos;*)

		list = Catch[
			Map[(cs = checkSchouten[ex,#];
				If[cs < maxRed, {cs, #}, Throw[{cs, #}]]) &, combos]
		];

		If[MatchQ[list,{_Integer,{_,_}}],
			list={list};
		];

		list = Sort[list, (#1[[1]] > #2[[1]]) &];

		repRule = {{},{}};
		gain=0;
		If[Length[list]=!=0 && First[list][[1]]>=0,

			If[OptionValue[AllowZeroGain],
				If[Length[list]=!=0 && First[list][[1]]>=0,
					repRule = First[list][[2]];
					gain = First[list][[1]];
					ex = FMCartesianSchouten2[ex,repRule[[2]]]
				],

				If[Length[list]=!=0 && First[list][[1]]>0,
					repRule = First[list][[2]];
					gain = First[list][[1]];
					ex = FMCartesianSchouten2[ex,repRule[[2]]]
				]


			]
		];

		Print["Gain: ", gain, "; Combo: ", repRule[[2]]];

		res = ex;

		res
];


FCPrint[1,"FMCartesianSchoutenBruteForce2 loaded."];
End[]
