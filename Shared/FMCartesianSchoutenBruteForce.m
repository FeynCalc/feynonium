(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: FMCartesianSchoutenBruteForce															*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2016 Vladyslav Shtabovenko
*)

(* :Summary:	Applies Schouten identity									*)

(* ------------------------------------------------------------------------ *)


FMCartesianSchoutenBruteForce::usage =
"FMCartesianSchoutenBruteForce[expr] applies 3D Schouten identity repetedly to simplify
the given expression as soons as possible.";

Begin["`Package`"]
End[]

Begin["`FMCartesianSchoutenBruteForce`Private`"]

Options[FMCartesianSchoutenBruteForce] = {
	FCI -> False,
	Expand -> True,
	Collect -> True,
	EpsEvaluate -> True,
	Head -> None,
	Factoring -> Identity
};

checkSchouten[x_, repRule_]:=
Block[{lenBefore,lenAfter},
	lenBefore = Length[x];
	lenAfter = Length[Expand[x /. CPair[a__]^z_ :> CPair[a] pow[CPair,z-1]  /. repRule[[1]] :> repRule[[2]]] /. pow -> Power ];
	lenBefore-lenAfter
];

FMCartesianSchoutenBruteForce[expr_, vars_List, OptionsPattern[]] :=
	Block[{ex, res,pat,head, sublists, combos, maxRed = 3, cs, gain=0,
		repRule,list,factfun},
		If[	OptionValue[FCI],
			ex = expr,
			ex = FCI[expr]
		];

		If[	FreeQ[ex,Eps],
			Return[ex]
		];

		factfun=OptionValue[Factoring];
		ex = Expand[EpsEvaluate[ex]];

		sublists = Subsets[vars, {5}];

		(*sublists = {
			{#[[1]],#[[2]],#[[3]],#[[4]],#[[5]]},
			{#[[1]],#[[2]],#[[4]],#[[3]],#[[5]]},
			{#[[1]],#[[2]],#[[5]],#[[3]],#[[4]]},
			{#[[1]],#[[3]],#[[4]],#[[2]],#[[5]]},
			{#[[1]],#[[3]],#[[5]],#[[2]],#[[4]]},
			{#[[1]],#[[4]],#[[5]],#[[2]],#[[3]]},
			{#[[2]],#[[3]],#[[4]],#[[1]],#[[5]]},
			{#[[2]],#[[3]],#[[5]],#[[1]],#[[4]]},
			{#[[2]],#[[4]],#[[5]],#[[1]],#[[3]]},
			{#[[3]],#[[4]],#[[5]],#[[1]],#[[2]]}
		}& /@ sublists;*)

		sublists = Permutations[#,{5}]& /@ sublists;

		sublists = Flatten[sublists,1];

		combos = {Eps[CMomentum[#[[1]]], CMomentum[#[[2]]],
			CMomentum[#[[3]]]] CPair[CMomentum[#[[4]]], CMomentum[#[[5]]]],

			Eps[CMomentum[#[[2]]], CMomentum[#[[3]]], CMomentum[#[[4]]]] CPair[
				CMomentum[#[[1]]], CMomentum[#[[5]]]] -

			Eps[CMomentum[#[[3]]], CMomentum[#[[4]]], CMomentum[#[[1]]]] CPair[
				CMomentum[#[[2]]], CMomentum[#[[5]]]] +

			Eps[CMomentum[#[[4]]], CMomentum[#[[1]]], CMomentum[#[[2]]]] CPair[
				CMomentum[#[[3]]], CMomentum[#[[5]]]]}&/@ sublists;


		combos = {EpsEvaluate[#[[1]]],EpsEvaluate[#[[2]]]}&/@ combos;

		combos = If[ MatchQ[#[[1]], -1 * _Eps _CPair],
			{Expand[-1*#[[1]]],Expand[-1*#[[2]]]},
			{#[[1]],#[[2]]}
		]& /@ combos;

		combos = Union[combos] /. {0,_} -> Unevaluated[Sequence[]];

		list = Catch[
			Map[(cs = checkSchouten[ex,#];
				If[cs < maxRed, {cs, #}, Throw[{cs, #}]]) &, combos]
		];

		If[MatchQ[list,{_Integer,{_,_}}],
			list={list};
		];

		list = Sort[list, (#1[[1]] > #2[[1]]) &];


		repRule = {{},{}};
		If[Length[list]=!=0 && First[list][[1]]>0,
			repRule = First[list][[2]];
			gain = First[list][[1]];
			ex = ex /. repRule[[1]] :> repRule[[2]]
		];

		Print["Gain: ", gain, "; Combo: ", repRule[[2]]];

		res = ex;

		res
];


FCPrint[1,"FMCartesianSchoutenBruteForce loaded."];
End[]
