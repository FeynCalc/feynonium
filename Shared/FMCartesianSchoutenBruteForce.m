(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: FMCartesianSchoutenBruteForce															*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2017 Vladyslav Shtabovenko
*)

(* :Summary:	Applies Schouten identity									*)

(* ------------------------------------------------------------------------ *)


FMCartesianSchoutenBruteForce::usage =
"FMCartesianSchoutenBruteForce[expr] applies 3D Schouten identity repetedly to simplify
the given expression as soons as possible.";

Begin["`Package`"]
End[]

Begin["`FMCartesianSchoutenBruteForce`Private`"]
fmcsbv::usage="";

Options[FMCartesianSchoutenBruteForce] = {
	FCI -> False,
	Expand -> True,
	Collect -> True,
	EpsEvaluate -> True,
	Head -> None,
	Factoring -> Identity,
	FCVerbose -> 0
};

checkSchouten[x_, repRule_]:=
Block[{lenBefore,lenAfter, expr},
	lenBefore = Length[x];
	expr = x /. CartesianPair[a__]^z_ :> CartesianPair[a] pow[CartesianPair[a],z-1];
	FCPrint[3, "FMCartesianSchoutenBruteForce: checkSchouten: expr ", expr, FCDoControl->fmcsbv];
	FCPrint[3, "FMCartesianSchoutenBruteForce: checkSchouten: repRule ", repRule, FCDoControl->fmcsbv];
	lenAfter = Length[Expand[expr  /. repRule[[1]] :> repRule[[2]]] /. pow -> Power ];
	lenBefore-lenAfter
];

FMCartesianSchoutenBruteForce[expr_, vars_List, OptionsPattern[]] :=
	Block[{ex, res,pat,head, sublists, combos, maxRed = 3, cs, gain=0,
		repRule,list,factfun},

		If[	OptionValue[FCVerbose]===False,
			fmcsbv=$VeryVerbose,
			If[MatchQ[OptionValue[FCVerbose], _Integer | 0],
				fmcsbv=OptionValue[FCVerbose]
			];
		];

		If[	OptionValue[FCI],
			ex = expr,
			ex = FCI[expr]
		];

		FCPrint[1, "FMCartesianSchoutenBruteForce. Entering.", FCDoControl->fmcsbv];
		FCPrint[3, "FMCartesianSchoutenBruteForce: Entering with ", ex, FCDoControl->fmcsbv];

		If[	FreeQ[ex,Eps],
			Return[ex]
		];

		factfun=OptionValue[Factoring];
		ex = Expand[EpsEvaluate[ex]];

		sublists = Subsets[vars, {5}];

		sublists = Permutations[#,{5}]& /@ sublists;

		sublists = Flatten[sublists,1];

		FCPrint[3, "FMCartesianSchoutenBruteForce: sublists: ", sublists, FCDoControl->fmcsbv];

		combos = {Eps[CartesianMomentum[#[[1]]], CartesianMomentum[#[[2]]],
			CartesianMomentum[#[[3]]]] CartesianPair[CartesianMomentum[#[[4]]], CartesianMomentum[#[[5]]]],

			Eps[CartesianMomentum[#[[2]]], CartesianMomentum[#[[3]]], CartesianMomentum[#[[4]]]] CartesianPair[
				CartesianMomentum[#[[1]]], CartesianMomentum[#[[5]]]] -

			Eps[CartesianMomentum[#[[3]]], CartesianMomentum[#[[4]]], CartesianMomentum[#[[1]]]] CartesianPair[
				CartesianMomentum[#[[2]]], CartesianMomentum[#[[5]]]] +

			Eps[CartesianMomentum[#[[4]]], CartesianMomentum[#[[1]]], CartesianMomentum[#[[2]]]] CartesianPair[
				CartesianMomentum[#[[3]]], CartesianMomentum[#[[5]]]]}&/@ sublists;


		FCPrint[4, "FMCartesianSchoutenBruteForce: combos ", combos, FCDoControl->fmcsbv];

		combos = {EpsEvaluate[#[[1]]],EpsEvaluate[#[[2]]]}&/@ combos;

		FCPrint[4, "FMCartesianSchoutenBruteForce: combos after EpsEvaluate: ", combos, FCDoControl->fmcsbv];

		combos = If[ MatchQ[#[[1]], -1 * _Eps _CartesianPair | -1 * _Eps],
			{Expand[-1*#[[1]]],Expand[-1*#[[2]]]},
			{#[[1]],#[[2]]}
		]& /@ combos;

		FCPrint[4, "FMCartesianSchoutenBruteForce: combos after sign adjustments: ", combos, FCDoControl->fmcsbv];

		combos = Union[combos] /. {0,_}|{a_,a_} -> Unevaluated[Sequence[]];

		FCPrint[3, "FMCartesianSchoutenBruteForce: final combos: ", combos, FCDoControl->fmcsbv];

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

		FCPrint[0, "FMCartesianSchoutenBruteForce: ", gain, " terms were removed using ", {repRule[[1]] -> repRule[[2]]}, " ", FCDoControl->fmcsbv];

		res = ex;

		res
];


FCPrint[1,"FMCartesianSchoutenBruteForce loaded."];
End[]
