(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: FMCartesianSchouten2															*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2016 Vladyslav Shtabovenko
*)

(* :Summary:	Applies Schouten identity									*)

(* ------------------------------------------------------------------------ *)


FMCartesianSchouten2::usage =
"FMCartesianSchouten2[expr] applies Schouten identity to the given combination of C-tensors";

FMCartesianSchouten2::notpresent =
"Warning! The Structure `1` doesn't appear in the expression!"

Begin["`Package`"]
End[]

Begin["`FMCartesianSchouten2`Private`"]

Options[FMCartesianSchouten2] = {
	FCI -> False,
	Expand -> True,
	Collect -> True,
	Head -> None
};

FMCartesianSchouten2[expr_, {a1_,b1_,a2_,b2_,a3_,b3_,a4_,a5_}, OptionsPattern[]] :=
	Block[{ex, res,pat,head, input},
		If[	OptionValue[FCI],
			ex = expr,
			ex = FCI[expr]
		];

		input =
			CPair[CMomentum[a1], CMomentum[b1]] CPair[CMomentum[a2], CMomentum[b2]] *
			CPair[CMomentum[a3], CMomentum[b3]] CPair[CMomentum[a4], CMomentum[a5]];

		If[	OptionValue[Expand],
			ex = Expand2[expr, {CPair}]
		];

		If[	FreeQ[ex, input],
			Message[FMCartesianSchouten2::notpresent,ToString[input,InputForm]]
		];



		res =
			ex /. {input :>

				((

				CPair[CMomentum[a1], CMomentum[b1]] CPair[CMomentum[a2],
		CMomentum[b3]] CPair[CMomentum[a3], CMomentum[b2]] CPair[
		CMomentum[a4], CMomentum[a5]] -
		CPair[CMomentum[a1], CMomentum[a5]] CPair[CMomentum[a2],
		CMomentum[b3]] CPair[CMomentum[a3], CMomentum[b2]] CPair[
		CMomentum[a4], CMomentum[b1]] +
		CPair[CMomentum[a1], CMomentum[a5]] CPair[CMomentum[a2],
		CMomentum[b2]] CPair[CMomentum[a3], CMomentum[b3]] CPair[
		CMomentum[a4], CMomentum[b1]] -
		CPair[CMomentum[a1], CMomentum[b1]] CPair[CMomentum[a2],
		CMomentum[b3]] CPair[CMomentum[a3], CMomentum[a5]] CPair[
		CMomentum[a4], CMomentum[b2]] +
		CPair[CMomentum[a1], CMomentum[a5]] CPair[CMomentum[a2],
		CMomentum[b3]] CPair[CMomentum[a3], CMomentum[b1]] CPair[
		CMomentum[a4], CMomentum[b2]] +
		CPair[CMomentum[a1], CMomentum[b1]] CPair[CMomentum[a2],
		CMomentum[a5]] CPair[CMomentum[a3], CMomentum[b3]] CPair[
		CMomentum[a4], CMomentum[b2]] -
		CPair[CMomentum[a1], CMomentum[a5]] CPair[CMomentum[a2],
		CMomentum[b1]] CPair[CMomentum[a3], CMomentum[b3]] CPair[
		CMomentum[a4], CMomentum[b2]] +
		CPair[CMomentum[a1],
		CMomentum[
			b3]] (CPair[CMomentum[a2],
			CMomentum[
			b2]] (CPair[CMomentum[a3], CMomentum[b1]] CPair[CMomentum[a4],
				CMomentum[a5]] -
			CPair[CMomentum[a3], CMomentum[a5]] CPair[CMomentum[a4],
				CMomentum[b1]]) +
			CPair[CMomentum[a2],
			CMomentum[
			b1]] (-CPair[CMomentum[a3], CMomentum[b2]] CPair[CMomentum[a4],
				CMomentum[a5]] +
			CPair[CMomentum[a3], CMomentum[a5]] CPair[CMomentum[a4],
				CMomentum[b2]]) +
			CPair[CMomentum[a2],
			CMomentum[
			a5]] (CPair[CMomentum[a3], CMomentum[b2]] CPair[CMomentum[a4],
				CMomentum[b1]] -
			CPair[CMomentum[a3], CMomentum[b1]] CPair[CMomentum[a4],
				CMomentum[b2]])) +
		CPair[CMomentum[a1], CMomentum[b1]] CPair[CMomentum[a2],
		CMomentum[b2]] CPair[CMomentum[a3], CMomentum[a5]] CPair[
		CMomentum[a4], CMomentum[b3]] -
		CPair[CMomentum[a1], CMomentum[a5]] CPair[CMomentum[a2],
		CMomentum[b2]] CPair[CMomentum[a3], CMomentum[b1]] CPair[
		CMomentum[a4], CMomentum[b3]] -
		CPair[CMomentum[a1], CMomentum[b1]] CPair[CMomentum[a2],
		CMomentum[a5]] CPair[CMomentum[a3], CMomentum[b2]] CPair[
		CMomentum[a4], CMomentum[b3]] +
		CPair[CMomentum[a1], CMomentum[a5]] CPair[CMomentum[a2],
		CMomentum[b1]] CPair[CMomentum[a3], CMomentum[b2]] CPair[
		CMomentum[a4], CMomentum[b3]] +
		CPair[CMomentum[a1],
		CMomentum[b2]] (CPair[CMomentum[a2],CMomentum[b3]] (-CPair[CMomentum[a3], CMomentum[b1]] CPair[CMomentum[a4],
				CMomentum[a5]] +
			CPair[CMomentum[a3], CMomentum[a5]] CPair[CMomentum[a4],
				CMomentum[b1]]) +
			CPair[CMomentum[a2],
			CMomentum[
			b1]] (CPair[CMomentum[a3], CMomentum[b3]] CPair[CMomentum[a4],
				CMomentum[a5]] -
			CPair[CMomentum[a3], CMomentum[a5]] CPair[CMomentum[a4],
				CMomentum[b3]]) +
			CPair[CMomentum[a2],
			CMomentum[
			a5]] (-CPair[CMomentum[a3], CMomentum[b3]] CPair[CMomentum[a4],
				CMomentum[b1]] +
			CPair[CMomentum[a3], CMomentum[b1]] CPair[CMomentum[a4],
				CMomentum[b3]]))

				)/. Pattern -> pat /. pat[a_,___]:>a)
				};

		If[ Length[Cases2[res/.head[_,0]:>0,head]]===1,
			Print["Warning! The replacement of ",
			input, " failed!" ]
		];

		If[ OptionValue[Head]=!=None,
			res = res /. head -> OptionValue[Head],
			res = res /. head[_,x_]:>x
		];

		If[	OptionValue[Collect],
			res = Collect2[res, {CPair}]
		];

		res
];


FCPrint[1,"FMCartesianSchouten2 loaded."];
End[]
