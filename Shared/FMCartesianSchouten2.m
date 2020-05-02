(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: FMCartesianSchouten2															*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2020 Vladyslav Shtabovenko
*)

(* :Summary:	Applies Schouten's identity									*)

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
			CartesianPair[CartesianMomentum[a1], CartesianMomentum[b1]] CartesianPair[CartesianMomentum[a2], CartesianMomentum[b2]] *
			CartesianPair[CartesianMomentum[a3], CartesianMomentum[b3]] CartesianPair[CartesianMomentum[a4], CartesianMomentum[a5]];

		If[	OptionValue[Expand],
			ex = Expand2[expr, {CartesianPair}]
		];

		If[	FreeQ[ex, input],
			Message[FMCartesianSchouten2::notpresent,ToString[input,InputForm]]
		];



		res =
			ex /. {input :>

				((

				CartesianPair[CartesianMomentum[a1], CartesianMomentum[b1]] CartesianPair[CartesianMomentum[a2],
		CartesianMomentum[b3]] CartesianPair[CartesianMomentum[a3], CartesianMomentum[b2]] CartesianPair[
		CartesianMomentum[a4], CartesianMomentum[a5]] -
		CartesianPair[CartesianMomentum[a1], CartesianMomentum[a5]] CartesianPair[CartesianMomentum[a2],
		CartesianMomentum[b3]] CartesianPair[CartesianMomentum[a3], CartesianMomentum[b2]] CartesianPair[
		CartesianMomentum[a4], CartesianMomentum[b1]] +
		CartesianPair[CartesianMomentum[a1], CartesianMomentum[a5]] CartesianPair[CartesianMomentum[a2],
		CartesianMomentum[b2]] CartesianPair[CartesianMomentum[a3], CartesianMomentum[b3]] CartesianPair[
		CartesianMomentum[a4], CartesianMomentum[b1]] -
		CartesianPair[CartesianMomentum[a1], CartesianMomentum[b1]] CartesianPair[CartesianMomentum[a2],
		CartesianMomentum[b3]] CartesianPair[CartesianMomentum[a3], CartesianMomentum[a5]] CartesianPair[
		CartesianMomentum[a4], CartesianMomentum[b2]] +
		CartesianPair[CartesianMomentum[a1], CartesianMomentum[a5]] CartesianPair[CartesianMomentum[a2],
		CartesianMomentum[b3]] CartesianPair[CartesianMomentum[a3], CartesianMomentum[b1]] CartesianPair[
		CartesianMomentum[a4], CartesianMomentum[b2]] +
		CartesianPair[CartesianMomentum[a1], CartesianMomentum[b1]] CartesianPair[CartesianMomentum[a2],
		CartesianMomentum[a5]] CartesianPair[CartesianMomentum[a3], CartesianMomentum[b3]] CartesianPair[
		CartesianMomentum[a4], CartesianMomentum[b2]] -
		CartesianPair[CartesianMomentum[a1], CartesianMomentum[a5]] CartesianPair[CartesianMomentum[a2],
		CartesianMomentum[b1]] CartesianPair[CartesianMomentum[a3], CartesianMomentum[b3]] CartesianPair[
		CartesianMomentum[a4], CartesianMomentum[b2]] +
		CartesianPair[CartesianMomentum[a1],CartesianMomentum[b3]] (CartesianPair[CartesianMomentum[a2],
		CartesianMomentum[b2]] (CartesianPair[CartesianMomentum[a3], CartesianMomentum[b1]] CartesianPair[CartesianMomentum[a4], CartesianMomentum[a5]] -
		CartesianPair[CartesianMomentum[a3], CartesianMomentum[a5]] CartesianPair[CartesianMomentum[a4],CartesianMomentum[b1]]) +
			CartesianPair[CartesianMomentum[a2],
			CartesianMomentum[
			b1]] (-CartesianPair[CartesianMomentum[a3], CartesianMomentum[b2]] CartesianPair[CartesianMomentum[a4],
				CartesianMomentum[a5]] +
			CartesianPair[CartesianMomentum[a3], CartesianMomentum[a5]] CartesianPair[CartesianMomentum[a4],
				CartesianMomentum[b2]]) +
			CartesianPair[CartesianMomentum[a2],
			CartesianMomentum[
			a5]] (CartesianPair[CartesianMomentum[a3], CartesianMomentum[b2]] CartesianPair[CartesianMomentum[a4],
				CartesianMomentum[b1]] -
			CartesianPair[CartesianMomentum[a3], CartesianMomentum[b1]] CartesianPair[CartesianMomentum[a4],
				CartesianMomentum[b2]])) +
		CartesianPair[CartesianMomentum[a1], CartesianMomentum[b1]] CartesianPair[CartesianMomentum[a2],
		CartesianMomentum[b2]] CartesianPair[CartesianMomentum[a3], CartesianMomentum[a5]] CartesianPair[
		CartesianMomentum[a4], CartesianMomentum[b3]] -
		CartesianPair[CartesianMomentum[a1], CartesianMomentum[a5]] CartesianPair[CartesianMomentum[a2],
		CartesianMomentum[b2]] CartesianPair[CartesianMomentum[a3], CartesianMomentum[b1]] CartesianPair[
		CartesianMomentum[a4], CartesianMomentum[b3]] -
		CartesianPair[CartesianMomentum[a1], CartesianMomentum[b1]] CartesianPair[CartesianMomentum[a2],
		CartesianMomentum[a5]] CartesianPair[CartesianMomentum[a3], CartesianMomentum[b2]] CartesianPair[
		CartesianMomentum[a4], CartesianMomentum[b3]] +
		CartesianPair[CartesianMomentum[a1], CartesianMomentum[a5]] CartesianPair[CartesianMomentum[a2],
		CartesianMomentum[b1]] CartesianPair[CartesianMomentum[a3], CartesianMomentum[b2]] CartesianPair[
		CartesianMomentum[a4], CartesianMomentum[b3]] +
		CartesianPair[CartesianMomentum[a1],
		CartesianMomentum[b2]] (CartesianPair[CartesianMomentum[a2],CartesianMomentum[b3]] (-CartesianPair[CartesianMomentum[a3], CartesianMomentum[b1]] CartesianPair[CartesianMomentum[a4],
				CartesianMomentum[a5]] +
			CartesianPair[CartesianMomentum[a3], CartesianMomentum[a5]] CartesianPair[CartesianMomentum[a4],
				CartesianMomentum[b1]]) +
			CartesianPair[CartesianMomentum[a2],
			CartesianMomentum[
			b1]] (CartesianPair[CartesianMomentum[a3], CartesianMomentum[b3]] CartesianPair[CartesianMomentum[a4],
				CartesianMomentum[a5]] -
			CartesianPair[CartesianMomentum[a3], CartesianMomentum[a5]] CartesianPair[CartesianMomentum[a4],
				CartesianMomentum[b3]]) +
			CartesianPair[CartesianMomentum[a2],
			CartesianMomentum[
			a5]] (-CartesianPair[CartesianMomentum[a3], CartesianMomentum[b3]] CartesianPair[CartesianMomentum[a4],
				CartesianMomentum[b1]] +
			CartesianPair[CartesianMomentum[a3], CartesianMomentum[b1]] CartesianPair[CartesianMomentum[a4],
				CartesianMomentum[b3]]))

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
			res = Collect2[res, {CartesianPair}]
		];

		res
];


FCPrint[1,"FMCartesianSchouten2 loaded."];
End[]
