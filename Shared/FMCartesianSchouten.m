(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: FMCartesianSchouten															*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2020 Vladyslav Shtabovenko
*)

(* :Summary:	Applies Schouten's identity									*)

(* ------------------------------------------------------------------------ *)


FMCartesianSchouten::usage =
"FMCartesianSchouten[expr] applies Schouten identity to the given combination of C- and E-tensors";

FMCartesianSchouten::notpresent =
"Warning! The Structure `1` doesn't appear in the expression!"

Begin["`Package`"]
End[]

Begin["`FMCartesianSchouten`Private`"]

Options[FMCartesianSchouten] = {
	Collect		-> True,
	EpsEvaluate -> True,
	Expand		-> True,
	FCI			-> False,
	Head		-> None
};

FMCartesianSchouten[expr_, {i_, j_, k_, l_, m_}, OptionsPattern[]] :=
	Block[{ex, res,pat,head, input, power},
		If[	OptionValue[FCI],
			ex = expr,
			ex = FCI[expr]
		];

		input =
			Eps[CartesianMomentum[i], CartesianMomentum[j], CartesianMomentum[k]] CartesianPair[CartesianMomentum[l], CartesianMomentum[m]];

		If[	OptionValue[Expand],
			ex = Expand2[expr, {Eps, CartesianPair}]
		];

		ex = ex /. Power[p_CartesianPair,n_] :> p power[p,n-1];

		If[	FreeQ[ex, input],
			Message[FMCartesianSchouten::notpresent,ToString[input,InputForm]]
		];



		res =
			ex /. {input :>
				(head[1,Eps[CartesianMomentum[j], CartesianMomentum[k], CartesianMomentum[l]] CartesianPair[
				CartesianMomentum[i], CartesianMomentum[m]]] -
				head[2,Eps[CartesianMomentum[k], CartesianMomentum[l], CartesianMomentum[i]] CartesianPair[
				CartesianMomentum[j], CartesianMomentum[m]]] +
				head[3,Eps[CartesianMomentum[l], CartesianMomentum[i], CartesianMomentum[j]] CartesianPair[
				CartesianMomentum[k], CartesianMomentum[m]]]/. Pattern -> pat /. pat[a_,___]:>a)};

		If[ Length[Cases2[res/.head[_,0]:>0,head]]===1,
			Print["Warning! The replacement of ",
			Eps[CartesianMomentum[i], CartesianMomentum[j], CartesianMomentum[k]] CartesianPair[CartesianMomentum[l], CartesianMomentum[m]], " failed!" ]
		];

		res = res /. power -> Power;

		If[ OptionValue[Head]=!=None,
			res = res /. head -> OptionValue[Head],
			res = res /. head[_,x_]:>x
		];

		If[	OptionValue[EpsEvaluate],
			res = EpsEvaluate[res]
		];

		If[	OptionValue[Collect],
			res = Collect2[res, {Eps, CartesianPair}]
		];

		res
];


FCPrint[1,"FMCartesianSchouten loaded."];
End[]
