(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: FMCartesianSchouten															*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2016 Vladyslav Shtabovenko
*)

(* :Summary:	Applies Schoute identity									*)

(* ------------------------------------------------------------------------ *)


FMCartesianSchouten::usage =
"FMCartesianSchouten[expr] applies Schouten identity to the given combination of C- and E-tensors";

FMCartesianSchouten::notpresent =
"Warning! The Structure `1` doesn't appear in the expression!"

Begin["`Package`"]
End[]

Begin["`FMCartesianSchouten`Private`"]

Options[FMCartesianSchouten] = {
	FCI -> False,
	Expand -> True,
	Collect -> True,
	EpsEvaluate -> True,
	Head -> None
};

FMCartesianSchouten[expr_, {i_, j_, k_, l_, m_}, OptionsPattern[]] :=
	Block[{ex, res,pat,head, input, power},
		If[	OptionValue[FCI],
			ex = expr,
			ex = FCI[expr]
		];

		input =
			Eps[CMomentum[i], CMomentum[j], CMomentum[k]] CPair[CMomentum[l], CMomentum[m]];

		If[	OptionValue[Expand],
			ex = Expand2[expr, {Eps, CPair}]
		];

		ex = ex /. Power[p_CPair,n_] :> p power[p,n-1];

		If[	FreeQ[ex, input],
			Message[FMCartesianSchouten::notpresent,ToString[input,InputForm]]
		];



		res =
			ex /. {input :>
				(head[1,Eps[CMomentum[j], CMomentum[k], CMomentum[l]] CPair[
				CMomentum[i], CMomentum[m]]] -
				head[2,Eps[CMomentum[k], CMomentum[l], CMomentum[i]] CPair[
				CMomentum[j], CMomentum[m]]] +
				head[3,Eps[CMomentum[l], CMomentum[i], CMomentum[j]] CPair[
				CMomentum[k], CMomentum[m]]]/. Pattern -> pat /. pat[a_,___]:>a)};

		If[ Length[Cases2[res/.head[_,0]:>0,head]]===1,
			Print["Warning! The replacement of ",
			Eps[CMomentum[i], CMomentum[j], CMomentum[k]] CPair[CMomentum[l], CMomentum[m]], " failed!" ]
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
			res = Collect2[res, {Eps, CPair}]
		];

		res
];


FCPrint[1,"FMCartesianSchouten loaded."];
End[]
