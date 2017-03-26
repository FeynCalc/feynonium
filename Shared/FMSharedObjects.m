(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: FMSharedObjects													*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2016 Vladyslav Shtabovenko
*)

(* :Summary:	Basic FeynOnium objects										*)

(* ------------------------------------------------------------------------ *)

FMStandardSpinorChain::usage=
"FMStandardSpinorChain[type,i,{p1,m1},{p2,m2}] denotes a 4-dimensional standard spinor chain. \
The value of type can be \"S\" (scalar), \"P\" (pseudoscalar), \"V\" (vector), \"A\" (axial-vector) or \"T\" (tensor). \n
The value of i can be 1 (ubar ... v), 2 (vbar ... u), 3 ( ubar ... u) or 4 (vbar ... v). \n
Finally p1, m1 and p2, m2 denote the mass and the momentum of the first and the last spinor respectively.";

FMBlockMatrixProduct::usage="";

Begin["`Package`"]
End[]

Begin["`FMSharedObjects`Private`"]
bmtmp::usage="";

DataType[FMStandardSpinorChain, FCTensor] = True;

(*
(*  eta^+ (...) xi corresponds to <0| chi^+ (...) psi *)
NRQCDSpinSinglet /:
	MakeBoxes[NRQCDSpinSinglet[Complex[0, 1]], TraditionalForm] :=
		RowBox[{SuperscriptBox["\[Eta]", "\[Dagger]"], ".", "\[Xi]"}];

(*  xi^+ (...) eta corresponds to psi^+ (...) xi |0> *)
NRQCDSpinSinglet /:
	MakeBoxes[NRQCDSpinSinglet[Complex[0, -1]], TraditionalForm] :=
		RowBox[{SuperscriptBox["\[Xi]", "\[Dagger]"], ".", "\[Eta]"}];
*)

FMStandardSpinorChain["T", _Integer, _List, _List, 0, _]:=
	0;

FMStandardSpinorChain["T", _Integer, _List, _List, _, 0]:=
	0;

FMStandardSpinorChain["T", _Integer, _List, _List, TIndex[], TIndex[] ]:=
	0;

FMStandardSpinorChain["T", _Integer, _List, _List, (a: _LorentzIndex | _CIndex | _Momentum | _CMomentum ),
	(a: _LorentzIndex | _CIndex | _Momentum | _CMomentum )]:=
	0;

FMStandardSpinorChain["T", i_Integer, l1_List, l2_List, (a:_CIndex | _CMomentum), TIndex[]]:=
	- FMStandardSpinorChain["T", i, l1, l2, TIndex[], a];

FMStandardSpinorChain /:
	MakeBoxes[FMStandardSpinorChain[t_String, i_, {p1_, m1_}, {p2_, m2_}], TraditionalForm] :=
	Switch[ i,
		1,
			SubscriptBox[t, RowBox[{ToBoxes[SpinorUBar[p1, m1], TraditionalForm], ToBoxes[SpinorV[p2, m2], TraditionalForm]}]],
		2,
			SubscriptBox[t, RowBox[{ToBoxes[SpinorVBar[p1, m1], TraditionalForm], ToBoxes[SpinorU[p2, m2], TraditionalForm]}]],
		3,
			SubscriptBox[t, RowBox[{ToBoxes[SpinorUBar[p1, m1], TraditionalForm], ToBoxes[SpinorU[p2, m2], TraditionalForm]}]],
		4,
			SubscriptBox[t, RowBox[{ToBoxes[SpinorVBar[p1, m1], TraditionalForm], ToBoxes[SpinorV[p2, m2], TraditionalForm]}]],
		_,
			Abort[]
	];

FMStandardSpinorChain /:
	MakeBoxes[FMStandardSpinorChain[t_String, i_, {p1_, m1_}, {p2_, m2_}, args__], TraditionalForm] :=
	Switch[ i,
		1,
			SubsuperscriptBox[t, RowBox[{ToBoxes[SpinorUBar[p1, m1], TraditionalForm], ToBoxes[SpinorV[p2, m2], TraditionalForm]}],
				RowBox[Map[ToBoxes[#,TraditionalForm]&,{args}]]],
		2,
			SubsuperscriptBox[t, RowBox[{ToBoxes[SpinorVBar[p1, m1], TraditionalForm], ToBoxes[SpinorU[p2, m2], TraditionalForm]}],
				RowBox[Map[ToBoxes[#,TraditionalForm]&,{args}]]],
		3,
			SubsuperscriptBox[t, RowBox[{ToBoxes[SpinorUBar[p1, m1], TraditionalForm], ToBoxes[SpinorU[p2, m2], TraditionalForm]}],
				RowBox[Map[ToBoxes[#,TraditionalForm]&,{args}]]],
		4,
			SubsuperscriptBox[t, RowBox[{ToBoxes[SpinorVBar[p1, m1], TraditionalForm], ToBoxes[SpinorV[p2, m2], TraditionalForm]}],
				RowBox[Map[ToBoxes[#,TraditionalForm]&,{args}]]],
		_,
			Abort[]
	]

FMBlockMatrixProduct[___,0,___] :=
	0;

FMBlockMatrixProduct[x_List] :=
	x;

FMBlockMatrixProduct[x_List, y_List] :=
	(
		bmtmp = Inner[Dot, x, y];
		If[	MatchQ[bmtmp, List[z_] /; FreeQ[z, List] && Length[{z}] === 1],
			Identity @@ bmtmp,
			bmtmp
		]
	);

FMBlockMatrixProduct[x_List, y_List, z__List] :=
	FMBlockMatrixProduct[x, FMBlockMatrixProduct[y, z]];


FCPrint[1,"FMSharedObjects loaded."];
End[]
