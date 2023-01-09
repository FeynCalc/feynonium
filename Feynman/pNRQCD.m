(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: pNRQCD															*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2021 Vladyslav Shtabovenko
*)

(* :Summary:	pNRQCD Feynman rules										*)

(* ------------------------------------------------------------------------ *)


FMKet::usage =
"FMKet[x] is represents a ket vector |x>. It is does not have any special
properties except for being a noncommutative object.";

FMBra::usage =
"FMBra[x] is represents a bra vector <x|. It is does not have any special
properties except for being a noncommutative object.";

FMOctetGluonOctetVertex::usage=
"FMOctetGluonOctetVertex[type_, colo1, {momg, indg, colg}, colo2] is a \
pNRQCD Octet-Gluon-Octet-Vertex. All momenta are incoming. The conventions \
follow Fig. 5 from arXiv:hep-ph/0410047, i.e. colo1 and colo2 are the color \
indices of the right and left octet fields respectively, while \
momg, indg and colg denote the momentum as well as the vector and color indices \
of the gluon. When indg is 0, the temporal component is understood, \
while indg being a symbol yields the spatial component. Following vertices are implemented: \n
FMOctetGluonOctetVertex[{\"1\"}, a, {p, 0, b}, c]: g O^+ i D_0 O
FMOctetGluonOctetVertex[{\"V_B\", r}, a, {p, 0, b}, c]: VB/2 Tr[O^+ (r.g E) O + O^+ O (r.g E)]
FMOctetGluonOctetVertex[{\"V_B\", r}, a, {p, i, b}, c]: VB/2 Tr[O^+ (r.g E) O + O^+ O (r.g E)]";

FMOctetGluonSingletVertex::usage=
"FMOctetGluonSingletVertex[type_, colo1, {momg, indg, colg}] is a \
pNRQCD Octet-Gluon-Singlet-Vertex. All momenta are incoming. The conventions \
follow Fig. 5 from arXiv:hep-ph/0410047, i.e. colo1 is the color \
index of the right octet field, while \
momg, indg and colg denote the momentum as well as the vector and color indices \
of the gluon. When indg is 0, the temporal component is understood, \
while indg being a symbol yields the spatial component. Following vertices are implemented: \n
FMOctetGluonOctetVertex[{\"V_A\", r}, a, {p, 0, b}]: VA Tr[O^+ (r.g E) S + S^+ (r.g E) O]
FMOctetGluonOctetVertex[{\"V_A\", r}, a, {p, i, b}]: VA Tr[O^+ (r.g E) S + S^+ (r.g E) O]";

FMOctetGluonGluonOctetVertex::usage=
"FMOctetGluonGluonOctetVertex[type_, colo1, {momg1, indg1, colg1}, {momg2_, indg2, colg2_}, colo2] is a \
pNRQCD Octet-Gluon-Gluon-Octet-Vertex. All momenta are incoming. The conventions \
follow Fig. 5 from arXiv:hep-ph/0410047, i.e. colo1 and colo2 are the color \
indices of the right and left octet fields respectively, while \
momg1/momg2, indg1/indg2 and colg1/colg2 denote the momenta as well as the vector and color indices \
of the two gluons. When indg1/indg2 is 0, the temporal component understood, \
while indg1/indg2 being a symbol yields the spatial component. Following vertices are implemented: \n
FMOctetGluonGluonOctetVertex[{\"V_B\", r}, a, {p1, i, d}, {p2, 0, c}, b]: VB/2 Tr[O^+ (r.g E) O + O^+ O (r.g E)]";

FMOctetGluonGluonSingletVertex::usage=
"FMOctetGluonGluonSingletVertex[type_, colo1, {momg1, indg1, colg1}, {momg2, indg2, colg2}] is a \
pNRQCD Octet-Gluon-Gluon-Singlet-Vertex. All momenta are incoming. The conventions \
follow Fig. 5 from arXiv:hep-ph/0410047, i.e. colo1 is the color \
index of the right octet field, while \
momg1/momg2, indg1/indg2 and colg1/colg2 denote the momenta as well as the vector and color indices \
of the two gluons. When indg1/indg2 is 0, the temporal component understood, \
while indg1/indg2 being a symbol yields the spatial component. Following vertices are implemented: \n
FMOctetGluonOctetVertex[{\"V_A\", r}, a, {p1, i, b}, {p2, 0, c}]: VA Tr[O^+ (r.g E) S + S^+ (r.g E) O]";

FMSingletPropagator::usage=
"FMSingletPropagator[{p, En, n}] is the pNRQCD singlet field propagator I/(p^0 - E_n) |n> <n|";

FMOctetPropagator::usage=
"FMOctetPropagator[{p, En, n}, {a, b}] is the pNRQCD octet field propagator I d^ab/(p^0 - E_n) |n> <n|";

FMCoulombGaugeGluonPropagator::usage=
"FMCoulombGaugeGluonPropagator[p, {mu, a}, {nu, b}] is the gluon Coulomb gauge propagator \n
I d^ab (d^ij - p^i p^j/(|p|^2))* 1/(p^2) for mu=i, nu=j
I d^ab 1/|p|^2 for mu=0, nu=0";

Begin["`Package`"]
End[]

Begin["`pNRQCD`Private`"]

Unprotect[SMP];
	SMP /: MakeBoxes[SMP["V_A"], TraditionalForm] :=
		SubscriptBox["V", "A"];
	SMP /: MakeBoxes[SMP["V_B"], TraditionalForm] :=
		SubscriptBox["V", "B"];
Protect[SMP];


pNRQCDSymbolsWithExplicitOption[optsExplicit___]:= {
	FMOctetGluonOctetVertex[xx__, op:OptionsPattern[]]  :>
		FMOctetGluonOctetVertex[xx, Explicit -> True, Sequence@@FilterRules[{optsExplicit}, Options[FMOctetGluonOctetVertex]], op],

	FMOctetGluonSingletVertex[xx__, op:OptionsPattern[]]  :>
		FMOctetGluonSingletVertex[xx, Explicit -> True, Sequence@@FilterRules[{optsExplicit}, Options[FMOctetGluonSingletVertex]], op],

	FMOctetGluonGluonOctetVertex[xx__, op:OptionsPattern[]]  :>
		FMOctetGluonGluonOctetVertex[xx, Explicit -> True, Sequence@@FilterRules[{optsExplicit}, Options[FMOctetGluonGluonOctetVertex]], op],

	FMOctetGluonGluonSingletVertex[xx__, op:OptionsPattern[]]  :>
		FMOctetGluonGluonSingletVertex[xx, Explicit -> True, Sequence@@FilterRules[{optsExplicit}, Options[FMOctetGluonGluonSingletVertex]], op],

	FMSingletPropagator[xx__, op:OptionsPattern[]]  :>
		FMSingletPropagator[xx, Explicit -> True, Sequence@@FilterRules[{optsExplicit}, Options[FMSingletPropagator]], op],

	FMOctetPropagator[xx__, op:OptionsPattern[]]  :>
		FMOctetPropagator[xx, Explicit -> True, Sequence@@FilterRules[{optsExplicit}, Options[FMOctetPropagator]], op],

	FMCoulombGaugeGluonPropagator[xx__, op:OptionsPattern[]]  :>
		FMCoulombGaugeGluonPropagator[xx, Explicit -> True, Sequence@@FilterRules[{optsExplicit}, Options[FMCoulombGaugeGluonPropagator]], op]
};


FeynCalc`Package`RulesForSymbolsWithExplicitOption = Join[FeynCalc`Package`RulesForSymbolsWithExplicitOption, {pNRQCDSymbolsWithExplicitOption}];

DeclareNonCommutative[FMKet];
DeclareNonCommutative[FMBra];

Options[FMOctetGluonOctetVertex] := {
	Dimension	-> 	D,
	Explicit	->	False
};

Options[FMOctetGluonSingletVertex] := {
	Dimension	-> 	D,
	Explicit	->	False
};

Options[FMOctetGluonGluonOctetVertex] := {
	Dimension	-> 	D,
	Explicit	->	False
};

Options[FMOctetGluonGluonSingletVertex] := {
	Dimension	-> 	D,
	Explicit	->	False
};

Options[FMSingletPropagator] := {
	Dimension	-> 	D,
	Explicit	->	False
};

Options[FMOctetPropagator] := {
	Dimension	-> 	D,
	Explicit	->	False
};

Options[FMCoulombGaugeGluonPropagator] := {
	Dimension	-> 	D,
	Explicit	->	False
};

FMKet /: MakeBoxes[FMKet[x__], TraditionalForm] :=
	ToBoxes[Row[{"|", Sequence @@ {x}, "\[RightAngleBracket]"}], TraditionalForm];

FMBra /: MakeBoxes[FMBra[x__], TraditionalForm] :=
	ToBoxes[Row[{"\[LeftAngleBracket]", Sequence @@ {x}, "|"}], TraditionalForm];

FMOctetGluonOctetVertex[{"1"}, colo1_, {(*momg*)_, 0, colg_}, colo2_, OptionsPattern[]] :=
	(
	SMP["g_s"] SUNF[SUNIndex[colo1], SUNIndex[colg], SUNIndex[colo2]]
	)/; OptionValue[Explicit];

FMOctetGluonOctetVertex[{"V_B", r_Symbol}, colo1_, {momg_, indg_ /; indg =!= 0, colg_}, colo2_, OptionsPattern[]] :=
	Block[{dim},
		dim = OptionValue[Dimension];
		DeclareNonCommutative[r];
		DeclareFCTensor[r];
		-SMP["g_s"] SMP["V_B"]/2 SUND[SUNIndex[colo1], SUNIndex[colg], SUNIndex[colo2]]*
		r[CartesianIndex[indg, dim - 1]] TemporalPair[TemporalMomentum[momg], LorentzIndex[0]]
	]/; OptionValue[Explicit];

FMOctetGluonOctetVertex[{"V_B", r_Symbol}, colo1_, {momg_, 0, colg_}, colo2_, OptionsPattern[]] :=
	Block[{dim},
		dim = OptionValue[Dimension];
		DeclareNonCommutative[r];
		DeclareFCTensor[r];
		SMP["g_s"] SMP["V_B"]/2 SUND[SUNIndex[colo1], SUNIndex[colg],SUNIndex[colo2]]*
		r[CartesianMomentum[momg, dim - 1]]
	]/; OptionValue[Explicit];

FMOctetGluonSingletVertex[{"V_A", r_Symbol}, colo1_, {momg_, indg_ /; indg =!= 0, colg_}, OptionsPattern[]] :=
	Block[{dim},
		dim = OptionValue[Dimension];
		DeclareNonCommutative[r];
		DeclareFCTensor[r];
		-SMP["g_s"] SMP["V_A"] SUNDelta[SUNIndex[colo1], SUNIndex[colg]]*
		Sqrt[Tf/SUNN]*r[CartesianIndex[indg, dim - 1]] TemporalPair[TemporalMomentum[momg], LorentzIndex[0]]
	]/; OptionValue[Explicit];


FMOctetGluonSingletVertex[{"V_A", r_Symbol}, colo1_, {momg_, 0, colg_}, OptionsPattern[]] :=
	Block[{dim},
		dim = OptionValue[Dimension];
		DeclareNonCommutative[r];
		DeclareFCTensor[r];
		SMP["g_s"] SMP["V_A"] SUNDelta[SUNIndex[colo1], SUNIndex[colg]]*
		Sqrt[Tf/SUNN]*r[CartesianMomentum[momg, dim - 1]]
	]/; OptionValue[Explicit];

FMOctetGluonGluonOctetVertex[{"V_B", r_Symbol}, colo1_, {(*momg1*)_, indg1_ /; indg1 =!= 0, colg1_}, {(*momg2*)_, 0, colg2_}, colo2_, OptionsPattern[]] :=
	Block[{dummy, dim},
		dim = OptionValue[Dimension];
		dummy = Unique["col"];
		DeclareNonCommutative[r];
		DeclareFCTensor[r];
		-I*SMP["g_s"]^2 SMP["V_B"]/2 SUND[SUNIndex[colo1], SUNIndex[colo2], SUNIndex[dummy]]*
		SUNF[SUNIndex[dummy], SUNIndex[colg1], SUNIndex[colg2]] r[CartesianIndex[indg1, dim - 1]]
	]/; OptionValue[Explicit];

FMOctetGluonGluonSingletVertex[{"V_A", r_Symbol}, colo_, {(*momg1*)_, indg1_ /; indg1 =!= 0, colg1_}, {(*momg2*)_, 0, colg2_}, OptionsPattern[]] :=
	Block[{dim},
		dim = OptionValue[Dimension];
		DeclareNonCommutative[r];
		DeclareFCTensor[r];
		-I*SMP["g_s"]^2 SMP["V_A"]*Sqrt[Tf/SUNN]*
		SUNF[SUNIndex[colo], SUNIndex[colg1], SUNIndex[colg2]] r[CartesianIndex[indg1, dim - 1]]
	]/; OptionValue[Explicit];

FMSingletPropagator[{p_, En_, n_}, OptionsPattern[]] :=
	Block[{dim},
		dim = OptionValue[Dimension];
		I*FMKet[n].FMBra[n] FeynAmpDenominator[GenericPropagatorDenominator[-En +
			TemporalPair[ExplicitLorentzIndex[0], TemporalMomentum[p]], {1, 1}]]
	]/; OptionValue[Explicit];

FMOctetPropagator[{p_, En_, n_}, {col1_, col2_}, OptionsPattern[]] :=
	Block[{dim},
		dim = OptionValue[Dimension];
		I*FMKet[n].FMBra[n]  SUNDelta[SUNIndex[col1], SUNIndex[col2]] *
		FeynAmpDenominator[GenericPropagatorDenominator[-En + TemporalPair[ExplicitLorentzIndex[0], TemporalMomentum[p]], {1,1}]]
	]/; OptionValue[Explicit];


FMCoulombGaugeGluonPropagator[p_, {ind1_ /; ind1 =!= 0, col1_}, {ind2_ /; ind2 =!= 0, col2_}, OptionsPattern[]] :=
	Block[{dim},
		dim = OptionValue[Dimension];
		I SUNDelta[SUNIndex[col1], SUNIndex[col2]] FeynAmpDenominator[StandardPropagatorDenominator[Momentum[p, dim], 0,
		0, {1, 1}]]*(
		CartesianPair[CartesianIndex[ind1, dim - 1], CartesianIndex[ind2, dim - 1]] -
		CartesianPair[CartesianMomentum[p, dim - 1],CartesianIndex[ind1, dim - 1]] *
		CartesianPair[CartesianMomentum[p, dim - 1], CartesianIndex[ind2, dim - 1]] FeynAmpDenominator[
		CartesianPropagatorDenominator[CartesianMomentum[p, -1 + dim], 0, 0, {1, -1}]]
		)
	]/; OptionValue[Explicit];

FMCoulombGaugeGluonPropagator[p_, {0, col1_}, {0, col2_}, OptionsPattern[]] :=
	Block[{dim},
		dim = OptionValue[Dimension];
		I SUNDelta[SUNIndex[col1], SUNIndex[col2]]*
		FeynAmpDenominator[CartesianPropagatorDenominator[CartesianMomentum[p, -1 + dim], 0, 0, {1, -1}]]
	]/; OptionValue[Explicit];


FCPrint[1,"pNRQCD loaded."];
End[]
