(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: FMSpinorChainsExplicit												*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2017 Vladyslav Shtabovenko
*)

(* :Summary:	Non-relativistic NRQCD expressions for spinor chains		*)

(* ------------------------------------------------------------------------ *)


FMSpinorChainsExplicit::usage =
"FMSpinorChainsExplicit[expr_] ...";

FMSpinorNormalization::usage =
"";

FMKinematicsOfHeavyFermions::usage=
"FMKinematicsOfHeavyFermions is an option for FMSpinorChainsExplicit. It determines \
the kinematical configuration of the heavy fermions that are represented by the spinors \
with momenta p1 and p2 and masses m1 and m2 respectively. Following values are supported: \n

\"Original\" - The dependence on the momenta p1 and p2 remains unchanged. \n

\"TwoBodyRestFrame\" - p1 and p2 are assumed to be rest frame vectors of a 2-body system. \
The dependence of the spinor chains on p1 and p2 is rewritten in terms of Jacobi momenta PR and QR as \
p1 = 1/2 P + Q, p2 = 1/2 P - Q. This is useful to study the annihilation of two heavy fermions. \
(e.g. decays of heavy quarkonia) \n

\"TwoBodyLabFrame\" - p1 and p2 are assumed to be laboratory frame vectors of a 2-body system. \
When boosted to the rest frame  of the system, they become p1R and p2R. The dependence of the spinor \
chains on p1 and p2 is rewritten in terms of p1R and p2R. The latter are rewritten in terms \
of Jacobi momenta P and Q as p1R = 1/2 P + Q, p2R = 1/2 P - Q. This is useful to study creation of \
non-relativistic systems that consist of two heavy fermions (e.g. production of heavy quarkonia). \n

\"ThreeBodyRestFrame\" - p1 and p2 are assumed to be rest frame vectors of a 3-body system. \
The dependence of the spinor chains on p1 and p2 is rewritten in terms of Jacobi momenta P, Q1 and Q2 as \
p1 = 1/3 P + Q1 - Q2, p2 = 1/3 P - Q1 - Q2. The third momentum of the 3-body system should be then rewritten
as p3 = 1/3 P + 2 Q2. This is useful to study the annihilation of two heavy fermions and a boson. \
(e.g. decays of heavy quarkonia) \n

\"ThreeBodyLabFrame\" - p1 and p2 are assumed to be laboratory frame vectors of a 2-body system. \
When boosted to the rest frame  of the system, they become p1R and p2R. The dependence of the spinor \
chains on p1 and p2 is rewritten in terms of p1R and p2R. The latter are rewritten in terms \
of Jacobi momenta P, Q1 and Q2 as p1 = 1/3 P + Q1 - Q2, p2 = 1/3 P - Q1 - Q2. The third momentum \
of the 3-body system should be then rewritten as p3 = 1/3 P + 2 Q2. This is useful to study creation of \
non-relativistic systems that consist of two heavy fermions and a boson (e.g. production of heavy quarkonia). \n
";

FMSpinorChainsExplicit::failmsg =
"Error! FMSpinorChainsExplicit has encountered a fatal problem and must abort the computation. \
The problem reads: `1`"


Begin["`Package`"]
End[]

Begin["`FMSpinorChainsExplicit`Private`"]

holdSpinorChains::usage="";
normalization::usage="";
sceVerbose::usage="";


Options[FMSpinorChainsExplicit] = {
	Collect :> True,
	DotSimplify -> True,
	EpsEvaluate -> True,
	ExpandScalarProduct -> True,
	FCI -> False,
	FCVerbose -> False,
	FMKinematicsOfHeavyFermions -> "Original",
	FMSpinorNormalization -> "relativistic",
	FinalSubstitutions -> {},
	Head -> Identity,
	PowerExpand -> True
};

FMSpinorChainsExplicit[expr_List, {p1final_, m1_}, {p2final_, m2_}, opts:OptionsPattern[]]:=
	Map[FMSpinorChainsExplicit[#, {p1final, m1}, {p2final, m2}, opts]&,expr];



FMSpinorChainsExplicit[expr_, {p1final_, m1_}, {p2final_, m2_}, OptionsPattern[]]:=
	Block[{ex, tmp, res, moms, heads, pairs,  chainList,head, headFinal, P, Eq,
			q, q1,q2 ,P0, SqP2, headNew, repRuleNormalization = {},
			boostedChainRulesQQbar, p1, p2, sanitizeChains,PR0,boostedChainRulesQQbarG,Q1,Q2,
			p1R0,p2R0,p1R,p2R, tmpci, PR,
			chainRules1,
			chainRules2,
			ruleKinematics,
			ruleTwoBodyRestFrameKinematics,
			ruleTwoBodyLabFrameKinematics,
			ruleThreeBodyRestFrameKinematics,
			ruleThreeBodyLabFrameKinematics
			},

		If [OptionValue[FCVerbose]===False,
			sceVerbose=$VeryVerbose,
			If[MatchQ[OptionValue[FCVerbose], _Integer?Positive | 0],
				sceVerbose=OptionValue[FCVerbose]
			];
		];

		normalization = OptionValue[FMSpinorNormalization];

		ruleTwoBodyRestFrameKinematics = {
			CartesianMomentum[p1] -> CartesianMomentum[FCGV["Jacobi QR"]],
			CartesianMomentum[p2] -> -CartesianMomentum[FCGV["Jacobi QR"]],
			TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[p1]] -> Sqrt[m1^2 + CartesianPair[CartesianMomentum[FCGV["Jacobi QR"]],CartesianMomentum[FCGV["Jacobi QR"]]]],
			TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[p2]] -> Sqrt[m2^2 + CartesianPair[CartesianMomentum[FCGV["Jacobi QR"]],CartesianMomentum[FCGV["Jacobi QR"]]]]
		};

		ruleThreeBodyRestFrameKinematics = {
			CartesianMomentum[p1] -> CartesianMomentum[FCGV["Jacobi Q1R"]]-CartesianMomentum[FCGV["Jacobi Q2R"]],
			CartesianMomentum[p2] -> -CartesianMomentum[FCGV["Jacobi Q1R"]]-CartesianMomentum[FCGV["Jacobi Q2R"]],
			TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[p1]] -> Sqrt[m1^2 +
				CartesianPair[CartesianMomentum[FCGV["Jacobi Q1R"]]-CartesianMomentum[FCGV["Jacobi Q2R"]],CartesianMomentum[FCGV["Jacobi Q1R"]]-CartesianMomentum[FCGV["Jacobi Q2R"]]]],
			TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[p2]] -> Sqrt[m2^2 +
				CartesianPair[CartesianMomentum[FCGV["Jacobi Q1R"]]+CartesianMomentum[FCGV["Jacobi Q2R"]],CartesianMomentum[FCGV["Jacobi Q1R"]]+CartesianMomentum[FCGV["Jacobi Q2R"]]]]
		};

		ruleTwoBodyLabFrameKinematics = {
			CartesianMomentum[p1R] -> CartesianMomentum[FCGV["Jacobi QR"]],
			CartesianMomentum[p2R] -> -CartesianMomentum[FCGV["Jacobi QR"]],
			TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[p1R]] -> Sqrt[m1^2 + CartesianPair[CartesianMomentum[FCGV["Jacobi QR"]],CartesianMomentum[FCGV["Jacobi QR"]]]],
			TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[p2R]] -> Sqrt[m2^2 + CartesianPair[CartesianMomentum[FCGV["Jacobi QR"]],CartesianMomentum[FCGV["Jacobi QR"]]]],
			TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[PR]] -> (	Sqrt[m1^2 + CartesianPair[CartesianMomentum[FCGV["Jacobi QR"]],CartesianMomentum[FCGV["Jacobi QR"]]]]+
												Sqrt[m2^2 + CartesianPair[CartesianMomentum[FCGV["Jacobi QR"]],CartesianMomentum[FCGV["Jacobi QR"]]]]),
			CartesianMomentum[P] -> CartesianMomentum[FCGV["Jacobi P"]]
		};

		ruleThreeBodyLabFrameKinematics = {
			CartesianMomentum[p1R] -> CartesianMomentum[FCGV["Jacobi Q1R"]]-CartesianMomentum[FCGV["Jacobi Q2R"]],
			CartesianMomentum[p2R] -> -CartesianMomentum[FCGV["Jacobi Q1R"]]-CartesianMomentum[FCGV["Jacobi Q2R"]],
			TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[p1R]] -> Sqrt[m1^2 +
				CartesianPair[CartesianMomentum[FCGV["Jacobi Q1R"]]-CartesianMomentum[FCGV["Jacobi Q2R"]],CartesianMomentum[FCGV["Jacobi Q1R"]]-CartesianMomentum[FCGV["Jacobi Q2R"]]]],
			TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[p2R]] -> Sqrt[m2^2 +
				CartesianPair[CartesianMomentum[FCGV["Jacobi Q1R"]]+CartesianMomentum[FCGV["Jacobi Q2R"]],CartesianMomentum[FCGV["Jacobi Q1R"]]+CartesianMomentum[FCGV["Jacobi Q2R"]]]],

			TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[PR]] -> ( Sqrt[4 CartesianPair[CartesianMomentum[FCGV["Jacobi Q2R"]],CartesianMomentum[FCGV["Jacobi Q2R"]]] + FCGV["m3"]^2] +

				Sqrt[m1^2 +
				CartesianPair[CartesianMomentum[FCGV["Jacobi Q1R"]]-CartesianMomentum[FCGV["Jacobi Q2R"]],CartesianMomentum[FCGV["Jacobi Q1R"]]-CartesianMomentum[FCGV["Jacobi Q2R"]]]] +

				Sqrt[m2^2 +
				CartesianPair[CartesianMomentum[FCGV["Jacobi Q1R"]]+CartesianMomentum[FCGV["Jacobi Q2R"]],CartesianMomentum[FCGV["Jacobi Q1R"]]+CartesianMomentum[FCGV["Jacobi Q2R"]]]]

			),

			CartesianMomentum[P] -> CartesianMomentum[FCGV["Jacobi P"]]

		};


		headFinal = OptionValue[Head];

		(* This is for cases when there are already some rules attached to p1final and p2final *)
		sanitizeChains = {
			FMStandardSpinorChain[zzz__,{p1final,m1},{p2final,m2},arg___] :> FMStandardSpinorChain[zzz,{p1,m1},{p2,m2},arg]
		};


		If[	OptionValue[FCI],
			ex = expr,
			ex = FCI[expr]
		];

		FCPrint[1, "FMSpinorChainsExplicit: Entering.", FCDoControl->sceVerbose];
		FCPrint[3, "FMSpinorChainsExplicit: Entering with: ", ex,  FCDoControl->sceVerbose];


		tmp = ex /. sanitizeChains;

		Switch[
			OptionValue[FMKinematicsOfHeavyFermions],
			"Original",
				FCPrint[1, "FMSpinorChainsExplicit: Original kinematics selected.", FCDoControl->sceVerbose];
				chainRules1= createRestFramChainRules[p1,p2,m1,m2, head];
				chainRules2 ={};
				ruleKinematics = {},
			"TwoBodyRestFrame",
				FCPrint[1, "FMSpinorChainsExplicit: Two body rest frame kinematics selected.", FCDoControl->sceVerbose];
				chainRules1= createRestFramChainRules[p1,p2,m1,m2, head];
				chainRules2 ={};
				ruleKinematics = ruleTwoBodyRestFrameKinematics,
			"ThreeBodyRestFrame",
				FCPrint[1, "FMSpinorChainsExplicit: Three body rest frame kinematics selected.", FCDoControl->sceVerbose];
				chainRules1= createRestFramChainRules[p1,p2,m1,m2, head];
				chainRules2 ={};
				ruleKinematics = ruleThreeBodyRestFrameKinematics,
			"TwoBodyLabFrame",
				FCPrint[1, "FMSpinorChainsExplicit: Two body lab frame kinematics selected.", FCDoControl->sceVerbose];
				chainRules1= createBoostedChainRules[p1,p2,m1,m2, head, P, p1R, p2R, PR];
				chainRules2 =createRestFramChainRules[p1R,p2R,m1,m2, head];
				ruleKinematics = ruleTwoBodyLabFrameKinematics,
			"ThreeBodyLabFrame",
				FCPrint[1, "FMSpinorChainsExplicit: Three body lab frame kinematics selected.", FCDoControl->sceVerbose];
				chainRules1= createBoostedChainRules[p1,p2,m1,m2, head, P, p1R, p2R, PR];
				chainRules2 =createRestFramChainRules[p1R,p2R,m1,m2, head];
				ruleKinematics = ruleThreeBodyLabFrameKinematics,
			_,
				Message[FMSpinorChainsExplicit::failmsg,"Unknown kinematic configuration"];
				Abort[]
		];

		FCPrint[3, "FMSpinorChainsExplicit: chainRules1 ", chainRules1,  FCDoControl->sceVerbose];
		FCPrint[3, "FMSpinorChainsExplicit: chainRules2 ", chainRules2,  FCDoControl->sceVerbose];
		FCPrint[3, "FMSpinorChainsExplicit: ruleKinematics ", ruleKinematics,  FCDoControl->sceVerbose];

		res = tmp  /. chainRules1 /. holdSpinorChains->FMStandardSpinorChain /. chainRules2;

		FCPrint[3, "FMSpinorChainsExplicit: After applying chainRules1 and chainRules2: ", res,  FCDoControl->sceVerbose];

		res = res /. head[x_]:> head[x /. head->Identity];
		res = res /. head[x_]:> head[x //. ruleKinematics];

		FCPrint[3, "FMSpinorChainsExplicit: After applying ruleKinematics: ", res,  FCDoControl->sceVerbose];

		res = res //. {p1->p1final, p2 -> p2final}/. OptionValue[FinalSubstitutions];

		FCPrint[3, "FMSpinorChainsExplicit: Intermediate result: ", res,  FCDoControl->sceVerbose];

		If[	OptionValue[ExpandScalarProduct],
			res = res/. head[x_]:> head[ExpandScalarProduct[x,FCI->True]]
		];

		If[	OptionValue[EpsEvaluate],
			res = res/. head[x_]:> head[EpsEvaluate[x,FCI->True]]
		];

		If[	OptionValue[PowerExpand],
			res = res/. head[x_]:> head[Expand[PowerExpand[x]]]
		];

		If[	OptionValue[DotSimplify],
			res = res/. head[x_]:> head[DotSimplify[x,FCI->False]]
		];

		If[	OptionValue[Collect],
			res = res/. head[x_]:> head[Collect2[x,{PauliXi,PauliEta}]]
		];


		res = res /. head -> headFinal;


		res

	];

createRestFramChainRules[p1_,p2_,m1_, m2_,  head_]:=
	Block[{p10, p20, p1p2, tmpci,n1,n2, res, norm},

		Switch[
			normalization,
			"nonrelativistic",
				n1 = Sqrt[(p10+ m1)/(2 p10)];
				n2 = Sqrt[(p20+ m2)/(2 p20)],
			"relativistic",
				n1 = Sqrt[(p10+ m1)];
				n2 = Sqrt[(p20+ m2)],
			"unspecified",
				n1 = FCGV["N1"];
				n2 = FCGV["N2"],
			_,
			Message[FMSpinorChainsExplicit::failmsg, "Unknown normalization of Dirac spinors."];
			Abort[]
		];

	res = {

		(*	Production scalar chain	*)
		FMStandardSpinorChain["S",1,{p1,m1},{p2,m2}] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[Momentum[p1], m1, 1].Spinor[-Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Production pseudo-scalar chain	*)
		FMStandardSpinorChain["P",1,{p1,m1},{p2,m2}] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[Momentum[p1], m1, 1].DiracGamma[5].Spinor[-Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],


		(*	Production vector chain , temporal component	*)
		TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[FMStandardSpinorChain["V",1,{p1,m1},{p2,m2}]]] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[Momentum[p1], m1, 1].DiracGamma[ExplicitLorentzIndex[0]].Spinor[-Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Production vector chain , spatial component	*)
		CartesianPair[(x: _CartesianIndex | _CartesianMomentum),CartesianMomentum[FMStandardSpinorChain["V",1,{p1,m1},{p2,m2}]]] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[Momentum[p1], m1, 1].DiracGamma[x].Spinor[-Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Production axial-vector chain , temporal component	*)
		TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[FMStandardSpinorChain["A",1,{p1,m1},{p2,m2}]]] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[Momentum[p1], m1, 1].DiracGamma[ExplicitLorentzIndex[0]].DiracGamma[5].Spinor[-Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Production axial-vector chain , spatial component	*)
		CartesianPair[(x: _CartesianIndex | _CartesianMomentum),CartesianMomentum[FMStandardSpinorChain["A",1,{p1,m1},{p2,m2}]]] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[Momentum[p1], m1, 1].DiracGamma[x].DiracGamma[5].Spinor[-Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],


		(*	Production tensor chain , temporal-spatial component	*)
		FMStandardSpinorChain["T",1,{p1,m1},{p2,m2},ExplicitLorentzIndex[0], (x: _CartesianIndex | _CartesianMomentum)] :>
			head[norm I ( FMSpinorChainExplicit2[Spinor[Momentum[p1], m1, 1].DiracGamma[ExplicitLorentzIndex[0]].DiracGamma[x].Spinor[-Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Production tensor chain , spatial-spatial component	*)
		FMStandardSpinorChain["T",1,{p1,m1},{p2,m2},(x: _CartesianIndex | _CartesianMomentum), (y: _CartesianIndex | _CartesianMomentum)] :>
			head[I norm (

				(CartesianPair[x, CartesianMomentum[p1]]  PauliXi[-I].PauliSigma[y].PauliEta[I] -
				CartesianPair[y, CartesianMomentum[p1]]  PauliXi[-I].PauliSigma[x].PauliEta[I] +
				I Eps[CartesianMomentum[p1],x,y] PauliXi[-I].PauliEta[I])/(p10+m1) -

				(CartesianPair[y, CartesianMomentum[p2]]  PauliXi[-I].PauliSigma[x].PauliEta[I] -
				CartesianPair[x, CartesianMomentum[p2]]  PauliXi[-I].PauliSigma[y].PauliEta[I] +
				I Eps[CartesianMomentum[p2],x,y] PauliXi[-I].PauliEta[I])/(p20+m2)
			)],

		(*	----------------------------------------------------------------------------------	*)

		(*	Decay scalar chain	*)
		FMStandardSpinorChain["S",2,{p1,m1},{p2,m2}] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[-Momentum[p1], m1, 1].Spinor[Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Decay pseudo-scalar chain	*)
		FMStandardSpinorChain["P",2,{p1,m1},{p2,m2}] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[-Momentum[p1], m1, 1].DiracGamma[5].Spinor[Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Decay vector chain , temporal component	*)
		TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[FMStandardSpinorChain["V",2,{p1,m1},{p2,m2}]]] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[-Momentum[p1], m1, 1].DiracGamma[ExplicitLorentzIndex[0]].Spinor[Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Decay vector chain , spatial component	*)
		CartesianPair[(x: _CartesianIndex | _CartesianMomentum),CartesianMomentum[FMStandardSpinorChain["V",2,{p1,m1},{p2,m2}]]] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[-Momentum[p1], m1, 1].DiracGamma[x].Spinor[Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Decay axial-vector chain , temporal component	*)
		TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[FMStandardSpinorChain["A",2,{p1,m1},{p2,m2}]]] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[-Momentum[p1], m1, 1].DiracGamma[ExplicitLorentzIndex[0]].DiracGamma[5].Spinor[Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Decay axial-vector chain , spatial component	*)
		CartesianPair[(x: _CartesianIndex | _CartesianMomentum),CartesianMomentum[FMStandardSpinorChain["A",2,{p1,m1},{p2,m2}]]] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[-Momentum[p1], m1, 1].DiracGamma[x].DiracGamma[5].Spinor[Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],


		(*	Decay tensor chain , temporal-spatial component	*)
		FMStandardSpinorChain["T",2,{p1,m1},{p2,m2},ExplicitLorentzIndex[0], (x: _CartesianIndex | _CartesianMomentum)] :>
			head[norm I ( FMSpinorChainExplicit2[Spinor[-Momentum[p1], m1, 1].DiracGamma[ExplicitLorentzIndex[0]].DiracGamma[x].Spinor[Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],


		(*	Decay tensor chain , spatial-spatial component	*)
		FMStandardSpinorChain["T",2,{p1,m1},{p2,m2},(x: _CartesianIndex | _CartesianMomentum), (y: _CartesianIndex | _CartesianMomentum)] :>
			head[-I norm (

				(CartesianPair[x, CartesianMomentum[p1]]  PauliEta[-I].PauliSigma[y].PauliXi[I] -
				CartesianPair[y, CartesianMomentum[p1]]  PauliEta[-I].PauliSigma[x].PauliXi[I] +
				I Eps[CartesianMomentum[p1],x,y] PauliEta[-I].PauliXi[I])/(p10+m1) -

				(CartesianPair[y, CartesianMomentum[p2]]  PauliEta[-I].PauliSigma[x].PauliXi[I] -
				CartesianPair[x, CartesianMomentum[p2]]  PauliEta[-I].PauliSigma[y].PauliXi[I] +
				I Eps[CartesianMomentum[p2],x,y] PauliEta[-I].PauliXi[I])/(p20+m2)
			)],

		(*	----------------------------------------------------------------------------------	*)

		(*	Fermion-fermion scalar chain	*)
		FMStandardSpinorChain["S",3,{p1,m1},{p2,m2}] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[Momentum[p1], m1, 1].Spinor[Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Fermion-fermion pseudo-scalar chain	*)
		FMStandardSpinorChain["P",3,{p1,m1},{p2,m2}] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[Momentum[p1], m1, 1].DiracGamma[5].Spinor[Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Fermion-fermion vector chain , temporal component	*)
		TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[FMStandardSpinorChain["V",3,{p1,m1},{p2,m2}]]] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[Momentum[p1], m1, 1].DiracGamma[ExplicitLorentzIndex[0]].Spinor[Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Fermion-fermion vector chain , spatial component	*)
		CartesianPair[(x: _CartesianIndex | _CartesianMomentum),CartesianMomentum[FMStandardSpinorChain["V",3,{p1,m1},{p2,m2}]]] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[Momentum[p1], m1, 1].DiracGamma[x].Spinor[Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Fermion-fermion axial-vector chain , temporal component	*)
		TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[FMStandardSpinorChain["A",3,{p1,m1},{p2,m2}]]] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[Momentum[p1], m1, 1].DiracGamma[ExplicitLorentzIndex[0]].DiracGamma[5].Spinor[Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Fermion-fermion axial-vector chain , spatial component	*)
		CartesianPair[(x: _CartesianIndex | _CartesianMomentum),CartesianMomentum[FMStandardSpinorChain["A",3,{p1,m1},{p2,m2}]]] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[Momentum[p1], m1, 1].DiracGamma[x].DiracGamma[5].Spinor[Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],


		(*	Fermion-fermion tensor chain , temporal-spatial component	*)
		FMStandardSpinorChain["T",3,{p1,m1},{p2,m2},ExplicitLorentzIndex[0], (x: _CartesianIndex | _CartesianMomentum)] :>
			head[norm I ( FMSpinorChainExplicit2[Spinor[Momentum[p1], m1, 1].DiracGamma[ExplicitLorentzIndex[0]].DiracGamma[x].Spinor[Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],


		(*	Fermion-fermion tensor chain , spatial-spatial component	*)
		FMStandardSpinorChain["T",3,{p1,m1},{p2,m2},(x: _CartesianIndex | _CartesianMomentum), (y: _CartesianIndex | _CartesianMomentum)] :>
			(
			tmpci = CartesianIndex[$MU[Unique[]]];
			head[ norm (
					PauliXi[-I].PauliSigma[tmpci].PauliXi[I] Eps[x, y, tmpci] +
					(-I (CartesianPair[x, CartesianMomentum[p2]] CartesianPair[y, CartesianMomentum[p1]] - CartesianPair[x, CartesianMomentum[p1]] CartesianPair[y,CartesianMomentum[p2]]) PauliXi[-I].PauliXi[I] -
					PauliXi[-I].PauliSigma[CartesianMomentum[p2]].PauliXi[I] Eps[x, y, CartesianMomentum[p1]] -
					PauliXi[-I].PauliSigma[y].PauliXi[I] Eps[x, CartesianMomentum[p1], CartesianMomentum[p2]] -
					PauliXi[-I].PauliSigma[tmpci].PauliXi[I] (-CartesianPair[x, y] Eps[tmpci, CartesianMomentum[p1], CartesianMomentum[p2]] +
					CartesianPair[y, CartesianMomentum[p2]] Eps[x, tmpci, CartesianMomentum[p1]] - CartesianPair[x, CartesianMomentum[p1]] Eps[y, tmpci, CartesianMomentum[p2]]))(1/((m1 + p10) (m2 + p20)))
			)]),


		(*	----------------------------------------------------------------------------------	*)

		(*	Antifermion-antifermion scalar chain	*)
		FMStandardSpinorChain["S",4,{p1,m1},{p2,m2}] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[-Momentum[p1], m1, 1].Spinor[-Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Antifermion-antifermion pseudo-scalar chain	*)
		FMStandardSpinorChain["P",4,{p1,m1},{p2,m2}] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[-Momentum[p1], m1, 1].DiracGamma[5].Spinor[-Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Antifermion-antifermion vector chain , temporal component	*)
		TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[FMStandardSpinorChain["V",4,{p1,m1},{p2,m2}]]] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[-Momentum[p1], m1, 1].DiracGamma[ExplicitLorentzIndex[0]].Spinor[-Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Antifermion-antifermion vector chain , spatial component	*)
		CartesianPair[(x: _CartesianIndex | _CartesianMomentum),CartesianMomentum[FMStandardSpinorChain["V",4,{p1,m1},{p2,m2}]]] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[-Momentum[p1], m1, 1].DiracGamma[x].Spinor[-Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Antifermion-antifermion axial-vector chain , temporal component	*)
		TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[FMStandardSpinorChain["A",4,{p1,m1},{p2,m2}]]] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[-Momentum[p1], m1, 1].DiracGamma[ExplicitLorentzIndex[0]].DiracGamma[5].Spinor[-Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],

		(*	Antifermion-antifermion axial-vector chain , spatial component	*)
		CartesianPair[(x: _CartesianIndex | _CartesianMomentum),CartesianMomentum[FMStandardSpinorChain["A",4,{p1,m1},{p2,m2}]]] :>
			head[norm ( FMSpinorChainExplicit2[Spinor[-Momentum[p1], m1, 1].DiracGamma[x].DiracGamma[5].Spinor[-Momentum[p2], m2, 1], FMSpinorNormalization -> "omitted", FCI->True])],


		(*	Antifermion-antifermion tensor chain , temporal-spatial component	*)
		FMStandardSpinorChain["T",4,{p1,m1},{p2,m2},ExplicitLorentzIndex[0], (x: _CartesianIndex | _CartesianMomentum)] :>
			(
			tmpci = CartesianIndex[$MU[Unique[]]];
			head[I norm (
				(CartesianPair[x, CartesianMomentum[p1]] PauliEta[-I].PauliEta[I] -
				I Eps[x, CartesianMomentum[p1], tmpci] PauliEta[-I].PauliSigma[tmpci].PauliEta[I])/(p10+m1) -

				(CartesianPair[x, CartesianMomentum[p2]] PauliEta[-I].PauliEta[I] +
				I Eps[x, CartesianMomentum[p2], tmpci] PauliEta[-I].PauliSigma[tmpci].PauliEta[I])/(p20+m2)
			)]
			),


		(*	Antifermion-antifermion tensor chain , spatial-spatial component	*)
		FMStandardSpinorChain["T",4,{p1,m1},{p2,m2},(x: _CartesianIndex | _CartesianMomentum), (y: _CartesianIndex | _CartesianMomentum)] :>
			(
			tmpci = CartesianIndex[$MU[Unique[]]];
			head[ norm (

				-PauliEta[-I].PauliSigma[tmpci].PauliEta[I] Eps[x, y, tmpci] +

			(I (CartesianPair[x, CartesianMomentum[p2]] CartesianPair[y, CartesianMomentum[p1]] - CartesianPair[x, CartesianMomentum[p1]] CartesianPair[y, CartesianMomentum[p2]]) PauliEta[-I].PauliEta[I] +
				PauliEta[-I].PauliSigma[CartesianMomentum[p2]].PauliEta[I] Eps[x, y, CartesianMomentum[p1]] +
				PauliEta[-I].PauliSigma[y].PauliEta[I] Eps[x, CartesianMomentum[p1], CartesianMomentum[p2]] +
				PauliEta[-I].PauliSigma[tmpci].PauliEta[I] (-CartesianPair[x, y] Eps[tmpci, CartesianMomentum[p1], CartesianMomentum[p2]] +
				CartesianPair[y, CartesianMomentum[p2]] Eps[x, tmpci, CartesianMomentum[p1]] - CartesianPair[x, CartesianMomentum[p1]] Eps[y, tmpci, CartesianMomentum[p2]]))/((m1 + p10) (m2 + p20))
			)]
			)
		};

		res = res/. norm -> n1 n2 /. {p10 -> TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[p1]],
			p20 -> TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[p2]], p1p2 -> CartesianPair[CartesianMomentum[p1],CartesianMomentum[p2]]};

		res
	];



createBoostedChainRules[p1_,p2_, m1_, m2_, head_, P_, p1R_, p2R_, PR_]:=
	Block[{PR0, p1R0, p2R0, PVecSq},

		PR0 = TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[PR]];

		p1R0 = TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[p1R]];
		p2R0 = TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[p2R]];
		PVecSq = CartesianPair[CartesianMomentum[P],CartesianMomentum[P]];

	{

		(*	Boosted scalar or pseudo-scalar chain	*)
		(* 	A Lorentz scalar is  Lorentz invairant.
			A Lorentz pseudo-scalar, is Lorentz invairant under boosts and rotations. Parity inversions are not considered here *)
		FMStandardSpinorChain[st:"S"|"P",ii_,{p1,m1},{p2,m2}] ->
			head[(holdSpinorChains[st,ii,{p1R,m1},{p2R,m2}])],

		(*	Boosted vector or axial vector chain , temporal component	*)
		(* 	L^0_0 s1_R g^0 (g^5) s2_R + L^0_i s1_R g^i (g^5) s2_R, with
				L^0_0 = P0/PR0 L^0_i = P^i/PR0 *)
		TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[FMStandardSpinorChain[st:"V"|"A",ii_,{p1,m1},{p2,m2}]]] ->
			head[(
				(*1st term*)
				Sqrt[1+PVecSq/PR0^2] TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[holdSpinorChains[st,ii,{p1R,m1},{p2R,m2}]]] +
				(*2nd term*)
				(1/PR0)CartesianPair[CartesianMomentum[P],CartesianMomentum[holdSpinorChains[st,ii,{p1R,m1},{p2R,m2}]]]

			)],

		(*	Boosted vector or axial vector chain , spatial component	*)
		(* 	L^i_0 s1_R g^0 (g^5) s2_R + L^i_j s1_R g^j (g^5) s2_R, with
					L^i_0 = P^i/PR0
					L^i_j = delta^ij + (P0/P0R-1) Phat^i Phat^j	*)
		CartesianPair[(x: _CartesianIndex | _CartesianMomentum),CartesianMomentum[FMStandardSpinorChain[st:"V"|"A",ii_,{p1,m1},{p2,m2}]]] ->
			head[(
				(*1st term*)
					(CartesianPair[CartesianMomentum[P],x]/PR0) TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[holdSpinorChains[st,ii,{p1R,m1},{p2R,m2}]]] +
				(*2nd term*)
					CartesianPair[x,CartesianMomentum[holdSpinorChains[st,ii,{p1R,m1},{p2R,m2}]]] +
				(*3rd term*)
				(Sqrt[1+PVecSq/PR0^2] - 1)*(1/PVecSq)*CartesianPair[CartesianMomentum[P],x] CartesianPair[CartesianMomentum[P],CartesianMomentum[holdSpinorChains[st,ii,{p1R,m1},{p2R,m2}]]]
			)],


		(*	Boosted tensors chain , temporal-spatial component	*)
		FMStandardSpinorChain[st:"T",ii_,{p1,m1},{p2,m2}, ExplicitLorentzIndex[0], (x: _CartesianIndex | _CartesianMomentum)] ->
			head[(
				(*1st term*)
				Sqrt[1+PVecSq/PR0^2] holdSpinorChains[st,ii,{p1R,m1},{p2R,m2},ExplicitLorentzIndex[0], x] +
				(*2nd term*)
				1/(PR0) holdSpinorChains[st,ii,{p1R,m1},{p2R,m2},CartesianMomentum[P], x] +
				(*3rd term*)
				(1-Sqrt[1+PVecSq/PR0^2])/PVecSq CartesianPair[x,CartesianMomentum[P]] holdSpinorChains[st,ii,{p1R,m1},{p2R,m2},ExplicitLorentzIndex[0], CartesianMomentum[P]]
			)],

		(*	Boosted tensors chain , spatial-spatial component	*)
		FMStandardSpinorChain[st:"T",ii_,{p1,m1},{p2,m2}, (x: _CartesianIndex | _CartesianMomentum), (y: _CartesianIndex | _CartesianMomentum)] ->
			head[(
				(*1st term*)
				holdSpinorChains[st,ii,{p1R,m1},{p2R,m2}, x, y] +
				(*2nd term*)
				CartesianPair[CartesianMomentum[P],x]/(PR0) holdSpinorChains[st,ii,{p1R,m1},{p2R,m2},ExplicitLorentzIndex[0], y] -
				(*3rd term*)
				CartesianPair[CartesianMomentum[P],y]/(PR0) holdSpinorChains[st,ii,{p1R,m1},{p2R,m2},ExplicitLorentzIndex[0], x] +
				(*4th term*)
				CartesianPair[CartesianMomentum[P],x] (Sqrt[1+PVecSq/PR0^2]-1)/PVecSq holdSpinorChains[st,ii,{p1R,m1},{p2R,m2},CartesianMomentum[P],y] -
				(*5th term*)
				CartesianPair[CartesianMomentum[P],y] (Sqrt[1+PVecSq/PR0^2]-1)/PVecSq holdSpinorChains[st,ii,{p1R,m1},{p2R,m2},CartesianMomentum[P],x]
			)]

		}
	];

FCPrint[1,"FMSpinorChainsExplicit loaded."];
End[]
