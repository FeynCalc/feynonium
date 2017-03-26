(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: FMSpinorChainsExplicit												*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2016 Vladyslav Shtabovenko
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
(*
		P = FCGV["Jacobi P"];
		q = FCGV["Jacobi Q"];

		(* q1 and q2 are the soft or ultrasoft scales defined in the rest frame of the QQbarG system *)
		q1 = FCGV["Quarkonium q1"];
		q2 = FCGV["Quarkonium q2"];

		(* Q1 and Q2 are related to q1 and q2 through a Lorentz transformation *)
		Q1 = FCGV["Quarkonium Q1"];
		Q2 = FCGV["Quarkonium Q2"];
*)

		(* p1R and p2R are the 3-momenta of p1 and p2 in the rest frame of the QQbarG system *)
	(*	p1R = q1-q2;
		p2R = -q1-q2;
		(* p1R0 and p2R0 are the energies of p1 and p2 in the rest frame of the QQbarG system *)
		p1R0 = Sqrt[CPair[CMomentum[p1R],CMomentum[p1R]] + mass^2];
		p2R0 = Sqrt[CPair[CMomentum[p2R],CMomentum[p2R]] + mass^2];*)

		(* P_R^0 is the temporal component of P in the rest frame of the QQbarG system *)
	(*	PR0 = (	p1R0+ p2R0+ 2 Sqrt[CPair[CMomentum[q2], CMomentum[q2]]]);*)
(*

		p1p2 = CPair[CMomentum[p1],CMomentum[p2]];


		P0 = TPair[TIndex[],TMomentum[P]];

		Eq = Sqrt[NRPair[Momentum[q],Momentum[q]] + mass^2];
		PVecSq = NRPair[Momentum[P],Momentum[P]];
		SqP2 = Sqrt[Pair[Momentum[P],Momentum[P]]];
*)

		(*
		p10 = TPair[TIndex[],TMomentum[p1]];
		p20 = TPair[TIndex[],TMomentum[p2]];
		*)
		ruleTwoBodyRestFrameKinematics = {
			CMomentum[p1] -> CMomentum[FCGV["Jacobi QR"]],
			CMomentum[p2] -> -CMomentum[FCGV["Jacobi QR"]],
			TPair[TIndex[],TMomentum[p1]] -> Sqrt[m1^2 + CPair[CMomentum[FCGV["Jacobi QR"]],CMomentum[FCGV["Jacobi QR"]]]],
			TPair[TIndex[],TMomentum[p2]] -> Sqrt[m2^2 + CPair[CMomentum[FCGV["Jacobi QR"]],CMomentum[FCGV["Jacobi QR"]]]]
		};

		ruleThreeBodyRestFrameKinematics = {
			CMomentum[p1] -> CMomentum[FCGV["Jacobi Q1R"]]-CMomentum[FCGV["Jacobi Q2R"]],
			CMomentum[p2] -> -CMomentum[FCGV["Jacobi Q1R"]]-CMomentum[FCGV["Jacobi Q2R"]],
			TPair[TIndex[],TMomentum[p1]] -> Sqrt[m1^2 +
				CPair[CMomentum[FCGV["Jacobi Q1R"]]-CMomentum[FCGV["Jacobi Q2R"]],CMomentum[FCGV["Jacobi Q1R"]]-CMomentum[FCGV["Jacobi Q2R"]]]],
			TPair[TIndex[],TMomentum[p2]] -> Sqrt[m2^2 +
				CPair[CMomentum[FCGV["Jacobi Q1R"]]+CMomentum[FCGV["Jacobi Q2R"]],CMomentum[FCGV["Jacobi Q1R"]]+CMomentum[FCGV["Jacobi Q2R"]]]]
		};

		ruleTwoBodyLabFrameKinematics = {
			CMomentum[p1R] -> CMomentum[FCGV["Jacobi QR"]],
			CMomentum[p2R] -> -CMomentum[FCGV["Jacobi QR"]],
			TPair[TIndex[],TMomentum[p1R]] -> Sqrt[m1^2 + CPair[CMomentum[FCGV["Jacobi QR"]],CMomentum[FCGV["Jacobi QR"]]]],
			TPair[TIndex[],TMomentum[p2R]] -> Sqrt[m2^2 + CPair[CMomentum[FCGV["Jacobi QR"]],CMomentum[FCGV["Jacobi QR"]]]],
			TPair[TIndex[],TMomentum[PR]] -> (	Sqrt[m1^2 + CPair[CMomentum[FCGV["Jacobi QR"]],CMomentum[FCGV["Jacobi QR"]]]]+
												Sqrt[m2^2 + CPair[CMomentum[FCGV["Jacobi QR"]],CMomentum[FCGV["Jacobi QR"]]]]),
			CMomentum[P] -> CMomentum[FCGV["Jacobi P"]]
		};

		ruleThreeBodyLabFrameKinematics = {
			CMomentum[p1R] -> CMomentum[FCGV["Jacobi Q1R"]]-CMomentum[FCGV["Jacobi Q2R"]],
			CMomentum[p2R] -> -CMomentum[FCGV["Jacobi Q1R"]]-CMomentum[FCGV["Jacobi Q2R"]],
			TPair[TIndex[],TMomentum[p1R]] -> Sqrt[m1^2 +
				CPair[CMomentum[FCGV["Jacobi Q1R"]]-CMomentum[FCGV["Jacobi Q2R"]],CMomentum[FCGV["Jacobi Q1R"]]-CMomentum[FCGV["Jacobi Q2R"]]]],
			TPair[TIndex[],TMomentum[p2R]] -> Sqrt[m2^2 +
				CPair[CMomentum[FCGV["Jacobi Q1R"]]+CMomentum[FCGV["Jacobi Q2R"]],CMomentum[FCGV["Jacobi Q1R"]]+CMomentum[FCGV["Jacobi Q2R"]]]],

			TPair[TIndex[],TMomentum[PR]] -> ( Sqrt[4 CPair[CMomentum[FCGV["Jacobi Q2R"]],CMomentum[FCGV["Jacobi Q2R"]]] + FCGV["m3"]^2] +

				Sqrt[m1^2 +
				CPair[CMomentum[FCGV["Jacobi Q1R"]]-CMomentum[FCGV["Jacobi Q2R"]],CMomentum[FCGV["Jacobi Q1R"]]-CMomentum[FCGV["Jacobi Q2R"]]]] +

				Sqrt[m2^2 +
				CPair[CMomentum[FCGV["Jacobi Q1R"]]+CMomentum[FCGV["Jacobi Q2R"]],CMomentum[FCGV["Jacobi Q1R"]]+CMomentum[FCGV["Jacobi Q2R"]]]]

			),

			CMomentum[P] -> CMomentum[FCGV["Jacobi P"]]

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

		(*If[	!FreeQ[res,FMStandardSpinorChain],
			Message[FMSpinorChainsExplicit::failmsg,"Failed to substitute all spinor chains."];
			Abort[]
		];*)

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
			head[norm (
				- PauliXi[-I].PauliSigma[CMomentum[p1]].PauliEta[I]/(p10+m1) +
				PauliXi[-I].PauliSigma[CMomentum[p2]].PauliEta[I]/(p20+m2)
			)],

		(*	Production pseudo-scalar chain	*)
		FMStandardSpinorChain["P",1,{p1,m1},{p2,m2}] :>
			(
			tmpci = CIndex[$MU[Unique[]]];
			head[norm (
				PauliXi[-I].PauliEta[I] -
				(p1p2 PauliXi[-I].PauliEta[I] +
				I Eps[tmpci, CMomentum[p1], CMomentum[p2]] PauliXi[-I].PauliSigma[tmpci].PauliEta[I])/((p10+m1)(p20+m2))
			)]),


		(*	Production vector chain , temporal component	*)
		TPair[TIndex[],TMomentum[FMStandardSpinorChain["V",1,{p1,m1},{p2,m2}]]] :>
			head[norm (
				PauliXi[-I].PauliSigma[CMomentum[p1]].PauliEta[I]/(p10+m1) +
				PauliXi[-I].PauliSigma[CMomentum[p2]].PauliEta[I]/(p20+m2)
			)],
		(*	Production vector chain , spatial component	*)
		CPair[(x: _CIndex | _CMomentum),CMomentum[FMStandardSpinorChain["V",1,{p1,m1},{p2,m2}]]] :>
			head[norm (
				PauliXi[-I].PauliSigma[x].PauliEta[I] +	(
					CPair[x, CMomentum[p1]] PauliXi[-I].PauliSigma[CMomentum[p2]].PauliEta[I] +
					CPair[x, CMomentum[p2]] PauliXi[-I].PauliSigma[CMomentum[p1]].PauliEta[I] -
					p1p2 PauliXi[-I].PauliSigma[x].PauliEta[I] -
					I PauliXi[-I].PauliEta[I] Eps[x,CMomentum[p1],CMomentum[p2]])/((p10+m1)(p20+m2))
			)],

		(*	Production axial-vector chain , temporal component	*)
		TPair[TIndex[],TMomentum[FMStandardSpinorChain["A",1,{p1,m1},{p2,m2}]]] :>
			(
			tmpci = CIndex[$MU[Unique[]]];
			head[norm (
				PauliXi[-I].PauliEta[I] +
				(p1p2 PauliXi[-I].PauliEta[I] +
				I Eps[tmpci, CMomentum[p1], CMomentum[p2]] PauliXi[-I].PauliSigma[tmpci].PauliEta[I])/((p10+m1)(p20+m2))
			)]),

		(*	Production axial-vector chain , spatial component	*)
		CPair[(x: _CIndex | _CMomentum),CMomentum[FMStandardSpinorChain["A",1,{p1,m1},{p2,m2}]]] :>
			(
			tmpci = CIndex[$MU[Unique[]]];
			head[norm (
				(CPair[x, CMomentum[p1]] PauliXi[-I].PauliEta[I] -
				I Eps[x, CMomentum[p1], tmpci] PauliXi[-I].PauliSigma[tmpci].PauliEta[I])/(p10+m1) +

				(CPair[x, CMomentum[p2]] PauliXi[-I].PauliEta[I] +
				I Eps[x, CMomentum[p2], tmpci] PauliXi[-I].PauliSigma[tmpci].PauliEta[I])/(p20+m2)
			)]
			),


		(*	Production tensor chain , temporal-spatial component	*)
		FMStandardSpinorChain["T",1,{p1,m1},{p2,m2},TIndex[], (x: _CIndex | _CMomentum)] :>
			head[I norm (
				PauliXi[-I].PauliSigma[x].PauliEta[I] -	(
					CPair[x, CMomentum[p1]] PauliXi[-I].PauliSigma[CMomentum[p2]].PauliEta[I] +
					CPair[x, CMomentum[p2]] PauliXi[-I].PauliSigma[CMomentum[p1]].PauliEta[I] -
					p1p2 PauliXi[-I].PauliSigma[x].PauliEta[I] -
					I Eps[x,CMomentum[p1],CMomentum[p2]])/((p10+m1)(p20+m2))
			)],


		(*	Production tensor chain , spatial-spatial component	*)
		FMStandardSpinorChain["T",1,{p1,m1},{p2,m2},(x: _CIndex | _CMomentum), (y: _CIndex | _CMomentum)] :>
			head[I norm (

				(CPair[x, CMomentum[p1]]  PauliXi[-I].PauliSigma[y].PauliEta[I] -
				CPair[y, CMomentum[p1]]  PauliXi[-I].PauliSigma[x].PauliEta[I] +
				I Eps[CMomentum[p1],x,y] PauliXi[-I].PauliEta[I])/(p10+m1) -

				(CPair[y, CMomentum[p2]]  PauliXi[-I].PauliSigma[x].PauliEta[I] -
				CPair[x, CMomentum[p2]]  PauliXi[-I].PauliSigma[y].PauliEta[I] +
				I Eps[CMomentum[p2],x,y] PauliXi[-I].PauliEta[I])/(p20+m2)
			)],

		(*	----------------------------------------------------------------------------------	*)

		(*	Decay scalar chain	*)
		FMStandardSpinorChain["S",2,{p1,m1},{p2,m2}] :>
			head[norm (
				PauliEta[-I].PauliSigma[CMomentum[p1]].PauliXi[I]/(p10+m1) -
				PauliEta[-I].PauliSigma[CMomentum[p2]].PauliXi[I]/(p20+m2)
			)],

		(*	Decay pseudo-scalar chain	*)
		FMStandardSpinorChain["P",2,{p1,m1},{p2,m2}] :>
			(
			tmpci = CIndex[$MU[Unique[]]];
			head[norm (
				-PauliEta[-I].PauliXi[I] +
				(p1p2 PauliEta[-I].PauliXi[I] +
				I Eps[tmpci, CMomentum[p1], CMomentum[p2]] PauliEta[-I].PauliSigma[tmpci].PauliXi[I])/((p10+m1)(p20+m2))
			)]),

		(*	Decay vector chain , temporal component	*)
		TPair[TIndex[],TMomentum[FMStandardSpinorChain["V",2,{p1,m1},{p2,m2}]]] :>
			head[norm (
				PauliEta[-I].PauliSigma[CMomentum[p1]].PauliXi[I]/(p10+m1) +
				PauliEta[-I].PauliSigma[CMomentum[p2]].PauliXi[I]/(p20+m2)
			)],
		(*	Decay vector chain , spatial component	*)
		CPair[(x: _CIndex | _CMomentum),CMomentum[FMStandardSpinorChain["V",2,{p1,m1},{p2,m2}]]] :>
			head[norm (
				PauliEta[-I].PauliSigma[x].PauliXi[I] +	(
					CPair[x, CMomentum[p1]] PauliEta[-I].PauliSigma[CMomentum[p2]].PauliXi[I] +
					CPair[x, CMomentum[p2]] PauliEta[-I].PauliSigma[CMomentum[p1]].PauliXi[I] -
					p1p2 PauliEta[-I].PauliSigma[x].PauliXi[I] -
					I PauliEta[-I].PauliXi[I] Eps[x,CMomentum[p1],CMomentum[p2]])/((p10+m1)(p20+m2))
			)],

		(*	Decay axial-vector chain , temporal component	*)
		TPair[TIndex[],TMomentum[FMStandardSpinorChain["A",2,{p1,m1},{p2,m2}]]] :>
			(
			tmpci = CIndex[$MU[Unique[]]];
			head[norm (
				PauliEta[-I].PauliXi[I] +
				(p1p2 PauliEta[-I].PauliXi[I] +
				I Eps[tmpci, CMomentum[p1], CMomentum[p2]] PauliEta[-I].PauliSigma[tmpci].PauliXi[I])/((p10+m1)(p20+m2))
			)]),

		(*	Decay axial-vector chain , spatial component	*)
		CPair[(x: _CIndex | _CMomentum),CMomentum[FMStandardSpinorChain["A",2,{p1,m1},{p2,m2}]]] :>
			(
			tmpci = CIndex[$MU[Unique[]]];
			head[norm (
				(CPair[x, CMomentum[p1]] PauliEta[-I].PauliXi[I] -
				I Eps[x, CMomentum[p1], tmpci] PauliEta[-I].PauliSigma[tmpci].PauliXi[I])/(p10+m1) +

				(CPair[x, CMomentum[p2]] PauliEta[-I].PauliXi[I] +
				I Eps[x, CMomentum[p2], tmpci] PauliEta[-I].PauliSigma[tmpci].PauliXi[I])/(p20+m2)
			)]
			),


		(*	Decay tensor chain , temporal-spatial component	*)
		FMStandardSpinorChain["T",2,{p1,m1},{p2,m2},TIndex[], (x: _CIndex | _CMomentum)] :>
			head[-I norm (
				PauliEta[-I].PauliSigma[x].PauliXi[I] -	(
					CPair[x, CMomentum[p1]] PauliEta[-I].PauliSigma[CMomentum[p2]].PauliXi[I] +
					CPair[x, CMomentum[p2]] PauliEta[-I].PauliSigma[CMomentum[p1]].PauliXi[I] -
					p1p2 PauliEta[-I].PauliSigma[x].PauliXi[I] -
					I PauliEta[-I].PauliXi[I] Eps[x,CMomentum[p1],CMomentum[p2]])/((p10+m1)(p20+m2))
			)],


		(*	Decay tensor chain , spatial-spatial component	*)
		FMStandardSpinorChain["T",2,{p1,m1},{p2,m2},(x: _CIndex | _CMomentum), (y: _CIndex | _CMomentum)] :>
			head[-I norm (

				(CPair[x, CMomentum[p1]]  PauliEta[-I].PauliSigma[y].PauliXi[I] -
				CPair[y, CMomentum[p1]]  PauliEta[-I].PauliSigma[x].PauliXi[I] +
				I Eps[CMomentum[p1],x,y] PauliEta[-I].PauliXi[I])/(p10+m1) -

				(CPair[y, CMomentum[p2]]  PauliEta[-I].PauliSigma[x].PauliXi[I] -
				CPair[x, CMomentum[p2]]  PauliEta[-I].PauliSigma[y].PauliXi[I] +
				I Eps[CMomentum[p2],x,y] PauliEta[-I].PauliXi[I])/(p20+m2)
			)],

		(*	----------------------------------------------------------------------------------	*)

		(*	Fermion-fermion scalar chain	*)
		FMStandardSpinorChain["S",3,{p1,m1},{p2,m2}] :>
			(
			tmpci = CIndex[$MU[Unique[]]];
			head[norm (
				PauliXi[-I].PauliXi[I] -
				(p1p2 PauliXi[-I].PauliXi[I] +
				I Eps[tmpci, CMomentum[p1], CMomentum[p2]] PauliXi[-I].PauliSigma[tmpci].PauliXi[I])/((p10+m1)(p20+m2))
			)]),

		(*	Fermion-fermion pseudo-scalar chain	*)
		FMStandardSpinorChain["P",3,{p1,m1},{p2,m2}] :>
			head[norm (
				-PauliXi[-I].PauliSigma[CMomentum[p1]].PauliXi[I]/(p10+m1) +
				PauliXi[-I].PauliSigma[CMomentum[p2]].PauliXi[I]/(p20+m2)
			)],

		(*	Fermion-fermion vector chain , temporal component	*)
		TPair[TIndex[],TMomentum[FMStandardSpinorChain["V",3,{p1,m1},{p2,m2}]]] :>
			(
			tmpci = CIndex[$MU[Unique[]]];
			head[norm (
				PauliXi[-I].PauliXi[I] +
				(p1p2 PauliXi[-I].PauliXi[I] +
				I Eps[tmpci, CMomentum[p1], CMomentum[p2]] PauliXi[-I].PauliSigma[tmpci].PauliXi[I])/((p10+m1)(p20+m2))
			)]),

		(*	Fermion-fermion vector chain , spatial component	*)
		CPair[(x: _CIndex | _CMomentum),CMomentum[FMStandardSpinorChain["V",3,{p1,m1},{p2,m2}]]] :>
			(
			tmpci = CIndex[$MU[Unique[]]];
			head[ norm (
				(CPair[x, CMomentum[p1]] PauliXi[-I].PauliXi[I] -
				I Eps[x, CMomentum[p1], tmpci] PauliXi[-I].PauliSigma[tmpci].PauliXi[I])/(p10+m1) +

				(CPair[x, CMomentum[p2]] PauliXi[-I].PauliXi[I] +
				I Eps[x, CMomentum[p2], tmpci] PauliXi[-I].PauliSigma[tmpci].PauliXi[I])/(p20+m2)
			)]
			),

		(*	Fermion-fermion axial-vector chain , temporal component	*)
		TPair[TIndex[],TMomentum[FMStandardSpinorChain["A",3,{p1,m1},{p2,m2}]]] :>
			head[norm (
				PauliXi[-I].PauliSigma[CMomentum[p1]].PauliXi[I]/(p10+m1) +
				PauliXi[-I].PauliSigma[CMomentum[p2]].PauliXi[I]/(p20+m2)
			)],

		(*	Fermion-fermion axial-vector chain , spatial component	*)
		CPair[(x: _CIndex | _CMomentum),CMomentum[FMStandardSpinorChain["A",3,{p1,m1},{p2,m2}]]] :>
			head[ norm (
				PauliXi[-I].PauliSigma[x].PauliXi[I] +	(
					CPair[x, CMomentum[p1]] PauliXi[-I].PauliSigma[CMomentum[p2]].PauliXi[I] +
					CPair[x, CMomentum[p2]] PauliXi[-I].PauliSigma[CMomentum[p1]].PauliXi[I] -
					p1p2 PauliXi[-I].PauliSigma[x].PauliXi[I] -
					PauliXi[-I].PauliXi[I] I Eps[x,CMomentum[p1],CMomentum[p2]])/((p10+m1)(p20+m2))
			)],


		(*	Fermion-fermion tensor chain , temporal-spatial component	*)
		FMStandardSpinorChain["T",3,{p1,m1},{p2,m2},TIndex[], (x: _CIndex | _CMomentum)] :>
			(
			tmpci = CIndex[$MU[Unique[]]];
			head[-I norm (
				(CPair[x, CMomentum[p1]] PauliXi[-I].PauliXi[I] -
				I Eps[x, CMomentum[p1], tmpci] PauliXi[-I].PauliSigma[tmpci].PauliXi[I])/(p10+m1) -

				(CPair[x, CMomentum[p2]] PauliXi[-I].PauliXi[I] +
				I Eps[x, CMomentum[p2], tmpci] PauliXi[-I].PauliSigma[tmpci].PauliXi[I])/(p20+m2)
			)]
			),


		(*	Fermion-fermion tensor chain , spatial-spatial component	*)
		FMStandardSpinorChain["T",3,{p1,m1},{p2,m2},(x: _CIndex | _CMomentum), (y: _CIndex | _CMomentum)] :>
			(
			tmpci = CIndex[$MU[Unique[]]];
			head[ norm (
					PauliXi[-I].PauliSigma[tmpci].PauliXi[I] Eps[x, y, tmpci] +
					(-I (CPair[x, CMomentum[p2]] CPair[y, CMomentum[p1]] - CPair[x, CMomentum[p1]] CPair[y,CMomentum[p2]]) PauliXi[-I].PauliXi[I] -
					PauliXi[-I].PauliSigma[CMomentum[p2]].PauliXi[I] Eps[x, y, CMomentum[p1]] -
					PauliXi[-I].PauliSigma[y].PauliXi[I] Eps[x, CMomentum[p1], CMomentum[p2]] -
					PauliXi[-I].PauliSigma[tmpci].PauliXi[I] (-CPair[x, y] Eps[tmpci, CMomentum[p1], CMomentum[p2]] +
					CPair[y, CMomentum[p2]] Eps[x, tmpci, CMomentum[p1]] - CPair[x, CMomentum[p1]] Eps[y, tmpci, CMomentum[p2]]))(1/((m1 + p10) (m2 + p20)))
			)]),


		(*	----------------------------------------------------------------------------------	*)

		(*	Antifermion-antifermion scalar chain	*)
		FMStandardSpinorChain["S",4,{p1,m1},{p2,m2}] :>
			(
			tmpci = CIndex[$MU[Unique[]]];
			head[norm (
				-PauliEta[-I].PauliEta[I] +
				(p1p2 PauliEta[-I].PauliEta[I] +
				I Eps[tmpci, CMomentum[p1], CMomentum[p2]] PauliEta[-I].PauliSigma[tmpci].PauliEta[I])/((p10+m1)(p20+m2))
			)]),

		(*	Antifermion-antifermion pseudo-scalar chain	*)
		FMStandardSpinorChain["P",4,{p1,m1},{p2,m2}] :>
			head[norm (
				PauliEta[-I].PauliSigma[CMomentum[p1]].PauliEta[I]/(p10+m1) -
				PauliEta[-I].PauliSigma[CMomentum[p2]].PauliEta[I]/(p20+m2)
			)],

		(*	Antifermion-antifermion vector chain , temporal component	*)
		TPair[TIndex[],TMomentum[FMStandardSpinorChain["V",4,{p1,m1},{p2,m2}]]] :>
			(
			tmpci = CIndex[$MU[Unique[]]];
			head[norm (
				PauliEta[-I].PauliEta[I] +
				(p1p2 PauliEta[-I].PauliEta[I] +
				I Eps[tmpci, CMomentum[p1], CMomentum[p2]] PauliEta[-I].PauliSigma[tmpci].PauliEta[I])/((p10+m1)(p20+m2))
			)]),

		(*	Antifermion-antifermion vector chain , spatial component	*)
		CPair[(x: _CIndex | _CMomentum),CMomentum[FMStandardSpinorChain["V",4,{p1,m1},{p2,m2}]]] :>
			(
			tmpci = CIndex[$MU[Unique[]]];
			head[norm (
				(CPair[x, CMomentum[p1]] PauliEta[-I].PauliEta[I] -
				I Eps[x, CMomentum[p1], tmpci] PauliEta[-I].PauliSigma[tmpci].PauliEta[I])/(p10+m1) +

				(CPair[x, CMomentum[p2]] PauliEta[-I].PauliEta[I] +
				I Eps[x, CMomentum[p2], tmpci] PauliEta[-I].PauliSigma[tmpci].PauliEta[I])/(p20+m2)
			)]
			),

		(*	Antifermion-antifermion axial-vector chain , temporal component	*)
		TPair[TIndex[],TMomentum[FMStandardSpinorChain["A",4,{p1,m1},{p2,m2}]]] :>
			head[norm (
				PauliEta[-I].PauliSigma[CMomentum[p1]].PauliEta[I]/(p10+m1) +
				PauliEta[-I].PauliSigma[CMomentum[p2]].PauliEta[I]/(p20+m2)
			)],

		(*	Antifermion-antifermion axial-vector chain , spatial component	*)
		CPair[(x: _CIndex | _CMomentum),CMomentum[FMStandardSpinorChain["A",4,{p1,m1},{p2,m2}]]] :>
			head[norm (
				PauliEta[-I].PauliSigma[x].PauliEta[I] +	(
					CPair[x, CMomentum[p1]] PauliEta[-I].PauliSigma[CMomentum[p2]].PauliEta[I] +
					CPair[x, CMomentum[p2]] PauliEta[-I].PauliSigma[CMomentum[p1]].PauliEta[I] -
					p1p2 PauliEta[-I].PauliSigma[x].PauliEta[I] -
					I PauliEta[-I].PauliEta[I] Eps[x,CMomentum[p1],CMomentum[p2]])/((p10+m1)(p20+m2))
			)],


		(*	Antifermion-antifermion tensor chain , temporal-spatial component	*)
		FMStandardSpinorChain["T",4,{p1,m1},{p2,m2},TIndex[], (x: _CIndex | _CMomentum)] :>
			(
			tmpci = CIndex[$MU[Unique[]]];
			head[I norm (
				(CPair[x, CMomentum[p1]] PauliEta[-I].PauliEta[I] -
				I Eps[x, CMomentum[p1], tmpci] PauliEta[-I].PauliSigma[tmpci].PauliEta[I])/(p10+m1) -

				(CPair[x, CMomentum[p2]] PauliEta[-I].PauliEta[I] +
				I Eps[x, CMomentum[p2], tmpci] PauliEta[-I].PauliSigma[tmpci].PauliEta[I])/(p20+m2)
			)]
			),


		(*	Antifermion-antifermion tensor chain , spatial-spatial component	*)
		FMStandardSpinorChain["T",4,{p1,m1},{p2,m2},(x: _CIndex | _CMomentum), (y: _CIndex | _CMomentum)] :>
			(
			tmpci = CIndex[$MU[Unique[]]];
			head[ norm (

				-PauliEta[-I].PauliSigma[tmpci].PauliEta[I] Eps[x, y, tmpci] +

			(I (CPair[x, CMomentum[p2]] CPair[y, CMomentum[p1]] - CPair[x, CMomentum[p1]] CPair[y, CMomentum[p2]]) PauliEta[-I].PauliEta[I] +
				PauliEta[-I].PauliSigma[CMomentum[p2]].PauliEta[I] Eps[x, y, CMomentum[p1]] +
				PauliEta[-I].PauliSigma[y].PauliEta[I] Eps[x, CMomentum[p1], CMomentum[p2]] +
				PauliEta[-I].PauliSigma[tmpci].PauliEta[I] (-CPair[x, y] Eps[tmpci, CMomentum[p1], CMomentum[p2]] +
				CPair[y, CMomentum[p2]] Eps[x, tmpci, CMomentum[p1]] - CPair[x, CMomentum[p1]] Eps[y, tmpci, CMomentum[p2]]))/((m1 + p10) (m2 + p20))
			)]
			)
		};

		res = res/. norm -> n1 n2 /. {p10 -> TPair[TIndex[],TMomentum[p1]],
			p20 -> TPair[TIndex[],TMomentum[p2]], p1p2 -> CPair[CMomentum[p1],CMomentum[p2]]};

		res
	];



createBoostedChainRules[p1_,p2_, m1_, m2_, head_, P_, p1R_, p2R_, PR_]:=
	Block[{PR0, p1R0, p2R0, PVecSq},

		PR0 = TPair[TIndex[],TMomentum[PR]];

		p1R0 = TPair[TIndex[],TMomentum[p1R]];
		p2R0 = TPair[TIndex[],TMomentum[p2R]];
		PVecSq = CPair[CMomentum[P],CMomentum[P]];

	{

		(*	Boosted scalar or pseudo-scalar chain	*)
		(* 	A Lorentz scalar is  Lorentz invairant.
			A Lorentz pseudo-scalar, is Lorentz invairant under boosts and rotations. Parity inversions are not considered here *)
		FMStandardSpinorChain[st:"S"|"P",ii_,{p1,m1},{p2,m2}] ->
			head[(holdSpinorChains[st,ii,{p1R,m1},{p2R,m2}])],

		(*	Boosted vector or axial vector chain , temporal component	*)
		(* 	L^0_0 s1_R g^0 (g^5) s2_R + L^0_i s1_R g^i (g^5) s2_R, with
				L^0_0 = P0/PR0 L^0_i = P^i/PR0 *)
		TPair[TIndex[],TMomentum[FMStandardSpinorChain[st:"V"|"A",ii_,{p1,m1},{p2,m2}]]] ->
			head[(
				(*1st term*)
				Sqrt[1+PVecSq/PR0^2] TPair[TIndex[],TMomentum[holdSpinorChains[st,ii,{p1R,m1},{p2R,m2}]]] +
				(*2nd term*)
				(1/PR0)CPair[CMomentum[P],CMomentum[holdSpinorChains[st,ii,{p1R,m1},{p2R,m2}]]]

			)],

		(*	Boosted vector or axial vector chain , spatial component	*)
		(* 	L^i_0 s1_R g^0 (g^5) s2_R + L^i_j s1_R g^j (g^5) s2_R, with
					L^i_0 = P^i/PR0
					L^i_j = delta^ij + (P0/P0R-1) Phat^i Phat^j	*)
		CPair[(x: _CIndex | _CMomentum),CMomentum[FMStandardSpinorChain[st:"V"|"A",ii_,{p1,m1},{p2,m2}]]] ->
			head[(
				(*1st term*)
					(CPair[CMomentum[P],x]/PR0) TPair[TIndex[],TMomentum[holdSpinorChains[st,ii,{p1R,m1},{p2R,m2}]]] +
				(*2nd term*)
					CPair[x,CMomentum[holdSpinorChains[st,ii,{p1R,m1},{p2R,m2}]]] +
				(*3rd term*)
				(Sqrt[1+PVecSq/PR0^2] - 1)*(1/PVecSq)*CPair[CMomentum[P],x] CPair[CMomentum[P],CMomentum[holdSpinorChains[st,ii,{p1R,m1},{p2R,m2}]]]
			)],


		(*	Boosted tensors chain , temporal-spatial component	*)
		FMStandardSpinorChain[st:"T",ii_,{p1,m1},{p2,m2}, TIndex[], (x: _CIndex | _CMomentum)] ->
			head[(
				(*1st term*)
				Sqrt[1+PVecSq/PR0^2] holdSpinorChains[st,ii,{p1R,m1},{p2R,m2},TIndex[], x] +
				(*2nd term*)
				1/(PR0) holdSpinorChains[st,ii,{p1R,m1},{p2R,m2},CMomentum[P], x] +
				(*3rd term*)
				(1-Sqrt[1+PVecSq/PR0^2])/PVecSq CPair[x,CMomentum[P]] holdSpinorChains[st,ii,{p1R,m1},{p2R,m2},TIndex[], CMomentum[P]]
			)],

		(*	Boosted tensors chain , spatial-spatial component	*)
		FMStandardSpinorChain[st:"T",ii_,{p1,m1},{p2,m2}, (x: _CIndex | _CMomentum), (y: _CIndex | _CMomentum)] ->
			head[(
				(*1st term*)
				holdSpinorChains[st,ii,{p1R,m1},{p2R,m2}, x, y] +
				(*2nd term*)
				CPair[CMomentum[P],x]/(PR0) holdSpinorChains[st,ii,{p1R,m1},{p2R,m2},TIndex[], y] -
				(*3rd term*)
				CPair[CMomentum[P],y]/(PR0) holdSpinorChains[st,ii,{p1R,m1},{p2R,m2},TIndex[], x] +
				(*4th term*)
				CPair[CMomentum[P],x] (Sqrt[1+PVecSq/PR0^2]-1)/PVecSq holdSpinorChains[st,ii,{p1R,m1},{p2R,m2},CMomentum[P],y] -
				(*5th term*)
				CPair[CMomentum[P],y] (Sqrt[1+PVecSq/PR0^2]-1)/PVecSq holdSpinorChains[st,ii,{p1R,m1},{p2R,m2},CMomentum[P],x]
			)]

		}
	];

FCPrint[1,"FMSpinorChainsExplicit loaded."];
End[]
