(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: FMInsertCovariantProjector										*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2017 Vladyslav Shtabovenko
*)

(* :Summary:	Inserts covariant projectors of Bodwin and Petrelli			*)

(* ------------------------------------------------------------------------ *)


FMInsertCovariantProjector::usage =
"FMInsertCovariantProjector replaces spinor chains with covariant projectors \
of Bodwin and Petrelli from arXiv:hep-ph/0205210. \n
FMInsertCovariantProjector[expr, {p1,m}, {p2,m}, {col1,col2}] inserts spin singlet \
color singlet projector \n
FMInsertCovariantProjector[expr, {p1,m}, {p2,m}, Lor1, {col1,col2}] inserts spin triplet \
color singlet projector \n
FMInsertCovariantProjector[expr, {p1,m}, {p2,m}, {adjcol0, col1,col2}] inserts spin singlet \
color octet projector \n
FMInsertCovariantProjector[expr, {p1,m}, {p2,m}, Lor1, {adjcol0, col1,col2}] inserts spin triplet \
color octet projector
";

FMUseSimplifiedCovariantProjectors::usage=
"FMUseSimplifiedCovariantProjectors is an option for FMInsertCovariantProjector. \
When we are dealing with an exclusive process, where the only hadrons in the final \
state are the quarkonia, one can use simplified versions of color singlet projectors, \
valid to all orders in velocity, c.f. arXiv:0710.0995 for more details. Setting this \
option to True activates the usage of these projectors."

FMInsertCovariantProjector::failmsg =
"Error! FMInsertCovariantProjector has encountered a fatal problem and must abort the computation. \
The problem reads: `1`"


Begin["`Package`"]
End[]

Begin["`FMInsertCovariantProjector`Private`"]

holdSpinorChains::usage="";
normalization::usage="";
cpjVerbose::usage="";
optDim::usage="";
optFCI::usage="";
optSpinorNorm::usage="";
optFCE::usage="";
optSimplifiedProjectors::usage="";

Options[FMInsertCovariantProjector] = {
	Dimension -> D,
	FCE -> False,
	FCI -> False,
	FCVerbose -> False,
	FMSpinorNormalization -> "nonrelativistic",
	FMUseSimplifiedCovariantProjectors -> False
};

(*Sping singlet color singlet*)
FMInsertCovariantProjector[expr_, {p1_, m_}, {p2_, m_}/; !OptionQ[{p2,m}], {colFu1_, colFu2_}/; !OptionQ[{colFu1, colFu2}], OptionsPattern[]] :=
	Block[{},
		{optDim, optFCE, optFCI, cpjVerbose, optSpinorNorm, optSimplifiedProjectors} =
			{OptionValue[Dimension],OptionValue[FCE],OptionValue[FCI], OptionValue[FCVerbose],
				OptionValue[FMSpinorNormalization], OptionValue[FMUseSimplifiedCovariantProjectors]};
		covariantProjector[expr, {p1, m}, {p2, m}, 5, {colFu1, colFu2}]
	];

(*Sping triplet color singlet*)
FMInsertCovariantProjector[expr_, {p1_, m_}, {p2_, m_}, lorIndex_Symbol/; !OptionQ[lorIndex], {colFu1_, colFu2_}/; !OptionQ[{colFu1, colFu2}],  OptionsPattern[]] :=
	Block[{},
		{optDim, optFCE, optFCI, cpjVerbose, optSpinorNorm, optSimplifiedProjectors} =
			{OptionValue[Dimension],OptionValue[FCE],OptionValue[FCI], OptionValue[FCVerbose],
				OptionValue[FMSpinorNormalization], OptionValue[FMUseSimplifiedCovariantProjectors]};
		covariantProjector[expr, {p1, m}, {p2, m}, lorIndex, {colFu1, colFu2}]
	];

(*Sping singlet color octet*)
FMInsertCovariantProjector[expr_, {p1_, m_}, {p2_, m_}, {colAdj_, colFu1_, colFu2_}/; !OptionQ[{colAdj, colFu1, colFu2}], OptionsPattern[]] :=
	Block[{},
		{optDim, optFCE, optFCI, cpjVerbose, optSpinorNorm, optSimplifiedProjectors} =
			{OptionValue[Dimension],OptionValue[FCE],OptionValue[FCI], OptionValue[FCVerbose],
				OptionValue[FMSpinorNormalization], OptionValue[FMUseSimplifiedCovariantProjectors]};
		If[	optSimplifiedProjectors,
			Message[FMInsertCovariantProjector::failmsg,"Simplified covariant projectors cannot be used to extract color octet contributions."];
			Abort[]
		];
		covariantProjector[expr, {p1, m}, {p2, m}, 5, {colAdj, colFu1, colFu2}]
	];

(*Sping triplet color octet*)
FMInsertCovariantProjector[expr_, {p1_, m_}, {p2_, m_}, lorIndex_Symbol, {colAdj_, colFu1_, colFu2_}/; !OptionQ[{colAdj, colFu1, colFu2}], OptionsPattern[]] :=
	Block[{},
		{optDim, optFCE, optFCI, cpjVerbose, optSpinorNorm, optSimplifiedProjectors} =
			{OptionValue[Dimension],OptionValue[FCE],OptionValue[FCI], OptionValue[FCVerbose],
				OptionValue[FMSpinorNormalization], OptionValue[FMUseSimplifiedCovariantProjectors]};
		If[	optSimplifiedProjectors,
			Message[FMInsertCovariantProjector::failmsg,"Simplified covariant projectors cannot be used to extract color octet contributions."];
			Abort[]
		];
		covariantProjector[expr, {p1, m}, {p2, m}, lorIndex, {colAdj, colFu1, colFu2}]
	];


covariantProjector[expr_, {p1_, m_}, {p2_, m_}, diracGammaIndex_, colors_List] :=
	Block[{ex, holdDOT, P, En, ruleProjectors, ruleSimplifiedProjectors, res, norm, colorProj, mark, ga, sign},


		If[	diracGammaIndex===5,
			ga = DiracGamma[5];
			sign = 1,
			If[ optSimplifiedProjectors,
				ga = DiracGamma[LorentzIndex[diracGammaIndex,optDim],optDim] - Pair[Momentum[p1-p2, optDim],LorentzIndex[diracGammaIndex,optDim]]/(2 (En+m)),
				ga = DiracGamma[LorentzIndex[diracGammaIndex,optDim],optDim]
			];
			sign = -1
		];

		If [cpjVerbose===False,
			cpjVerbose=$VeryVerbose
		];

		FCPrint[1,"FMInsertCovariantProjector: Entering.", FCDoControl->cpjVerbose];
		FCPrint[3,"FMInsertCovariantProjector: Entering with: ", expr, FCDoControl->cpjVerbose];

		If[ !optFCI,
			ex = FCI[expr],
			ex = expr
		];

		P = p1 + p2;
		En = (TemporalPair[ExplicitLorentzIndex[0], TemporalMomentum[p1]] + TemporalPair[ExplicitLorentzIndex[0], TemporalMomentum[p2]]) /2;

		ruleProjectors = {
			(* decay, vbar (p2) ... u (p1) *)
			holdDOT[Spinor[-Momentum[p2, ___], m, ___], z___, Spinor[Momentum[p1, ___], m, ___]] /; FreeQ[{z}, Spinor] :>
				sign/(4 Sqrt[2] En(En + m)) DiracTrace[holdDOT[DiracGamma[Momentum[p1, optDim], optDim] + m,
				DiracGamma[Momentum[P, optDim], optDim] + 2 En, ga, DiracGamma[Momentum[p2, optDim], optDim] - m, z]] norm colorProj mark,
			(* production, ubar(p1) ... v (p2) *)
			holdDOT[Spinor[Momentum[p1, ___], m, ___], z___, Spinor[-Momentum[p2, ___], m, ___]] /; FreeQ[{z}, Spinor] :>
				sign/(4 Sqrt[2] En(En + m)) DiracTrace[holdDOT[DiracGamma[Momentum[p2, optDim], optDim] - m,
				ga, DiracGamma[Momentum[P, optDim], optDim] + 2 En, DiracGamma[Momentum[p1, optDim], optDim] + m, z]] norm colorProj mark
		};

		ruleSimplifiedProjectors = {
			(* decay, vbar (p2) ... u (p1) *)
			holdDOT[Spinor[-Momentum[p2, ___], m, ___], z___, Spinor[Momentum[p1, ___], m, ___]] /; FreeQ[{z}, Spinor] :>
				sign/(2 Sqrt[2] En) DiracTrace[holdDOT[DiracGamma[Momentum[p1, optDim], optDim] + m,
				ga, DiracGamma[Momentum[p2, optDim], optDim] - m, z]] norm colorProj mark,
			(* production, ubar(p1) ... v (p2) *)
			holdDOT[Spinor[Momentum[p1, ___], m, ___], z___, Spinor[-Momentum[p2, ___], m, ___]] /; FreeQ[{z}, Spinor] :>
				sign/(2 Sqrt[2] En) DiracTrace[holdDOT[DiracGamma[Momentum[p2, optDim], optDim] - m,
				ga, DiracGamma[Momentum[p1, optDim], optDim] + m, z]] norm colorProj mark
		};

		ex = ex /. DOT -> holdDOT;
		If[	optSimplifiedProjectors,
			ex = ex /. ruleSimplifiedProjectors /. holdDOT -> DOT,
			ex = ex /. ruleProjectors /. holdDOT -> DOT
		];

		FCPrint[3,"FMInsertCovariantProjector: Intermediate result ", ex, FCDoControl->cpjVerbose];

		If[	FreeQ[ex,mark],
			Message[FMInsertCovariantProjector::failmsg, "Unable to identify suitable spinor chains."];
			Abort[]
		];

		Switch[
			optSpinorNorm,
			"nonrelativistic",
				ex = ex /. norm -> 1/(2 En),
			"relativistic",
				ex = ex /. norm -> 1,
			"unspecified",
				ex = ex /. norm ->  FCGV["N"],
			_,
			Message[FMInsertCovariantProjector::failmsg, "Unknown normalization of Dirac spinors."];
			Abort[]
		];

		Switch[
			colors,
			{_,_,_},
				ex = ex /. colorProj -> Sqrt[2] SUNTF[{colors[[1]]},colors[[2]],colors[[3]]],
			{_,_},
				ex = ex /. colorProj -> 1/Sqrt[SUNN] SUNFDelta[SUNFIndex[colors[[1]]],SUNFIndex[colors[[2]]]],
			_,
			Message[FMInsertCovariantProjector::failmsg, "Unknown color configuration."];
			Abort[]
		];

		res = ex /. mark -> 1;

		If[	optFCE,
			res = FCE[res]
		];

		FCPrint[1,"FMInsertCovariantProjector: Leaving.", FCDoControl->cpjVerbose];
		FCPrint[3,"FMInsertCovariantProjector: Leaving with: ", res, FCDoControl->cpjVerbose];


		res
	];



FCPrint[1,"FMInsertCovariantProjector loaded."];
End[]
