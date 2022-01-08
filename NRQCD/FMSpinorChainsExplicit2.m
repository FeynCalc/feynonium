(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: FMSpinorChainExplicit2											*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2021 Vladyslav Shtabovenko
*)

(* :Summary:	Identifies standard 4D spinor chains to						*)

(* ------------------------------------------------------------------------ *)


FMSpinorChainExplicit2::usage =
"FMSpinorChainsExplicit[exp] rewrites all Dirac spinor chains present in the \
expression in terms of Pauli matrices and spinors. The energies and momenta \
appearing inside the spinors remain unchanged. ";

FMSpinorChainExplicit2::failmsg =
"Error! FMSpinorChainsExplicit has encountered a fatal problem and must abort the computation. \
The problem reads: `1`"

Begin["`Package`"]
End[]

Begin["`FMSpinorChainExplicit2`Private`"]

dsHead::usage="";
dotHold::usage="";
n1::usage="";
n2::usage="";
ind::usage="";
sce2Verbose::usage="";

Options[FMSpinorChainExplicit2] = {
	Collecting 			-> True,
	Contract 			-> True,
	DiracGammaCombine	-> True,
	DotSimplify			-> True,
	EpsEvaluate			-> True,
	FCI					-> False,
	FCVerbose			-> False,
	FMNormalization		-> "relativistic",
	PauliTrick			-> True,
	PowerExpand			-> True
};

FMSpinorChainExplicit2[expr_List, opts:OptionsPattern[]] :=
	Map[FMSpinorChainExplicit2[#,opts]&,expr];

FMSpinorChainExplicit2[expr_, OptionsPattern[]]:=
	Block[{ex, heads, tmp, res, null1,null2, repRule,
		diracObjects, diracObjectsEval, normRule,times,time},


		If [OptionValue[FCVerbose]===False,
			sce2Verbose=$VeryVerbose,
			If[MatchQ[OptionValue[FCVerbose], _Integer],
				sce2Verbose=OptionValue[FCVerbose]
			];
		];


		If[ !OptionValue[FCI],
			ex = FCI[expr],
			ex = expr
		];

		If[ FreeQ[ex,Spinor],
			Return[ex]
		];

		ex = FCDiracIsolate[ex,FCI->True,Head->dsHead, DotSimplify->True, DiracGammaCombine->OptionValue[DiracGammaCombine],DiracTrace->False];

		ex = ex /. z_dsHead/; FreeQ[z,Spinor] :> Identity@@z;

		ex = powerExpand[ex,dsHead,times];

		If[!FreeQ[ex,times],
			Message[FMSpinorChainExplicit2::failmsg,"Power of spinor chains are currently unsupported"];
			Abort[]
		];

		diracObjects = Cases[ex+null1+null2, dsHead[_], Infinity]//DeleteDuplicates//Sort;

		diracObjectsEval = diracObjects /. dsHead[x_]/;!FreeQ[x,DiracSigma] :> dsHead[DiracSigmaExplicit[x,FCI->True]];



		diracObjectsEval = diracObjectsEval  /.DOT -> dotHold //. spinorRules //. diracGammaRules /. dotHold -> FMBlockMatrixProduct;

		If[	!FreeQ2[diracObjectsEval,{DiracGamma,Spinor}],
			Message[FMSpinorChainsExplicit2::failmsg, "Failed to insert explicit form for all matrices and spinors."];
			Abort[]
		];

		Switch[
			OptionValue[FMNormalization],
			"nonrelativistic",
				normRule  = {(n1|n2)[p_,m_] :> Sqrt[(TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[p]]+ m)/(2 TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[p]])] },
			"relativistic",
				normRule  = {(n1|n2)[p_,m_] :> Sqrt[(TemporalPair[ExplicitLorentzIndex[0],TemporalMomentum[p]]+ m)] },
			"unspecified",
				normRule  = {n1[p_,m_] :> FCGV["N1"][p,m], n2[p_,m_] :> FCGV["N2"][p,m]  },
			"omitted",
				normRule  = {(n1|n2)[_,_] -> 1},
			_,
			Message[FMSpinorChainsExplicit2::failmsg, "Unknown normalization of Dirac spinors."];
			Abort[]
		];

		diracObjectsEval  = diracObjectsEval /. normRule;
		repRule = Thread[Rule[diracObjects, diracObjectsEval]];

		res = ex /. Dispatch[repRule] /. times -> Times;

		If[ OptionValue[DotSimplify],
			time = AbsoluteTime[];
			FCPrint[1, "FMSpinorChainsExplicit2: Applying DotSimplify.", FCDoControl->sce2Verbose];
			res = res /.dsHead[x_] :> dsHead[DotSimplify[x,FCI->True]];
			FCPrint[1, "FMSpinorChainsExplicit2: Done applying DotSimplify, timing: ",  N[AbsoluteTime[] - time, 4], FCDoControl->sce2Verbose]
		];

		If[ OptionValue[PauliTrick],
			time = AbsoluteTime[];
			FCPrint[1, "FMSpinorChainsExplicit2: Applying PauliTrick.", FCDoControl->sce2Verbose];
			res = res /.dsHead[x_] :> dsHead[PauliTrick[x,FCI->True]];
			FCPrint[1, "FMSpinorChainsExplicit2: Done applying PauliTrick, timing: ",  N[AbsoluteTime[] - time, 4], FCDoControl->sce2Verbose]
		];

		If[ OptionValue[Contract],
			time = AbsoluteTime[];
			FCPrint[1, "FMSpinorChainsExplicit2: Applying Contract.", FCDoControl->sce2Verbose];
			res = res /.dsHead[x_] :> dsHead[Contract[x,FCI->True]];
			FCPrint[1, "FMSpinorChainsExplicit2: Done applying Contract, timing: ",  N[AbsoluteTime[] - time, 4], FCDoControl->sce2Verbose]
		];

		If[ OptionValue[EpsEvaluate],
			time = AbsoluteTime[];
			FCPrint[1, "FMSpinorChainsExplicit2: Applying EpsEvaluate.", FCDoControl->sce2Verbose];
			res = res /.dsHead[x_] :> dsHead[EpsEvaluate[x,FCI->True]];
			FCPrint[1, "FMSpinorChainsExplicit2: Done applying EpsEvaluate, timing: ",  N[AbsoluteTime[] - time, 4], FCDoControl->sce2Verbose]
		];

		If[	OptionValue[PowerExpand],
			time = AbsoluteTime[];
			FCPrint[1, "FMSpinorChainsExplicit2: Applying PowerExpand.", FCDoControl->sce2Verbose];
			res = res/. dsHead[x_]:> dsHead[Expand[PowerExpand[x]]];
			FCPrint[1, "FMSpinorChainsExplicit2: Done applying PowerExpand, timing: ",  N[AbsoluteTime[] - time, 4], FCDoControl->sce2Verbose]
		];

		If[	OptionValue[Collecting],
			time = AbsoluteTime[];
			FCPrint[1, "FMSpinorChainsExplicit2: Applying Collect.", FCDoControl->sce2Verbose];
			res = res/. dsHead[x_]:> dsHead[Collect2[x,{PauliXi,PauliEta}]];
			FCPrint[1, "FMSpinorChainsExplicit2: Done applying Collect, timing: ",  N[AbsoluteTime[] - time, 4], FCDoControl->sce2Verbose]
		];

		res = res /. dsHead->Identity;


		res

	];

spinorRules = {
	(* ubar *)
	dotHold[Spinor[Momentum[p_, dim_:4], m_, 1],z___]/;!MatchQ[dim,_Symbol-4]:> n1[p,m] dotHold[{PauliXi[-I], -(PauliXi[-I].PauliSigma[CartesianMomentum[p,dim-1],dim-1]/(m + TemporalPair[ExplicitLorentzIndex[0], TemporalMomentum[p]]))},z],
	(* vbar *)
	dotHold[Spinor[-Momentum[p_, dim_:4], m_, 1],z___]/;!MatchQ[dim,_Symbol-4]:> n2[p,m] dotHold[{PauliEta[-I].PauliSigma[CartesianMomentum[p,dim-1],dim-1]/(m + TemporalPair[ExplicitLorentzIndex[0], TemporalMomentum[p]]), -PauliEta[-I]},z],
	(* u *)
	dotHold[z___,Spinor[Momentum[p_, dim_:4], m_, 1]]/;!MatchQ[dim,_Symbol-4]:> n1[p,m] dotHold[z,{{PauliXi[I]}, {PauliSigma[CartesianMomentum[p,dim-1],dim-1].PauliXi[I]/(m + TemporalPair[ExplicitLorentzIndex[0], TemporalMomentum[p]])}}],
	(* v *)
	dotHold[z___,Spinor[-Momentum[p_, dim_:4], m_, 1]]/;!MatchQ[dim,_Symbol-4]:> n2[p,m] dotHold[z,{{PauliSigma[CartesianMomentum[p,dim-1],dim-1].PauliEta[I]/(m + TemporalPair[ExplicitLorentzIndex[0], TemporalMomentum[p]])}, {PauliEta[I]}}]
};


diracGammaRules = {
	dotHold[z1___, coeff_. DiracGamma[x:(  _Momentum| _CartesianMomentum| _LorentzIndex| _CartesianIndex | _ExplicitLorentzIndex),dim_:4] + cc_:0, z2___]/;NonCommFreeQ[{cc,coeff}]:>
	( ind = CartesianIndex[$MU[Unique[]],cDimSelect[dim]];
		dotHold[z1,{ {coeff FeynCalc`Package`MetricT Pair[x,ExplicitLorentzIndex[0]]+cc,  coeff FeynCalc`Package`MetricS Pair[x,ind] PauliSigma[ind,cDimSelect[dim]]},
					{-coeff FeynCalc`Package`MetricS Pair[x,ind] PauliSigma[ind,cDimSelect[dim]], -coeff  FeynCalc`Package`MetricT Pair[x,ExplicitLorentzIndex[0]]+cc}},z2]
	),
	dotHold[z1___, coeff_. DiracGamma[5] + cc_:0, z2___]/;NonCommFreeQ[{coeff,cc}]:>
		dotHold[z1,coeff { {0, 1}, {1, 0}} + cc,z2],

	dotHold[z1___, coeff_. DiracGamma[6] + cc_:0, z2___]/;NonCommFreeQ[{coeff,cc}]:>
		dotHold[z1, 1/2 coeff { {1, 1}, {1, 1}} + cc,z2],

	dotHold[z1___, coeff_. DiracGamma[7] + cc_:0, z2___]/;NonCommFreeQ[{coeff,cc}]:>
		dotHold[z1, 1/2 coeff { {1, -1}, {-1, 1}} + cc,z2]
};

cDimSelect[d_Symbol]:=
	d-1;

cDimSelect[d_Symbol-4]:=
	d-4;

cDimSelect[4]:=
	3;

powerExpand[ex_, head_, times_]:=
	ex /. Power[Pattern[z,Blank[head]], n_Integer?Positive] :>
		Apply[times, Table[z, {Abs[n]}]]^Sign[n]/; !FreeQ[ex,Power];

powerExpand[ex_, _, _, _]:=
	ex/; FreeQ[ex,Power];

FCPrint[1,"FMSpinorChainExplicit2 loaded."];
End[]
