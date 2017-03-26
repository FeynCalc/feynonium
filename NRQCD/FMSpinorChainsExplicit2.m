(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: FMSpinorChainExplicit2											*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2016 Vladyslav Shtabovenko
*)

(* :Summary:	Identifies standard 4D spinor chains to						*)

(* ------------------------------------------------------------------------ *)


FMSpinorChainExplicit2::usage =
"";

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

Options[FMSpinorChainExplicit2] = {
	Contract -> True,
	DiracGammaCombine -> True,
	DotSimplify -> True,
	EpsEvaluate -> True,
	FCI -> False,
	FMSpinorNormalization -> "relativistic",
	PauliTrick -> True,
	PowerExpand ->True,
	Collect -> True
};

FMSpinorChainExplicit2[expr_List, opts:OptionsPattern[]] :=
	Map[FMSpinorChainExplicit2[#,opts]&,expr];

FMSpinorChainExplicit2[expr_, OptionsPattern[]]:=
	Block[{ex, heads, tmp, res, null1,null2, repRule,
		diracObjects, diracObjectsEval, normRule,times},


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
			OptionValue[FMSpinorNormalization],
			"nonrelativistic",
				normRule  = {(n1|n2)[p_,m_] :> Sqrt[(TPair[TIndex[],TMomentum[p]]+ m)/(2 TPair[TIndex[],TMomentum[p]])] },
			"relativistic",
				normRule  = {(n1|n2)[p_,m_] :> Sqrt[(TPair[TIndex[],TMomentum[p]]+ m)] },
			"unspecified",
				normRule  = {n1[p_,m_] :> FCGV["N1"][p,m], n2[p_,m_] :> FCGV["N2"][p,m]  },
			_,
			Message[FMSpinorChainsExplicit2::failmsg, "Unknown normalization of Dirac spinors."];
			Abort[]
		];

		diracObjectsEval  = diracObjectsEval /. normRule;


		repRule = MapThread[Rule[#1, #2] &, {diracObjects, diracObjectsEval}];

		res = ex/.repRule /. times -> Times;

		If[ OptionValue[DotSimplify],
			res = res /.dsHead[x_] :> dsHead[DotSimplify[x,FCI->True]]
		];

		If[ OptionValue[PauliTrick],
			res = res /.dsHead[x_] :> dsHead[PauliTrick[x,FCI->True]]
		];

		If[ OptionValue[Contract],
			res = res /.dsHead[x_] :> dsHead[Contract[x,FCI->True]]
		];

		If[ OptionValue[EpsEvaluate],
			res = res /.dsHead[x_] :> dsHead[EpsEvaluate[x,FCI->True]]
		];

		If[	OptionValue[PowerExpand],
			res = res/. dsHead[x_]:> dsHead[Expand[PowerExpand[x]]]
		];

		If[	OptionValue[Collect],
			res = res/. dsHead[x_]:> dsHead[Collect2[x,{PauliXi,PauliEta}]]
		];

		res = res /. dsHead->Identity;


		res

	];

spinorRules = {
	(* ubar *)
	dotHold[Spinor[Momentum[p_, dim_:4], m_, 1],z___]/;!MatchQ[dim,_Symbol-4]:> n1[p,m] dotHold[{PauliXi[-I], -(PauliXi[-I].PauliSigma[CMomentum[p,dim-1],dim-1]/(m + TPair[TIndex[], TMomentum[p]]))},z],
	(* vbar *)
	dotHold[Spinor[-Momentum[p_, dim_:4], m_, 1],z___]/;!MatchQ[dim,_Symbol-4]:> n2[p,m] dotHold[{PauliEta[-I].PauliSigma[CMomentum[p,dim-1],dim-1]/(m + TPair[TIndex[], TMomentum[p]]), -PauliEta[-I]},z],
	(* u *)
	dotHold[z___,Spinor[Momentum[p_, dim_:4], m_, 1]]/;!MatchQ[dim,_Symbol-4]:> n1[p,m] dotHold[z,{{PauliXi[I]}, {PauliSigma[CMomentum[p,dim-1],dim-1].PauliXi[I]/(m + TPair[TIndex[], TMomentum[p]])}}],
	(* v *)
	dotHold[z___,Spinor[-Momentum[p_, dim_:4], m_, 1]]/;!MatchQ[dim,_Symbol-4]:> n1[p,m] dotHold[z,{{PauliSigma[CMomentum[p,dim-1],dim-1].PauliEta[I]/(m + TPair[TIndex[], TMomentum[p]])}, {PauliEta[I]}}]
};


diracGammaRules = {
	dotHold[z1___, coeff_. DiracGamma[x:(  _Momentum| _CMomentum| _LorentzIndex| _CIndex | _TIndex),dim_:4] + cc_:0, z2___]/;NonCommFreeQ[{cc,coeff}]:>
	( ind = CIndex[$MU[Unique[]],cDimSelect[dim]];
		dotHold[z1,{ {coeff FeynCalc`Package`MetricT Pair[x,TIndex[]]+cc,  coeff FeynCalc`Package`MetricS Pair[x,ind] PauliSigma[ind,cDimSelect[dim]]},
					{-coeff FeynCalc`Package`MetricS Pair[x,ind] PauliSigma[ind,cDimSelect[dim]], -coeff  FeynCalc`Package`MetricT Pair[x,TIndex[]]+cc}},z2]
	),
	dotHold[z1___, coeff_. DiracGamma[5] + cc_:0, z2___]/;NonCommFreeQ[{coeff,cc}]:>
		dotHold[z1,{ {0, 1}, {1, 0}},z2]
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
