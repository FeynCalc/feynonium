(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: FMToFMStandardSpinorChains											*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2020 Vladyslav Shtabovenko
*)

(* :Summary:	Identifies standard 4D spinor chains to						*)

(* ------------------------------------------------------------------------ *)


FMToStandardSpinorChains::usage =
"FMToStandardSpinorChains[expr] identifies basic spinor chains in 4-dimensions \
which are scalar, pseudoscalar, vector, axial-vector and tensor (SPVAT). The \
function should be applied after DiracReduce.";

Begin["`Package`"]
End[]

Begin["`FMToFMStandardSpinorChains`Private`"]

dsHead::usage="";

Options[FMToStandardSpinorChains] = {
	DiracGammaCombine	-> True,
	FCI 				-> False
};

FMToStandardSpinorChains[expr_List, opts:OptionsPattern[]] :=
	Map[FMToStandardSpinorChains[#,opts]&,expr];

FMToStandardSpinorChains[expr_, OptionsPattern[]]:=
	Block[{ex, heads, tmp, res, null1,null2, repRule,
		diracObjects, diracObjectsEval},


		If[ !OptionValue[FCI],
			ex = FCI[expr],
			ex = expr
		];

		If[ FreeQ[ex,Spinor],
			Return[ex]
		];


		ex = FCDiracIsolate[ex,FCI->True,Head->dsHead, DotSimplify->True, DiracGammaCombine->OptionValue[DiracGammaCombine],DiracTrace->False];

		diracObjects = Cases[ex+null1+null2, dsHead[_], Infinity]//DeleteDuplicates//Sort;


		diracObjectsEval =diracObjects/.Dispatch[convRules]/.dsHead->Identity;

		repRule = Thread[Rule[diracObjects, diracObjectsEval]];
		res = ex /. Dispatch[repRule];

		res

	];

convRules = {

			(* SCALAR *)
			(* ubar g^mu v *)
			dsHead[Spinor[Momentum[p1_], m1_, 1].Spinor[-Momentum[p2_], m2_, 1]] :>
				FMStandardSpinorChain["S",1,{p1,m1},{p2,m2}],
			(* vbar g^mu u *)
			dsHead[Spinor[-Momentum[p1_], m1_, 1].Spinor[Momentum[p2_], m2_, 1]] :>
				FMStandardSpinorChain["S",2,{p1,m1},{p2,m2}],
			(* ubar g^mu u *)
			dsHead[Spinor[Momentum[p1_], m1_, 1].Spinor[Momentum[p2_], m2_, 1]] :>
				FMStandardSpinorChain["S",3,{p1,m1},{p2,m2}],
			(* vbar g^mu v *)
			dsHead[Spinor[-Momentum[p1_], m1_, 1].Spinor[-Momentum[p2_], m2_, 1]] :>
				FMStandardSpinorChain["S",4,{p1,m1},{p2,m2}],

			(* PSEUDO-SCALAR *)
			(* ubar g^mu v *)
			dsHead[Spinor[Momentum[p1_], m1_, 1].DiracGamma[5].Spinor[-Momentum[p2_], m2_, 1]] :>
				FMStandardSpinorChain["P",1,{p1,m1},{p2,m2}],
			(* vbar g^mu u *)
			dsHead[Spinor[-Momentum[p1_], m1_, 1].DiracGamma[5].Spinor[Momentum[p2_], m2_, 1]] :>
				FMStandardSpinorChain["P",2,{p1,m1},{p2,m2}],
			(* ubar g^mu u *)
			dsHead[Spinor[Momentum[p1_], m1_, 1].DiracGamma[5].Spinor[Momentum[p2_], m2_, 1]] :>
				FMStandardSpinorChain["P",3,{p1,m1},{p2,m2}],
			(* vbar g^mu v *)
			dsHead[Spinor[-Momentum[p1_], m1_, 1].DiracGamma[5].Spinor[-Momentum[p2_], m2_, 1]] :>
				FMStandardSpinorChain["P",4,{p1,m1},{p2,m2}],

			(* VECTOR *)
			(* ubar g^mu v *)
			dsHead[Spinor[Momentum[p1_], m1_, 1].DiracGamma[x_].Spinor[-Momentum[p2_], m2_, 1]] :>
				Pair[Momentum[FMStandardSpinorChain["V",1,{p1,m1},{p2,m2}]],x],
			(* vbar g^mu u *)
			dsHead[Spinor[-Momentum[p1_], m1_, 1].DiracGamma[x_].Spinor[Momentum[p2_], m2_, 1]] :>
				Pair[Momentum[FMStandardSpinorChain["V",2,{p1,m1},{p2,m2}]],x],
			(* ubar g^mu u *)
			dsHead[Spinor[Momentum[p1_], m1_, 1].DiracGamma[x_].Spinor[Momentum[p2_], m2_, 1]] :>
				Pair[Momentum[FMStandardSpinorChain["V",3,{p1,m1},{p2,m2}]],x],
			(* vbar g^mu v *)
			dsHead[Spinor[-Momentum[p1_], m1_, 1].DiracGamma[x_].Spinor[-Momentum[p2_], m2_, 1]] :>
				Pair[Momentum[FMStandardSpinorChain["V",4,{p1,m1},{p2,m2}]],x],

			(* AXIAL-VECTOR *)
			(* ubar g^mu v *)
			dsHead[Spinor[Momentum[p1_], m1_, 1].DiracGamma[x_].DiracGamma[5].Spinor[-Momentum[p2_], m2_, 1]] :>
				Pair[Momentum[FMStandardSpinorChain["A",1,{p1,m1},{p2,m2}]],x],
			(* vbar g^mu u *)
			dsHead[Spinor[-Momentum[p1_], m1_, 1].DiracGamma[x_].DiracGamma[5].Spinor[Momentum[p2_], m2_, 1]] :>
				Pair[Momentum[FMStandardSpinorChain["A",2,{p1,m1},{p2,m2}]],x],
			(* ubar g^mu u *)
			dsHead[Spinor[Momentum[p1_], m1_, 1].DiracGamma[x_].DiracGamma[5].Spinor[Momentum[p2_], m2_, 1]] :>
				Pair[Momentum[FMStandardSpinorChain["A",3,{p1,m1},{p2,m2}]],x],
			(* vbar g^mu v *)
			dsHead[Spinor[-Momentum[p1_], m1_, 1].DiracGamma[x_].DiracGamma[5].Spinor[-Momentum[p2_], m2_, 1]] :>
				Pair[Momentum[FMStandardSpinorChain["A",4,{p1,m1},{p2,m2}]],x],


			(* TENSOR *)
			(* ubar g^mu v *)
			dsHead[Spinor[Momentum[p1_], m1_, 1].DiracSigma[DiracGamma[x_],DiracGamma[y_]].Spinor[-Momentum[p2_], m2_, 1]] :>
				FMStandardSpinorChain["T",1,{p1,m1},{p2,m2},x,y],
			(* vbar g^mu u *)
			dsHead[Spinor[-Momentum[p1_], m1_, 1].DiracSigma[DiracGamma[x_],DiracGamma[y_]].Spinor[Momentum[p2_], m2_, 1]] :>
				FMStandardSpinorChain["T",2,{p1,m1},{p2,m2},x,y],
			(* ubar g^mu u *)
			dsHead[Spinor[Momentum[p1_], m1_, 1].DiracSigma[DiracGamma[x_],DiracGamma[y_]].Spinor[Momentum[p2_], m2_, 1]] :>
				FMStandardSpinorChain["T",3,{p1,m1},{p2,m2},x,y],
			(* vbar g^mu v *)
			dsHead[Spinor[-Momentum[p1_], m1_, 1].DiracSigma[DiracGamma[x_],DiracGamma[y_]].Spinor[-Momentum[p2_], m2_, 1]] :>
				FMStandardSpinorChain["T",4,{p1,m1},{p2,m2},x,y]
		};

FCPrint[1,"FMToStandardSpinorChains loaded."];
End[]
