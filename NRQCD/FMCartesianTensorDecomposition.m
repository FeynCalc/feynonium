(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: FMCartesianTensorDecomposition									*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2020 Vladyslav Shtabovenko
*)

(* :Summary:	Projects different J values out of Cartesian tensors		*)

(* ------------------------------------------------------------------------ *)


FMCartesianTensorDecomposition::usage =
"FMCartesianTensorDecomposition[expr, {v1,v2,...}, J] projects our angular
momenta J out of tensors that are built from the vectors v1, v2, ... .";

FMCartesianTensorDecomposition::failmsg =
"Error! Uncontract has encountered a fatal problem and must abort the computation. \
The problem reads: `1`"

Begin["`Package`"]
End[]

Begin["`FMCartesianTensorDecomposition`Private`"]

ctdVerbose::usage="";

projHead::usage="";

tensorProjRule0::usage="";
tensorProjRule1::usage="";
tensorProjRule2::usage="";

Options[FMCartesianTensorDecomposition] = {
	Contract -> True,
	FCE -> False,
	FCI -> False,
	FCVerbose -> False,
	Factoring -> Factor,
	Collecting -> True
};

FMCartesianTensorDecomposition[expr_List, rest__] :=
	Map[FMCartesianTensorDecomposition[#,rest]&,expr];

FMCartesianTensorDecomposition[expr_, vecs_List, j:Except[_?OptionQ], OptionsPattern[]]:=
	Block[{ex, heads, tmp, tmpUnc, res, null1,null2, repRule, projList,
			projListEval, projRepRule, finalRepRule, tensorProjRule},

		If [OptionValue[FCVerbose]===False,
			ctdVerbose=$VeryVerbose,
			If[MatchQ[OptionValue[FCVerbose], _Integer],
				ctdVerbose=OptionValue[FCVerbose]
			];
		];

		If[ !OptionValue[FCI],
			ex = FCI[expr],
			ex = expr
		];

		If[	FreeQ2[ex,vecs],
			Return[ex]
		];

		tmp = Uncontract[ex, Sequence@@vecs, CartesianPair -> All, FCI->True];

		FCPrint[1, "FMCartesianTensorDecomposition: After Uncontract: ", tmp, FCDoControl->ctdVerbose];

		tmpUnc = FCLoopIsolate[tmp, vecs, Head -> projHead, FCI->True,
			FeynAmpDenominatorSplit->False, DiracGammaExpand->False, DotSimplify->False, PaVe->False];

		FCPrint[1, "FMCartesianTensorDecomposition: After FCLoopIsolate: ", tmpUnc, FCDoControl->ctdVerbose];

		If[	!FreeQ2[tmpUnc/. _projHead:>Unique[],vecs],
			Message[FMCartesianTensorDecomposition::failmsg,"Failed to isolate all relevant vectors."];
			Abort[];

		];

		projList = Cases[tmpUnc+null1+null2, _projHead, Infinity]//DeleteDuplicates//Sort;

		FCPrint[1, "FMCartesianTensorDecomposition: projList: ", projList, FCDoControl->ctdVerbose];

		If[ !MatchQ[projList/.Times->List/. projHead[z_CartesianPair]:>projHead[{z}],{projHead[{__CartesianPair}]..}],
			Message[FMCartesianTensorDecomposition::failmsg,"Incorrect structure of Cartesian tensors."];
			Abort[];
		];

		If[ FCGetDimensions[projList]=!={3},
			Message[FMCartesianTensorDecomposition::failmsg, "Projections in other than 3 dimensions are not supported."];
			Abort[];
		];

		projListEval = projList /. CartesianPair -> CartesianPairContract /. CartesianPairContract -> CartesianPair //. projHead[CartesianPair[a__CartesianMomentum]^n_. b_.] :> CartesianPair[a]^n projHead[b] /.
		projHead[]|projHead[1]->1;

		FCPrint[1, "FMCartesianTensorDecomposition: projListEval: ", projListEval, FCDoControl->ctdVerbose];

		(*	If all the vectors are already contracted with each other
			and we are not taking the J=0 projection, then all other projections give zero. *)
		If[	j=!=0,
			tmpUnc=FCSplit[tmpUnc,{projHead}][[2]]
		];


		Switch[ j,
			0,
				tensorProjRule = tensorProjRule0,
			1,
				tensorProjRule = tensorProjRule1,
			2,
				tensorProjRule = tensorProjRule2,
			_,
			Message[FMCartesianTensorDecomposition::failmsg,"Decompositions for J>2 are currently not implemented."];
			Abort[]
		];

		projListEval = projListEval /. tensorProjRule;

		finalRepRule = Thread[Rule[projList,projListEval]];

		res = tmpUnc /. finalRepRule;

		If[	OptionValue[Contract],
			res = Contract[res,FCI->True]
		];

		If[	OptionValue[Collecting],
			res = Collect2[res,vecs, Factoring->OptionValue[Factoring]]
		];

		If[	OptionValue[FCE],
			res = FCE[res]
		];

		res


	]/; IntegerQ[j] && j>=0;

tensorProjRule0 = {
	(* Rank 1*)
	projHead[CartesianPair[_CartesianIndex, _CartesianMomentum ]] :>0,

	(* Rank 2*)
	projHead[CartesianPair[i1_CartesianIndex, m1_CartesianMomentum ] CartesianPair[i2_CartesianIndex, m2_CartesianMomentum]] :>
		CartesianPair[m1,m2] CartesianPair[i1,i2]/3,

	(* Rank 3*)
	projHead[CartesianPair[i1_CartesianIndex, m1_CartesianMomentum ] CartesianPair[i2_CartesianIndex, m2_CartesianMomentum] CartesianPair[i3_CartesianIndex, m3_CartesianMomentum]] :>
		-(CartesianPair[i1, m3]*CartesianPair[i2, m2]*CartesianPair[i3, m1])/6 + (CartesianPair[i1, m2]*CartesianPair[i2, m3]*CartesianPair[i3, m1])/6 +
		(CartesianPair[i1, m3]*CartesianPair[i2, m1]*CartesianPair[i3, m2])/6 - (CartesianPair[i1, m1]*CartesianPair[i2, m3]*CartesianPair[i3, m2])/6 -
		(CartesianPair[i1, m2]*CartesianPair[i2, m1]*CartesianPair[i3, m3])/6 + (CartesianPair[i1, m1]*CartesianPair[i2, m2]*CartesianPair[i3, m3])/6,

	(* Rank 4*)
	projHead[CartesianPair[i1_CartesianIndex, m1_CartesianMomentum ] CartesianPair[i2_CartesianIndex, m2_CartesianMomentum] CartesianPair[i3_CartesianIndex, m3_CartesianMomentum] CartesianPair[i4_CartesianIndex, m4_CartesianMomentum]] :>
		(2*CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/15 -
		(CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/30 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/30 -
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/30 +
		(2*CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/15 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/30 -
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/30 -
		(CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/30 +
		(2*CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/15,

	(* Rank 5*)
	projHead[CartesianPair[i1_CartesianIndex, m1_CartesianMomentum ] CartesianPair[i2_CartesianIndex, m2_CartesianMomentum] CartesianPair[i3_CartesianIndex, m3_CartesianMomentum]*
		CartesianPair[i4_CartesianIndex, m4_CartesianMomentum] CartesianPair[i5_CartesianIndex, m5_CartesianMomentum]] :>
		-(CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/30 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m4]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/30 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/30 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m5]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/30 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/30 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m4]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/30 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m4]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/10 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/30 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m5]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/30 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m5]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/10 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/30 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m3]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/30 -
		(CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/30 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m5]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/30 -
		(CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/30 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m3]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/30 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m3]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/10 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/30 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m5]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/30 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m5]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/10 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/30 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m3]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/30 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/30 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m4]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/30 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/30 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m3]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/30 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m3]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/10 -
		(CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/30 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m4]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/30 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m4]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/10 -
		(CartesianPair[i1, m5]*CartesianPair[i2, m4]*CartesianPair[i3, i4]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/30 +
		(CartesianPair[i1, m4]*CartesianPair[i2, m5]*CartesianPair[i3, i4]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/30 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m4]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/30 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m5]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/30 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/30 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m4]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/10 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m4]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/30 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/30 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m5]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/10 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m5]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/30 +
		(CartesianPair[i1, m5]*CartesianPair[i2, m2]*CartesianPair[i3, i4]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/30 -
		(CartesianPair[i1, m2]*CartesianPair[i2, m5]*CartesianPair[i3, i4]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/30 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m2]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/30 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m5]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/30 -
		(CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/30 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m2]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/10 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m2]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/30 +
		(CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/30 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m5]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/10 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, m5]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/30 -
		(CartesianPair[i1, m4]*CartesianPair[i2, m2]*CartesianPair[i3, i4]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/30 +
		(CartesianPair[i1, m2]*CartesianPair[i2, m4]*CartesianPair[i3, i4]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/30 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m2]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/30 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m4]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/30 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/30 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m2]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/10 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m2]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/30 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/30 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m4]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/10 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, m4]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/30 -
		(CartesianPair[i1, m5]*CartesianPair[i2, m3]*CartesianPair[i3, i4]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/30 +
		(CartesianPair[i1, m3]*CartesianPair[i2, m5]*CartesianPair[i3, i4]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/30 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/30 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m3]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/10 -
		(CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/30 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m5]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/10 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m3]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/30 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m3]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/30 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m5]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/30 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m5]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/30 +
		(CartesianPair[i1, m5]*CartesianPair[i2, m2]*CartesianPair[i3, i4]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/30 -
		(CartesianPair[i1, m2]*CartesianPair[i2, m5]*CartesianPair[i3, i4]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/30 -
		(CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/30 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m2]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/10 +
		(CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/30 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m5]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/10 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m2]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/30 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m2]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/30 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m5]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/30 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, m5]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/30 -
		(CartesianPair[i1, m3]*CartesianPair[i2, m2]*CartesianPair[i3, i4]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/30 +
		(CartesianPair[i1, m2]*CartesianPair[i2, m3]*CartesianPair[i3, i4]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/30 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/30 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m2]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/10 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/30 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m3]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/10 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m2]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/30 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m2]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/30 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m3]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/30 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, m3]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/30 +
		(CartesianPair[i1, m5]*CartesianPair[i2, m4]*CartesianPair[i3, i4]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/30 -
		(CartesianPair[i1, m4]*CartesianPair[i2, m5]*CartesianPair[i3, i4]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/30 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/30 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/30 -
		(CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/10 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m4]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/30 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m4]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/30 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/10 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m5]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/30 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m5]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/30 -
		(CartesianPair[i1, m5]*CartesianPair[i2, m1]*CartesianPair[i3, i4]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/30 +
		(CartesianPair[i1, m1]*CartesianPair[i2, m5]*CartesianPair[i3, i4]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/30 -
		(CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/30 +
		(CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/30 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/10 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m1]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/30 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m1]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/30 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/10 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, m5]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/30 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, m5]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/30 +
		(CartesianPair[i1, m4]*CartesianPair[i2, m1]*CartesianPair[i3, i4]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/30 -
		(CartesianPair[i1, m1]*CartesianPair[i2, m4]*CartesianPair[i3, i4]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/30 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/30 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/30 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/10 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m1]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/30 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m1]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/30 +
		(CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/10 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, m4]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/30 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, m4]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/30 +
		(CartesianPair[i1, m5]*CartesianPair[i2, m3]*CartesianPair[i3, i4]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/30 -
		(CartesianPair[i1, m3]*CartesianPair[i2, m5]*CartesianPair[i3, i4]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/30 -
		(CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/10 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m3]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/30 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/10 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m5]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/30 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/30 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m3]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/30 -
		(CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/30 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m5]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/30 -
		(CartesianPair[i1, m5]*CartesianPair[i2, m1]*CartesianPair[i3, i4]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/30 +
		(CartesianPair[i1, m1]*CartesianPair[i2, m5]*CartesianPair[i3, i4]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/30 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/10 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m1]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/30 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/10 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, m5]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/30 -
		(CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/30 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m1]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/30 +
		(CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/30 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, m5]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/30 +
		(CartesianPair[i1, m3]*CartesianPair[i2, m1]*CartesianPair[i3, i4]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/30 -
		(CartesianPair[i1, m1]*CartesianPair[i2, m3]*CartesianPair[i3, i4]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/30 -
		(CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/10 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m1]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/30 +
		(CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/10 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, m3]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/30 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/30 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m1]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/30 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/30 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, m3]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/30 -
		(CartesianPair[i1, m5]*CartesianPair[i2, m2]*CartesianPair[i3, i4]*CartesianPair[i5, m1]*CartesianPair[m3, m4])/10 +
		(CartesianPair[i1, m2]*CartesianPair[i2, m5]*CartesianPair[i3, i4]*CartesianPair[i5, m1]*CartesianPair[m3, m4])/10 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[i5, m1]*CartesianPair[m3, m4])/30 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m2]*CartesianPair[i5, m1]*CartesianPair[m3, m4])/30 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m1]*CartesianPair[m3, m4])/30 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m5]*CartesianPair[i5, m1]*CartesianPair[m3, m4])/30 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[i5, m1]*CartesianPair[m3, m4])/30 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m2]*CartesianPair[i5, m1]*CartesianPair[m3, m4])/30 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m1]*CartesianPair[m3, m4])/30 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m5]*CartesianPair[i5, m1]*CartesianPair[m3, m4])/30 +
		(CartesianPair[i1, m5]*CartesianPair[i2, m1]*CartesianPair[i3, i4]*CartesianPair[i5, m2]*CartesianPair[m3, m4])/10 -
		(CartesianPair[i1, m1]*CartesianPair[i2, m5]*CartesianPair[i3, i4]*CartesianPair[i5, m2]*CartesianPair[m3, m4])/10 -
		(CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[i5, m2]*CartesianPair[m3, m4])/30 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m1]*CartesianPair[i5, m2]*CartesianPair[m3, m4])/30 +
		(CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m2]*CartesianPair[m3, m4])/30 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, m5]*CartesianPair[i5, m2]*CartesianPair[m3, m4])/30 -
		(CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[i5, m2]*CartesianPair[m3, m4])/30 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m1]*CartesianPair[i5, m2]*CartesianPair[m3, m4])/30 +
		(CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m2]*CartesianPair[m3, m4])/30 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, m5]*CartesianPair[i5, m2]*CartesianPair[m3, m4])/30 -
		(CartesianPair[i1, m2]*CartesianPair[i2, m1]*CartesianPair[i3, i4]*CartesianPair[i5, m5]*CartesianPair[m3, m4])/10 +
		(CartesianPair[i1, m1]*CartesianPair[i2, m2]*CartesianPair[i3, i4]*CartesianPair[i5, m5]*CartesianPair[m3, m4])/10 +
		(CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[i5, m5]*CartesianPair[m3, m4])/30 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m1]*CartesianPair[i5, m5]*CartesianPair[m3, m4])/30 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[i5, m5]*CartesianPair[m3, m4])/30 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, m2]*CartesianPair[i5, m5]*CartesianPair[m3, m4])/30 +
		(CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[i5, m5]*CartesianPair[m3, m4])/30 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m1]*CartesianPair[i5, m5]*CartesianPair[m3, m4])/30 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[i5, m5]*CartesianPair[m3, m4])/30 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, m2]*CartesianPair[i5, m5]*CartesianPair[m3, m4])/30
};

tensorProjRule1 = {
	(* Rank 1*)
	projHead[CartesianPair[i1_CartesianIndex, m1_CartesianMomentum ]] :> CartesianPair[i1,m1],

	(* Rank 2*)
	projHead[CartesianPair[i1_CartesianIndex, m1_CartesianMomentum ] CartesianPair[i2_CartesianIndex, m2_CartesianMomentum]] :>
		-(CartesianPair[i1, m2]*CartesianPair[i2, m1])/2 + (CartesianPair[i1, m1]*CartesianPair[i2, m2])/2,

	(* Rank 3*)
	projHead[CartesianPair[i1_CartesianIndex, m1_CartesianMomentum ] CartesianPair[i2_CartesianIndex, m2_CartesianMomentum] CartesianPair[i3_CartesianIndex, m3_CartesianMomentum]] :>
		-(CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[m1, m2])/10 - (CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[m1, m2])/10 +
		(2*CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[m1, m2])/5 - (CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[m1, m3])/10 +
		(2*CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[m1, m3])/5 - (CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[m1, m3])/10 +
		(2*CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[m2, m3])/5 - (CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[m2, m3])/10 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[m2, m3])/10,

	(* Rank 4*)
	projHead[CartesianPair[i1_CartesianIndex, m1_CartesianMomentum ] CartesianPair[i2_CartesianIndex, m2_CartesianMomentum] CartesianPair[i3_CartesianIndex, m3_CartesianMomentum] CartesianPair[i4_CartesianIndex, m4_CartesianMomentum]] :>
		-(CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[m1, m2])/10 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m3]*CartesianPair[m1, m2])/10 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[m1, m2])/10 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m4]*CartesianPair[m1, m2])/10 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[m1, m2])/10 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m3]*CartesianPair[m1, m2])/10 -
		(3*CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m3]*CartesianPair[m1, m2])/10 -
		(CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[m1, m2])/10 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m4]*CartesianPair[m1, m2])/10 +
		(3*CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m4]*CartesianPair[m1, m2])/10 -
		(CartesianPair[i1, m4]*CartesianPair[i2, m2]*CartesianPair[i3, i4]*CartesianPair[m1, m3])/10 +
		(CartesianPair[i1, m2]*CartesianPair[i2, m4]*CartesianPair[i3, i4]*CartesianPair[m1, m3])/10 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m2]*CartesianPair[m1, m3])/10 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m4]*CartesianPair[m1, m3])/10 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[m1, m3])/10 -
		(3*CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m2]*CartesianPair[m1, m3])/10 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m2]*CartesianPair[m1, m3])/10 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[m1, m3])/10 +
		(3*CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m4]*CartesianPair[m1, m3])/10 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, m4]*CartesianPair[m1, m3])/10 -
		(CartesianPair[i1, m3]*CartesianPair[i2, m2]*CartesianPair[i3, i4]*CartesianPair[m1, m4])/10 +
		(CartesianPair[i1, m2]*CartesianPair[i2, m3]*CartesianPair[i3, i4]*CartesianPair[m1, m4])/10 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[m1, m4])/10 -
		(3*CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m2]*CartesianPair[m1, m4])/10 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[m1, m4])/10 +
		(3*CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m3]*CartesianPair[m1, m4])/10 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m2]*CartesianPair[m1, m4])/10 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m2]*CartesianPair[m1, m4])/10 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m3]*CartesianPair[m1, m4])/10 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, m3]*CartesianPair[m1, m4])/10 +
		(CartesianPair[i1, m4]*CartesianPair[i2, m1]*CartesianPair[i3, i4]*CartesianPair[m2, m3])/10 -
		(CartesianPair[i1, m1]*CartesianPair[i2, m4]*CartesianPair[i3, i4]*CartesianPair[m2, m3])/10 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[m2, m3])/10 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[m2, m3])/10 -
		(3*CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[m2, m3])/10 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m1]*CartesianPair[m2, m3])/10 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m1]*CartesianPair[m2, m3])/10 +
		(3*CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[m2, m3])/10 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, m4]*CartesianPair[m2, m3])/10 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, m4]*CartesianPair[m2, m3])/10 +
		(CartesianPair[i1, m3]*CartesianPair[i2, m1]*CartesianPair[i3, i4]*CartesianPair[m2, m4])/10 -
		(CartesianPair[i1, m1]*CartesianPair[i2, m3]*CartesianPair[i3, i4]*CartesianPair[m2, m4])/10 -
		(3*CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[m2, m4])/10 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m1]*CartesianPair[m2, m4])/10 +
		(3*CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[m2, m4])/10 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, m3]*CartesianPair[m2, m4])/10 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[m2, m4])/10 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m1]*CartesianPair[m2, m4])/10 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[m2, m4])/10 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, m3]*CartesianPair[m2, m4])/10 -
		(3*CartesianPair[i1, m2]*CartesianPair[i2, m1]*CartesianPair[i3, i4]*CartesianPair[m3, m4])/10 +
		(3*CartesianPair[i1, m1]*CartesianPair[i2, m2]*CartesianPair[i3, i4]*CartesianPair[m3, m4])/10 +
		(CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[m3, m4])/10 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m1]*CartesianPair[m3, m4])/10 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[m3, m4])/10 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, m2]*CartesianPair[m3, m4])/10 +
		(CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[m3, m4])/10 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m1]*CartesianPair[m3, m4])/10 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[m3, m4])/10 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, m2]*CartesianPair[m3, m4])/10,

	(* Rank 5*)
	projHead[CartesianPair[i1_CartesianIndex, m1_CartesianMomentum ] CartesianPair[i2_CartesianIndex, m2_CartesianMomentum] CartesianPair[i3_CartesianIndex, m3_CartesianMomentum]*
		CartesianPair[i4_CartesianIndex, m4_CartesianMomentum] CartesianPair[i5_CartesianIndex, m5_CartesianMomentum]] :>
		(CartesianPair[i1, m5]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/35 +
		(CartesianPair[i1, i5]*CartesianPair[i2, m5]*CartesianPair[i3, i4]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/35 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/35 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/14 +
		(CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/35 -
		(CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/14 -
		(CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/14 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/35 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/35 -
		(CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/14 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/35 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/35 +
		(8*CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/35 -
		(CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/14 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/14 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/35 -
		(CartesianPair[i1, i5]*CartesianPair[i2, m4]*CartesianPair[i3, i4]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/14 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/35 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/35 -
		(CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/14 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m4]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/35 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/14 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/35 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/35 +
		(8*CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/35 -
		(CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m4]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/14 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m4]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/14 -
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m4]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/14 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m4]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/35 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m4]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/35 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/35 +
		(CartesianPair[i1, i5]*CartesianPair[i2, m5]*CartesianPair[i3, i4]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/35 -
		(CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/14 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/35 -
		(CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/14 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/35 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/35 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/14 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/35 +
		(CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/35 -
		(CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/14 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/35 -
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/14 +
		(8*CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/35 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/14 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/35 -
		(CartesianPair[i1, i5]*CartesianPair[i2, m3]*CartesianPair[i3, i4]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/14 -
		(CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/14 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/35 +
		(8*CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/35 -
		(CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m3]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/14 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/35 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/35 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/14 -
		(CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/14 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m3]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/35 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m3]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/35 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m3]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/35 -
		(CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m3]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/14 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m3]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/35 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/14 +
		(CartesianPair[i1, i5]*CartesianPair[i2, m4]*CartesianPair[i3, i4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/35 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/35 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/35 +
		(CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/35 -
		(CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/14 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/35 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/14 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/35 -
		(CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/14 +
		(8*CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/35 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/14 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/35 -
		(CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/14 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/35 -
		(CartesianPair[i1, m3]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/14 +
		(CartesianPair[i1, i5]*CartesianPair[i2, m3]*CartesianPair[i3, i4]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/35 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/35 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/14 -
		(CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/14 +
		(8*CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m3]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/35 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/35 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/35 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/14 +
		(CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/35 -
		(CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m3]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/14 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m3]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/35 -
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m3]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/14 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m3]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/35 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m3]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/35 -
		(CartesianPair[i1, m5]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/14 -
		(CartesianPair[i1, i5]*CartesianPair[i2, m5]*CartesianPair[i3, i4]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/14 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/35 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/35 +
		(CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/35 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/35 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/35 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/35 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/14 +
		(CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/35 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/35 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/14 -
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/14 -
		(CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/14 +
		(8*CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/35 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/14 +
		(8*CartesianPair[i1, i5]*CartesianPair[i2, m2]*CartesianPair[i3, i4]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/35 +
		(CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/35 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, i5]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/14 -
		(CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/14 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m2]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/35 +
		(CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/35 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, i5]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/14 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, i5]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/35 -
		(CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/14 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m2]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/35 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m2]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/35 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m2]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/35 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m2]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/35 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m2]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/14 +
		(8*CartesianPair[i1, m1]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/35 -
		(CartesianPair[i1, i5]*CartesianPair[i2, m1]*CartesianPair[i3, i4]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/14 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/14 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, i5]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/35 +
		(CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/35 -
		(CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m1]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/14 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/14 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, i5]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/35 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, i5]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/35 +
		(CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/35 -
		(CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m1]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/14 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m1]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/35 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m1]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/35 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m1]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/35 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m1]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/14 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/35 +
		(CartesianPair[i1, i5]*CartesianPair[i2, m4]*CartesianPair[i3, i4]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/35 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/14 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/14 +
		(CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/35 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m4]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/35 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/35 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/35 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/14 -
		(CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/14 -
		(CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m4]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/14 +
		(8*CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m4]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/35 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m4]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/35 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m4]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/35 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m4]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/14 +
		(CartesianPair[i1, m2]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/35 -
		(CartesianPair[i1, i5]*CartesianPair[i2, m2]*CartesianPair[i3, i4]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/14 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/14 +
		(8*CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, i5]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/35 +
		(CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/35 -
		(CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m2]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/14 +
		(CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/35 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, i5]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/14 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, i5]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/35 +
		(CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/35 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m2]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/35 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m2]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/14 -
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m2]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/14 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m2]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/35 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m2]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/35 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/14 +
		(CartesianPair[i1, i5]*CartesianPair[i2, m1]*CartesianPair[i3, i4]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/35 +
		(8*CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/35 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, i5]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/14 -
		(CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/14 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m1]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/35 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/14 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, i5]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/35 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, i5]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/35 +
		(CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/35 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m1]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/35 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m1]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/14 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m1]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/35 -
		(CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m1]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/14 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m1]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/35 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/35 +
		(CartesianPair[i1, i5]*CartesianPair[i2, m3]*CartesianPair[i3, i4]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/35 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/35 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, i5]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/35 -
		(CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/14 -
		(CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m3]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/14 -
		(CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/14 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, i5]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/14 +
		(8*CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, i5]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/35 +
		(CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/35 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m3]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/35 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m3]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/14 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m3]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/35 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m3]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/35 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m3]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/14 +
		(CartesianPair[i1, m2]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/35 -
		(CartesianPair[i1, i5]*CartesianPair[i2, m2]*CartesianPair[i3, i4]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/14 +
		(CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/35 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, i5]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/14 +
		(CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/35 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m2]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/35 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/14 +
		(8*CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, i5]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/35 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, i5]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/14 +
		(CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/35 -
		(CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m2]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/14 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m2]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/35 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m2]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/35 -
		(CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m2]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/14 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m2]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/35 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/14 +
		(CartesianPair[i1, i5]*CartesianPair[i2, m1]*CartesianPair[i3, i4]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/35 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/14 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, i5]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/35 +
		(CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/35 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m1]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/35 +
		(8*CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/35 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, i5]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/14 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, i5]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/14 -
		(CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/14 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m1]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/35 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m1]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/35 -
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m1]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/14 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m1]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/35 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m1]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/35
};

tensorProjRule2 = {
	(* Rank 1*)
	projHead[CartesianPair[_CartesianIndex, _CartesianMomentum ]] :>0,

	(* Rank 2*)
	projHead[CartesianPair[i1_CartesianIndex, m1_CartesianMomentum ] CartesianPair[i2_CartesianIndex, m2_CartesianMomentum]] :>
		(CartesianPair[i1, m2]*CartesianPair[i2, m1])/2 + (CartesianPair[i1, m1]*CartesianPair[i2, m2])/2 - (CartesianPair[i1, i2]*CartesianPair[m1, m2])/3,

	(* Rank 3*)
	projHead[CartesianPair[i1_CartesianIndex, m1_CartesianMomentum ] CartesianPair[i2_CartesianIndex, m2_CartesianMomentum] CartesianPair[i3_CartesianIndex, m3_CartesianMomentum]] :>
		-(CartesianPair[i1, m2]*CartesianPair[i2, m3]*CartesianPair[i3, m1])/3 - (CartesianPair[i1, m3]*CartesianPair[i2, m1]*CartesianPair[i3, m2])/3 +
		(2*CartesianPair[i1, m1]*CartesianPair[i2, m2]*CartesianPair[i3, m3])/3 + (CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[m1, m2])/6 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[m1, m2])/6 - (CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[m1, m2])/3 +
		(CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[m1, m3])/6 - (CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[m1, m3])/3 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[m1, m3])/6 - (CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[m2, m3])/3 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[m2, m3])/6 + (CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[m2, m3])/6,

	(* Rank 4*)
	projHead[CartesianPair[i1_CartesianIndex, m1_CartesianMomentum ] CartesianPair[i2_CartesianIndex, m2_CartesianMomentum] CartesianPair[i3_CartesianIndex, m3_CartesianMomentum] CartesianPair[i4_CartesianIndex, m4_CartesianMomentum]] :>
		(2*CartesianPair[i1, m4]*CartesianPair[i2, m3]*CartesianPair[i3, i4]*CartesianPair[m1, m2])/21 +
		(2*CartesianPair[i1, m3]*CartesianPair[i2, m4]*CartesianPair[i3, i4]*CartesianPair[m1, m2])/21 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[m1, m2])/14 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m3]*CartesianPair[m1, m2])/14 -
		(CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[m1, m2])/14 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m4]*CartesianPair[m1, m2])/14 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[m1, m2])/14 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m3]*CartesianPair[m1, m2])/14 +
		(11*CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m3]*CartesianPair[m1, m2])/42 -
		(CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[m1, m2])/14 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m4]*CartesianPair[m1, m2])/14 +
		(11*CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m4]*CartesianPair[m1, m2])/42 -
		(CartesianPair[i1, m4]*CartesianPair[i2, m2]*CartesianPair[i3, i4]*CartesianPair[m1, m3])/14 -
		(CartesianPair[i1, m2]*CartesianPair[i2, m4]*CartesianPair[i3, i4]*CartesianPair[m1, m3])/14 +
		(2*CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[m1, m3])/21 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m2]*CartesianPair[m1, m3])/14 +
		(2*CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[m1, m3])/21 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m4]*CartesianPair[m1, m3])/14 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[m1, m3])/14 +
		(11*CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m2]*CartesianPair[m1, m3])/42 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m2]*CartesianPair[m1, m3])/14 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[m1, m3])/14 +
		(11*CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m4]*CartesianPair[m1, m3])/42 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, m4]*CartesianPair[m1, m3])/14 -
		(CartesianPair[i1, m3]*CartesianPair[i2, m2]*CartesianPair[i3, i4]*CartesianPair[m1, m4])/14 -
		(CartesianPair[i1, m2]*CartesianPair[i2, m3]*CartesianPair[i3, i4]*CartesianPair[m1, m4])/14 -
		(CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[m1, m4])/14 +
		(11*CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m2]*CartesianPair[m1, m4])/42 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[m1, m4])/14 +
		(11*CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m3]*CartesianPair[m1, m4])/42 +
		(2*CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[m1, m4])/21 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m2]*CartesianPair[m1, m4])/14 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m2]*CartesianPair[m1, m4])/14 +
		(2*CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[m1, m4])/21 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m3]*CartesianPair[m1, m4])/14 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, m3]*CartesianPair[m1, m4])/14 -
		(CartesianPair[i1, m4]*CartesianPair[i2, m1]*CartesianPair[i3, i4]*CartesianPair[m2, m3])/14 -
		(CartesianPair[i1, m1]*CartesianPair[i2, m4]*CartesianPair[i3, i4]*CartesianPair[m2, m3])/14 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[m2, m3])/14 +
		(2*CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m1]*CartesianPair[m2, m3])/21 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[m2, m3])/14 +
		(2*CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, m4]*CartesianPair[m2, m3])/21 +
		(11*CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[m2, m3])/42 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m1]*CartesianPair[m2, m3])/14 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m1]*CartesianPair[m2, m3])/14 +
		(11*CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[m2, m3])/42 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, m4]*CartesianPair[m2, m3])/14 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, m4]*CartesianPair[m2, m3])/14 -
		(10*CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/21 +
		(4*CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/21 +
		(4*CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/21 -
		(CartesianPair[i1, m3]*CartesianPair[i2, m1]*CartesianPair[i3, i4]*CartesianPair[m2, m4])/14 -
		(CartesianPair[i1, m1]*CartesianPair[i2, m3]*CartesianPair[i3, i4]*CartesianPair[m2, m4])/14 +
		(11*CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[m2, m4])/42 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m1]*CartesianPair[m2, m4])/14 +
		(11*CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[m2, m4])/42 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, m3]*CartesianPair[m2, m4])/14 -
		(CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[m2, m4])/14 +
		(2*CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m1]*CartesianPair[m2, m4])/21 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m1]*CartesianPair[m2, m4])/14 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[m2, m4])/14 +
		(2*CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, m3]*CartesianPair[m2, m4])/21 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, m3]*CartesianPair[m2, m4])/14 +
		(4*CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/21 -
		(10*CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/21 +
		(4*CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/21 +
		(11*CartesianPair[i1, m2]*CartesianPair[i2, m1]*CartesianPair[i3, i4]*CartesianPair[m3, m4])/42 +
		(11*CartesianPair[i1, m1]*CartesianPair[i2, m2]*CartesianPair[i3, i4]*CartesianPair[m3, m4])/42 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[m3, m4])/14 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m1]*CartesianPair[m3, m4])/14 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[m3, m4])/14 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, m2]*CartesianPair[m3, m4])/14 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[m3, m4])/14 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m1]*CartesianPair[m3, m4])/14 +
		(2*CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, m1]*CartesianPair[m3, m4])/21 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[m3, m4])/14 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, m2]*CartesianPair[m3, m4])/14 +
		(2*CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, m2]*CartesianPair[m3, m4])/21 +
		(4*CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/21 +
		(4*CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/21 -
		(10*CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/21,

	(* Rank 5*)
	projHead[CartesianPair[i1_CartesianIndex, m1_CartesianMomentum ] CartesianPair[i2_CartesianIndex, m2_CartesianMomentum] CartesianPair[i3_CartesianIndex, m3_CartesianMomentum]*
		CartesianPair[i4_CartesianIndex, m4_CartesianMomentum] CartesianPair[i5_CartesianIndex, m5_CartesianMomentum]] :>
		(CartesianPair[i1, m5]*CartesianPair[i2, m4]*CartesianPair[i3, m3]*CartesianPair[i4, i5]*CartesianPair[m1, m2])/7 +
		(CartesianPair[i1, m4]*CartesianPair[i2, m5]*CartesianPair[i3, m3]*CartesianPair[i4, i5]*CartesianPair[m1, m2])/7 -
		(CartesianPair[i1, m5]*CartesianPair[i2, m3]*CartesianPair[i3, m4]*CartesianPair[i4, i5]*CartesianPair[m1, m2])/7 -
		(CartesianPair[i1, m4]*CartesianPair[i2, m3]*CartesianPair[i3, m5]*CartesianPair[i4, i5]*CartesianPair[m1, m2])/7 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i5]*CartesianPair[i3, m4]*CartesianPair[i4, m3]*CartesianPair[m1, m2])/18 -
		(5*CartesianPair[i1, i5]*CartesianPair[i2, m5]*CartesianPair[i3, m4]*CartesianPair[i4, m3]*CartesianPair[m1, m2])/63 +
		(11*CartesianPair[i1, m4]*CartesianPair[i2, i5]*CartesianPair[i3, m5]*CartesianPair[i4, m3]*CartesianPair[m1, m2])/126 +
		(5*CartesianPair[i1, i5]*CartesianPair[i2, m4]*CartesianPair[i3, m5]*CartesianPair[i4, m3]*CartesianPair[m1, m2])/63 +
		(CartesianPair[i1, m5]*CartesianPair[i2, m3]*CartesianPair[i3, i5]*CartesianPair[i4, m4]*CartesianPair[m1, m2])/14 -
		(CartesianPair[i1, m3]*CartesianPair[i2, m5]*CartesianPair[i3, i5]*CartesianPair[i4, m4]*CartesianPair[m1, m2])/14 -
		(31*CartesianPair[i1, m5]*CartesianPair[i2, i5]*CartesianPair[i3, m3]*CartesianPair[i4, m4]*CartesianPair[m1, m2])/126 -
		(CartesianPair[i1, i5]*CartesianPair[i2, m5]*CartesianPair[i3, m3]*CartesianPair[i4, m4]*CartesianPair[m1, m2])/9 -
		(CartesianPair[i1, m3]*CartesianPair[i2, i5]*CartesianPair[i3, m5]*CartesianPair[i4, m4]*CartesianPair[m1, m2])/63 +
		(CartesianPair[i1, i5]*CartesianPair[i2, m3]*CartesianPair[i3, m5]*CartesianPair[i4, m4]*CartesianPair[m1, m2])/9 +
		(CartesianPair[i1, m4]*CartesianPair[i2, m3]*CartesianPair[i3, i5]*CartesianPair[i4, m5]*CartesianPair[m1, m2])/14 -
		(CartesianPair[i1, m3]*CartesianPair[i2, m4]*CartesianPair[i3, i5]*CartesianPair[i4, m5]*CartesianPair[m1, m2])/14 -
		(5*CartesianPair[i1, m4]*CartesianPair[i2, i5]*CartesianPair[i3, m3]*CartesianPair[i4, m5]*CartesianPair[m1, m2])/126 -
		(2*CartesianPair[i1, i5]*CartesianPair[i2, m4]*CartesianPair[i3, m3]*CartesianPair[i4, m5]*CartesianPair[m1, m2])/63 +
		(10*CartesianPair[i1, m3]*CartesianPair[i2, i5]*CartesianPair[i3, m4]*CartesianPair[i4, m5]*CartesianPair[m1, m2])/63 +
		(2*CartesianPair[i1, i5]*CartesianPair[i2, m3]*CartesianPair[i3, m4]*CartesianPair[i4, m5]*CartesianPair[m1, m2])/63 +
		(11*CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/126 +
		(5*CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m4]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/63 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/18 -
		(5*CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m5]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/63 +
		(2*CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/63 +
		(5*CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m4]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/126 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m4]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/21 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/63 +
		(19*CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m5]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/126 -
		(2*CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m5]*CartesianPair[i5, m3]*CartesianPair[m1, m2])/7 +
		(2*CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/63 -
		(13*CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m3]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/126 +
		(11*CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/126 +
		(13*CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m5]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/126 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/63 +
		(19*CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m3]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/126 -
		(2*CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m3]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/7 -
		(4*CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/63 -
		(5*CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m5]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/63 +
		(2*CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m5]*CartesianPair[i5, m4]*CartesianPair[m1, m2])/21 -
		(11*CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/63 -
		(23*CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m3]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/126 -
		(11*CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/126 +
		(23*CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m4]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/126 +
		(2*CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/63 +
		(5*CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m3]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/126 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m3]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/21 -
		(2*CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/63 -
		(19*CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m4]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/63 +
		(4*CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m4]*CartesianPair[i5, m5]*CartesianPair[m1, m2])/7 -
		(5*CartesianPair[i1, m5]*CartesianPair[i2, m4]*CartesianPair[i3, m2]*CartesianPair[i4, i5]*CartesianPair[m1, m3])/42 -
		(5*CartesianPair[i1, m4]*CartesianPair[i2, m5]*CartesianPair[i3, m2]*CartesianPair[i4, i5]*CartesianPair[m1, m3])/42 +
		(5*CartesianPair[i1, m5]*CartesianPair[i2, m2]*CartesianPair[i3, m4]*CartesianPair[i4, i5]*CartesianPair[m1, m3])/21 -
		(5*CartesianPair[i1, m2]*CartesianPair[i2, m5]*CartesianPair[i3, m4]*CartesianPair[i4, i5]*CartesianPair[m1, m3])/42 +
		(5*CartesianPair[i1, m4]*CartesianPair[i2, m2]*CartesianPair[i3, m5]*CartesianPair[i4, i5]*CartesianPair[m1, m3])/21 -
		(5*CartesianPair[i1, m2]*CartesianPair[i2, m4]*CartesianPair[i3, m5]*CartesianPair[i4, i5]*CartesianPair[m1, m3])/42 -
		(41*CartesianPair[i1, m5]*CartesianPair[i2, i5]*CartesianPair[i3, m4]*CartesianPair[i4, m2]*CartesianPair[m1, m3])/252 +
		(CartesianPair[i1, i5]*CartesianPair[i2, m5]*CartesianPair[i3, m4]*CartesianPair[i4, m2]*CartesianPair[m1, m3])/9 -
		(13*CartesianPair[i1, m4]*CartesianPair[i2, i5]*CartesianPair[i3, m5]*CartesianPair[i4, m2]*CartesianPair[m1, m3])/252 -
		(CartesianPair[i1, i5]*CartesianPair[i2, m4]*CartesianPair[i3, m5]*CartesianPair[i4, m2]*CartesianPair[m1, m3])/9 -
		(CartesianPair[i1, m5]*CartesianPair[i2, m2]*CartesianPair[i3, i5]*CartesianPair[i4, m4]*CartesianPair[m1, m3])/4 +
		(CartesianPair[i1, m2]*CartesianPair[i2, m5]*CartesianPair[i3, i5]*CartesianPair[i4, m4]*CartesianPair[m1, m3])/4 +
		(59*CartesianPair[i1, m5]*CartesianPair[i2, i5]*CartesianPair[i3, m2]*CartesianPair[i4, m4]*CartesianPair[m1, m3])/252 +
		(CartesianPair[i1, i5]*CartesianPair[i2, m5]*CartesianPair[i3, m2]*CartesianPair[i4, m4]*CartesianPair[m1, m3])/18 +
		(5*CartesianPair[i1, m2]*CartesianPair[i2, i5]*CartesianPair[i3, m5]*CartesianPair[i4, m4]*CartesianPair[m1, m3])/126 -
		(CartesianPair[i1, i5]*CartesianPair[i2, m2]*CartesianPair[i3, m5]*CartesianPair[i4, m4]*CartesianPair[m1, m3])/18 -
		(CartesianPair[i1, m4]*CartesianPair[i2, m2]*CartesianPair[i3, i5]*CartesianPair[i4, m5]*CartesianPair[m1, m3])/4 +
		(CartesianPair[i1, m2]*CartesianPair[i2, m4]*CartesianPair[i3, i5]*CartesianPair[i4, m5]*CartesianPair[m1, m3])/4 +
		(31*CartesianPair[i1, m4]*CartesianPair[i2, i5]*CartesianPair[i3, m2]*CartesianPair[i4, m5]*CartesianPair[m1, m3])/252 -
		(CartesianPair[i1, i5]*CartesianPair[i2, m4]*CartesianPair[i3, m2]*CartesianPair[i4, m5]*CartesianPair[m1, m3])/18 -
		(23*CartesianPair[i1, m2]*CartesianPair[i2, i5]*CartesianPair[i3, m4]*CartesianPair[i4, m5]*CartesianPair[m1, m3])/126 +
		(CartesianPair[i1, i5]*CartesianPair[i2, m2]*CartesianPair[i3, m4]*CartesianPair[i4, m5]*CartesianPair[m1, m3])/18 -
		(13*CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/252 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m4]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/9 -
		(41*CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/252 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m5]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/9 +
		(5*CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/126 -
		(23*CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m4]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/252 +
		(5*CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m4]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/126 +
		(19*CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/126 -
		(79*CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m5]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/252 +
		(19*CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m5]*CartesianPair[i5, m2]*CartesianPair[m1, m3])/126 -
		(8*CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/63 +
		(7*CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m2]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/36 +
		(17*CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/252 -
		(7*CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m5]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/36 +
		(19*CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/126 -
		(79*CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m2]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/252 +
		(19*CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m2]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/126 -
		(5*CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/63 +
		(23*CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m5]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/126 -
		(5*CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, m5]*CartesianPair[i5, m4]*CartesianPair[m1, m3])/63 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/63 +
		(11*CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m2]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/36 +
		(73*CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/252 -
		(11*CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m4]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/36 +
		(5*CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/126 -
		(23*CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m2]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/252 +
		(5*CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m2]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/126 -
		(19*CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/63 +
		(79*CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m4]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/126 -
		(19*CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, m4]*CartesianPair[i5, m5]*CartesianPair[m1, m3])/63 +
		(3*CartesianPair[i1, m5]*CartesianPair[i2, m3]*CartesianPair[i3, m2]*CartesianPair[i4, i5]*CartesianPair[m1, m4])/14 -
		(3*CartesianPair[i1, m5]*CartesianPair[i2, m2]*CartesianPair[i3, m3]*CartesianPair[i4, i5]*CartesianPair[m1, m4])/14 -
		(3*CartesianPair[i1, m3]*CartesianPair[i2, m2]*CartesianPair[i3, m5]*CartesianPair[i4, i5]*CartesianPair[m1, m4])/14 +
		(3*CartesianPair[i1, m2]*CartesianPair[i2, m3]*CartesianPair[i3, m5]*CartesianPair[i4, i5]*CartesianPair[m1, m4])/14 -
		(13*CartesianPair[i1, m5]*CartesianPair[i2, m3]*CartesianPair[i3, i5]*CartesianPair[i4, m2]*CartesianPair[m1, m4])/84 +
		(13*CartesianPair[i1, m3]*CartesianPair[i2, m5]*CartesianPair[i3, i5]*CartesianPair[i4, m2]*CartesianPair[m1, m4])/84 +
		(17*CartesianPair[i1, m5]*CartesianPair[i2, i5]*CartesianPair[i3, m3]*CartesianPair[i4, m2]*CartesianPair[m1, m4])/63 -
		(11*CartesianPair[i1, i5]*CartesianPair[i2, m5]*CartesianPair[i3, m3]*CartesianPair[i4, m2]*CartesianPair[m1, m4])/126 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i5]*CartesianPair[i3, m5]*CartesianPair[i4, m2]*CartesianPair[m1, m4])/36 +
		(11*CartesianPair[i1, i5]*CartesianPair[i2, m3]*CartesianPair[i3, m5]*CartesianPair[i4, m2]*CartesianPair[m1, m4])/126 +
		(13*CartesianPair[i1, m5]*CartesianPair[i2, m2]*CartesianPair[i3, i5]*CartesianPair[i4, m3]*CartesianPair[m1, m4])/84 -
		(13*CartesianPair[i1, m2]*CartesianPair[i2, m5]*CartesianPair[i3, i5]*CartesianPair[i4, m3]*CartesianPair[m1, m4])/84 -
		(17*CartesianPair[i1, m5]*CartesianPair[i2, i5]*CartesianPair[i3, m2]*CartesianPair[i4, m3]*CartesianPair[m1, m4])/63 +
		(11*CartesianPair[i1, i5]*CartesianPair[i2, m5]*CartesianPair[i3, m2]*CartesianPair[i4, m3]*CartesianPair[m1, m4])/126 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i5]*CartesianPair[i3, m5]*CartesianPair[i4, m3]*CartesianPair[m1, m4])/36 -
		(11*CartesianPair[i1, i5]*CartesianPair[i2, m2]*CartesianPair[i3, m5]*CartesianPair[i4, m3]*CartesianPair[m1, m4])/126 +
		(13*CartesianPair[i1, m3]*CartesianPair[i2, m2]*CartesianPair[i3, i5]*CartesianPair[i4, m5]*CartesianPair[m1, m4])/42 -
		(13*CartesianPair[i1, m2]*CartesianPair[i2, m3]*CartesianPair[i3, i5]*CartesianPair[i4, m5]*CartesianPair[m1, m4])/42 -
		(61*CartesianPair[i1, m3]*CartesianPair[i2, i5]*CartesianPair[i3, m2]*CartesianPair[i4, m5]*CartesianPair[m1, m4])/252 +
		(11*CartesianPair[i1, i5]*CartesianPair[i2, m3]*CartesianPair[i3, m2]*CartesianPair[i4, m5]*CartesianPair[m1, m4])/63 +
		(61*CartesianPair[i1, m2]*CartesianPair[i2, i5]*CartesianPair[i3, m3]*CartesianPair[i4, m5]*CartesianPair[m1, m4])/252 -
		(11*CartesianPair[i1, i5]*CartesianPair[i2, m2]*CartesianPair[i3, m3]*CartesianPair[i4, m5]*CartesianPair[m1, m4])/63 -
		(23*CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/252 +
		(61*CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m3]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/252 +
		(19*CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/126 -
		(61*CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m5]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/252 +
		(5*CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/63 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m3]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/9 +
		(5*CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m3]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/63 -
		(13*CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/126 +
		(7*CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m5]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/36 -
		(13*CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m5]*CartesianPair[i5, m2]*CartesianPair[m1, m4])/126 +
		(23*CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/252 -
		(61*CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m2]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/252 -
		(19*CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/126 +
		(61*CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m5]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/252 -
		(5*CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/63 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m2]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/9 -
		(5*CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m2]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/63 +
		(13*CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/126 -
		(7*CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m5]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/36 +
		(13*CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, m5]*CartesianPair[i5, m3]*CartesianPair[m1, m4])/126 +
		(61*CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/252 -
		(61*CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m2]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/126 -
		(61*CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/252 +
		(61*CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m3]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/126 -
		(23*CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/126 +
		(11*CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m2]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/36 -
		(23*CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m2]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/126 +
		(23*CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/126 -
		(11*CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m3]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/36 +
		(23*CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, m3]*CartesianPair[i5, m5]*CartesianPair[m1, m4])/126 +
		(2*CartesianPair[i1, m4]*CartesianPair[i2, m3]*CartesianPair[i3, m2]*CartesianPair[i4, i5]*CartesianPair[m1, m5])/63 +
		(4*CartesianPair[i1, m3]*CartesianPair[i2, m4]*CartesianPair[i3, m2]*CartesianPair[i4, i5]*CartesianPair[m1, m5])/63 -
		(2*CartesianPair[i1, m4]*CartesianPair[i2, m2]*CartesianPair[i3, m3]*CartesianPair[i4, i5]*CartesianPair[m1, m5])/63 -
		(4*CartesianPair[i1, m2]*CartesianPair[i2, m4]*CartesianPair[i3, m3]*CartesianPair[i4, i5]*CartesianPair[m1, m5])/63 +
		(2*CartesianPair[i1, m3]*CartesianPair[i2, m2]*CartesianPair[i3, m4]*CartesianPair[i4, i5]*CartesianPair[m1, m5])/63 -
		(2*CartesianPair[i1, m2]*CartesianPair[i2, m3]*CartesianPair[i3, m4]*CartesianPair[i4, i5]*CartesianPair[m1, m5])/63 +
		(11*CartesianPair[i1, m4]*CartesianPair[i2, m3]*CartesianPair[i3, i5]*CartesianPair[i4, m2]*CartesianPair[m1, m5])/126 -
		(11*CartesianPair[i1, m3]*CartesianPair[i2, m4]*CartesianPair[i3, i5]*CartesianPair[i4, m2]*CartesianPair[m1, m5])/126 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i5]*CartesianPair[i3, m3]*CartesianPair[i4, m2]*CartesianPair[m1, m5])/7 +
		(11*CartesianPair[i1, i5]*CartesianPair[i2, m4]*CartesianPair[i3, m3]*CartesianPair[i4, m2]*CartesianPair[m1, m5])/63 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i5]*CartesianPair[i3, m4]*CartesianPair[i4, m2]*CartesianPair[m1, m5])/42 -
		(11*CartesianPair[i1, i5]*CartesianPair[i2, m3]*CartesianPair[i3, m4]*CartesianPair[i4, m2]*CartesianPair[m1, m5])/63 -
		(11*CartesianPair[i1, m4]*CartesianPair[i2, m2]*CartesianPair[i3, i5]*CartesianPair[i4, m3]*CartesianPair[m1, m5])/126 +
		(11*CartesianPair[i1, m2]*CartesianPair[i2, m4]*CartesianPair[i3, i5]*CartesianPair[i4, m3]*CartesianPair[m1, m5])/126 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i5]*CartesianPair[i3, m2]*CartesianPair[i4, m3]*CartesianPair[m1, m5])/7 -
		(11*CartesianPair[i1, i5]*CartesianPair[i2, m4]*CartesianPair[i3, m2]*CartesianPair[i4, m3]*CartesianPair[m1, m5])/63 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i5]*CartesianPair[i3, m4]*CartesianPair[i4, m3]*CartesianPair[m1, m5])/42 +
		(11*CartesianPair[i1, i5]*CartesianPair[i2, m2]*CartesianPair[i3, m4]*CartesianPair[i4, m3]*CartesianPair[m1, m5])/63 -
		(11*CartesianPair[i1, m3]*CartesianPair[i2, m2]*CartesianPair[i3, i5]*CartesianPair[i4, m4]*CartesianPair[m1, m5])/63 +
		(11*CartesianPair[i1, m2]*CartesianPair[i2, m3]*CartesianPair[i3, i5]*CartesianPair[i4, m4]*CartesianPair[m1, m5])/63 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i5]*CartesianPair[i3, m2]*CartesianPair[i4, m4]*CartesianPair[m1, m5])/6 -
		(22*CartesianPair[i1, i5]*CartesianPair[i2, m3]*CartesianPair[i3, m2]*CartesianPair[i4, m4]*CartesianPair[m1, m5])/63 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i5]*CartesianPair[i3, m3]*CartesianPair[i4, m4]*CartesianPair[m1, m5])/6 +
		(22*CartesianPair[i1, i5]*CartesianPair[i2, m2]*CartesianPair[i3, m3]*CartesianPair[i4, m4]*CartesianPair[m1, m5])/63 +
		(19*CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[i5, m2]*CartesianPair[m1, m5])/126 -
		(11*CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m3]*CartesianPair[i5, m2]*CartesianPair[m1, m5])/126 -
		(2*CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[i5, m2]*CartesianPair[m1, m5])/63 +
		(11*CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m4]*CartesianPair[i5, m2]*CartesianPair[m1, m5])/126 -
		(5*CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[i5, m2]*CartesianPair[m1, m5])/63 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m3]*CartesianPair[i5, m2]*CartesianPair[m1, m5])/9 -
		(5*CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m3]*CartesianPair[i5, m2]*CartesianPair[m1, m5])/63 +
		(2*CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[i5, m2]*CartesianPair[m1, m5])/63 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m4]*CartesianPair[i5, m2]*CartesianPair[m1, m5])/18 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m4]*CartesianPair[i5, m2]*CartesianPair[m1, m5])/9 -
		(19*CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[i5, m3]*CartesianPair[m1, m5])/126 +
		(11*CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m2]*CartesianPair[i5, m3]*CartesianPair[m1, m5])/126 +
		(2*CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[i5, m3]*CartesianPair[m1, m5])/63 -
		(11*CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m4]*CartesianPair[i5, m3]*CartesianPair[m1, m5])/126 +
		(5*CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[i5, m3]*CartesianPair[m1, m5])/63 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m2]*CartesianPair[i5, m3]*CartesianPair[m1, m5])/9 +
		(5*CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m2]*CartesianPair[i5, m3]*CartesianPair[m1, m5])/63 -
		(2*CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[i5, m3]*CartesianPair[m1, m5])/63 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m4]*CartesianPair[i5, m3]*CartesianPair[m1, m5])/18 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, m4]*CartesianPair[i5, m3]*CartesianPair[m1, m5])/9 -
		(23*CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[i5, m4]*CartesianPair[m1, m5])/126 +
		(11*CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m2]*CartesianPair[i5, m4]*CartesianPair[m1, m5])/63 +
		(23*CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[i5, m4]*CartesianPair[m1, m5])/126 -
		(11*CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m3]*CartesianPair[i5, m4]*CartesianPair[m1, m5])/63 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[i5, m4]*CartesianPair[m1, m5])/9 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m2]*CartesianPair[i5, m4]*CartesianPair[m1, m5])/18 -
		(2*CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m2]*CartesianPair[i5, m4]*CartesianPair[m1, m5])/63 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[i5, m4]*CartesianPair[m1, m5])/9 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m3]*CartesianPair[i5, m4]*CartesianPair[m1, m5])/18 +
		(2*CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, m3]*CartesianPair[i5, m4]*CartesianPair[m1, m5])/63 -
		(CartesianPair[i1, m5]*CartesianPair[i2, m1]*CartesianPair[i3, m4]*CartesianPair[i4, i5]*CartesianPair[m2, m3])/7 +
		(CartesianPair[i1, m1]*CartesianPair[i2, m5]*CartesianPair[i3, m4]*CartesianPair[i4, i5]*CartesianPair[m2, m3])/7 -
		(CartesianPair[i1, m4]*CartesianPair[i2, m1]*CartesianPair[i3, m5]*CartesianPair[i4, i5]*CartesianPair[m2, m3])/7 +
		(CartesianPair[i1, m1]*CartesianPair[i2, m4]*CartesianPair[i3, m5]*CartesianPair[i4, i5]*CartesianPair[m2, m3])/7 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i5]*CartesianPair[i3, m4]*CartesianPair[i4, m1]*CartesianPair[m2, m3])/6 -
		(5*CartesianPair[i1, i5]*CartesianPair[i2, m5]*CartesianPair[i3, m4]*CartesianPair[i4, m1]*CartesianPair[m2, m3])/63 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i5]*CartesianPair[i3, m5]*CartesianPair[i4, m1]*CartesianPair[m2, m3])/42 +
		(5*CartesianPair[i1, i5]*CartesianPair[i2, m4]*CartesianPair[i3, m5]*CartesianPair[i4, m1]*CartesianPair[m2, m3])/63 +
		(3*CartesianPair[i1, m5]*CartesianPair[i2, m1]*CartesianPair[i3, i5]*CartesianPair[i4, m4]*CartesianPair[m2, m3])/14 -
		(3*CartesianPair[i1, m1]*CartesianPair[i2, m5]*CartesianPair[i3, i5]*CartesianPair[i4, m4]*CartesianPair[m2, m3])/14 -
		(5*CartesianPair[i1, m5]*CartesianPair[i2, i5]*CartesianPair[i3, m1]*CartesianPair[i4, m4]*CartesianPair[m2, m3])/42 +
		(2*CartesianPair[i1, i5]*CartesianPair[i2, m5]*CartesianPair[i3, m1]*CartesianPair[i4, m4]*CartesianPair[m2, m3])/63 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i5]*CartesianPair[i3, m5]*CartesianPair[i4, m4]*CartesianPair[m2, m3])/7 -
		(2*CartesianPair[i1, i5]*CartesianPair[i2, m1]*CartesianPair[i3, m5]*CartesianPair[i4, m4]*CartesianPair[m2, m3])/63 +
		(3*CartesianPair[i1, m4]*CartesianPair[i2, m1]*CartesianPair[i3, i5]*CartesianPair[i4, m5]*CartesianPair[m2, m3])/14 -
		(3*CartesianPair[i1, m1]*CartesianPair[i2, m4]*CartesianPair[i3, i5]*CartesianPair[i4, m5]*CartesianPair[m2, m3])/14 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i5]*CartesianPair[i3, m1]*CartesianPair[i4, m5]*CartesianPair[m2, m3])/42 +
		(CartesianPair[i1, i5]*CartesianPair[i2, m4]*CartesianPair[i3, m1]*CartesianPair[i4, m5]*CartesianPair[m2, m3])/9 +
		(CartesianPair[i1, m1]*CartesianPair[i2, i5]*CartesianPair[i3, m4]*CartesianPair[i4, m5]*CartesianPair[m2, m3])/7 -
		(CartesianPair[i1, i5]*CartesianPair[i2, m1]*CartesianPair[i3, m4]*CartesianPair[i4, m5]*CartesianPair[m2, m3])/9 -
		(CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/42 +
		(5*CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m4]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/63 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/6 -
		(5*CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m5]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/63 -
		(CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/21 +
		(5*CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m4]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/126 +
		(2*CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m4]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/63 -
		(2*CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/7 +
		(19*CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m5]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/126 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m5]*CartesianPair[i5, m1]*CartesianPair[m2, m3])/63 +
		(4*CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/21 -
		(13*CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m1]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/126 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/14 +
		(13*CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, m5]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/126 -
		(2*CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/7 +
		(19*CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m1]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/126 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m1]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/63 +
		(2*CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/21 -
		(5*CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, m5]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/63 -
		(4*CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, m5]*CartesianPair[i5, m4]*CartesianPair[m2, m3])/63 +
		(2*CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/21 -
		(23*CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m1]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/126 -
		(5*CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/14 +
		(23*CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, m4]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/126 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/21 +
		(5*CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m1]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/126 +
		(2*CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m1]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/63 +
		(4*CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/7 -
		(19*CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, m4]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/63 -
		(2*CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, m4]*CartesianPair[i5, m5]*CartesianPair[m2, m3])/63 -
		(CartesianPair[i1, m5]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/42 +
		(CartesianPair[i1, i5]*CartesianPair[i2, m5]*CartesianPair[i3, i4]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/42 -
		(4*CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/21 +
		(5*CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/42 -
		(CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/14 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/14 +
		(5*CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/21 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/6 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/42 +
		(2*CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/21 -
		(2*CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/21 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/42 -
		(11*CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/42 +
		(11*CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m5]*CartesianPair[m1, m4]*CartesianPair[m2, m3])/42 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/42 -
		(2*CartesianPair[i1, i5]*CartesianPair[i2, m4]*CartesianPair[i3, i4]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/21 -
		(5*CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/21 +
		(5*CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/21 +
		(2*CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/7 -
		(2*CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m4]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/7 +
		(5*CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/21 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/6 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/42 -
		(11*CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/42 +
		(11*CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m4]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/42 +
		(2*CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m4]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/21 -
		(2*CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m4]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/21 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m4]*CartesianPair[m1, m5]*CartesianPair[m2, m3])/42 -
		(CartesianPair[i1, m3]*CartesianPair[i2, m5]*CartesianPair[i3, m1]*CartesianPair[i4, i5]*CartesianPair[m2, m4])/42 +
		(5*CartesianPair[i1, m5]*CartesianPair[i2, m1]*CartesianPair[i3, m3]*CartesianPair[i4, i5]*CartesianPair[m2, m4])/42 -
		(3*CartesianPair[i1, m1]*CartesianPair[i2, m5]*CartesianPair[i3, m3]*CartesianPair[i4, i5]*CartesianPair[m2, m4])/14 +
		(3*CartesianPair[i1, m3]*CartesianPair[i2, m1]*CartesianPair[i3, m5]*CartesianPair[i4, i5]*CartesianPair[m2, m4])/14 -
		(2*CartesianPair[i1, m1]*CartesianPair[i2, m3]*CartesianPair[i3, m5]*CartesianPair[i4, i5]*CartesianPair[m2, m4])/21 +
		(CartesianPair[i1, m5]*CartesianPair[i2, m3]*CartesianPair[i3, i5]*CartesianPair[i4, m1]*CartesianPair[m2, m4])/28 -
		(CartesianPair[i1, m3]*CartesianPair[i2, m5]*CartesianPair[i3, i5]*CartesianPair[i4, m1]*CartesianPair[m2, m4])/28 -
		(3*CartesianPair[i1, m5]*CartesianPair[i2, i5]*CartesianPair[i3, m3]*CartesianPair[i4, m1]*CartesianPair[m2, m4])/28 +
		(19*CartesianPair[i1, i5]*CartesianPair[i2, m5]*CartesianPair[i3, m3]*CartesianPair[i4, m1]*CartesianPair[m2, m4])/126 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i5]*CartesianPair[i3, m5]*CartesianPair[i4, m1]*CartesianPair[m2, m4])/21 -
		(19*CartesianPair[i1, i5]*CartesianPair[i2, m3]*CartesianPair[i3, m5]*CartesianPair[i4, m1]*CartesianPair[m2, m4])/126 -
		(3*CartesianPair[i1, m5]*CartesianPair[i2, m1]*CartesianPair[i3, i5]*CartesianPair[i4, m3]*CartesianPair[m2, m4])/14 +
		(3*CartesianPair[i1, m1]*CartesianPair[i2, m5]*CartesianPair[i3, i5]*CartesianPair[i4, m3]*CartesianPair[m2, m4])/14 +
		(19*CartesianPair[i1, m5]*CartesianPair[i2, i5]*CartesianPair[i3, m1]*CartesianPair[i4, m3]*CartesianPair[m2, m4])/84 -
		(2*CartesianPair[i1, i5]*CartesianPair[i2, m5]*CartesianPair[i3, m1]*CartesianPair[i4, m3]*CartesianPair[m2, m4])/63 +
		(CartesianPair[i1, m1]*CartesianPair[i2, i5]*CartesianPair[i3, m5]*CartesianPair[i4, m3]*CartesianPair[m2, m4])/84 +
		(2*CartesianPair[i1, i5]*CartesianPair[i2, m1]*CartesianPair[i3, m5]*CartesianPair[i4, m3]*CartesianPair[m2, m4])/63 -
		(CartesianPair[i1, m3]*CartesianPair[i2, m1]*CartesianPair[i3, i5]*CartesianPair[i4, m5]*CartesianPair[m2, m4])/4 +
		(CartesianPair[i1, m1]*CartesianPair[i2, m3]*CartesianPair[i3, i5]*CartesianPair[i4, m5]*CartesianPair[m2, m4])/4 +
		(2*CartesianPair[i1, m3]*CartesianPair[i2, i5]*CartesianPair[i3, m1]*CartesianPair[i4, m5]*CartesianPair[m2, m4])/21 -
		(23*CartesianPair[i1, i5]*CartesianPair[i2, m3]*CartesianPair[i3, m1]*CartesianPair[i4, m5]*CartesianPair[m2, m4])/126 -
		(23*CartesianPair[i1, m1]*CartesianPair[i2, i5]*CartesianPair[i3, m3]*CartesianPair[i4, m5]*CartesianPair[m2, m4])/84 +
		(23*CartesianPair[i1, i5]*CartesianPair[i2, m1]*CartesianPair[i3, m3]*CartesianPair[i4, m5]*CartesianPair[m2, m4])/126 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/42 -
		(23*CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m3]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/252 -
		(9*CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/28 +
		(23*CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m5]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/252 -
		(CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/42 -
		(13*CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m3]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/252 +
		(11*CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m3]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/126 +
		(4*CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/21 -
		(8*CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m5]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/63 +
		(2*CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m5]*CartesianPair[i5, m1]*CartesianPair[m2, m4])/63 -
		(9*CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/28 +
		(19*CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, m1]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/126 +
		(CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/12 -
		(19*CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, m5]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/126 +
		(CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/6 -
		(41*CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, m1]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/252 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, m1]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/18 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/14 +
		(17*CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, m5]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/252 +
		(11*CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, m5]*CartesianPair[i5, m3]*CartesianPair[m2, m4])/126 -
		(3*CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/28 +
		(61*CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m1]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/252 +
		(9*CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/14 -
		(61*CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, m3]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/252 +
		(2*CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/21 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m1]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/63 -
		(11*CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m1]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/63 -
		(5*CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/14 +
		(73*CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, m3]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/252 -
		(11*CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, m3]*CartesianPair[i5, m5]*CartesianPair[m2, m4])/126 -
		(2*CartesianPair[i1, m5]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/21 -
		(CartesianPair[i1, i5]*CartesianPair[i2, m5]*CartesianPair[i3, i4]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/7 +
		(19*CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/42 -
		(2*CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/7 +
		(13*CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/42 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/21 -
		(2*CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/7 +
		(23*CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/42 -
		(2*CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/7 -
		(2*CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/21 +
		(3*CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/14 -
		(2*CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/21 +
		(11*CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/42 -
		(17*CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/21 +
		(11*CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m5]*CartesianPair[m1, m3]*CartesianPair[m2, m4])/42 -
		(CartesianPair[i1, m3]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/6 +
		(3*CartesianPair[i1, i5]*CartesianPair[i2, m3]*CartesianPair[i3, i4]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/7 +
		(25*CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/42 -
		(4*CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/7 -
		(13*CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/14 +
		(9*CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m3]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/14 -
		(5*CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/14 +
		(5*CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/42 +
		(5*CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, i5]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/21 +
		(2*CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/7 -
		(8*CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m3]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/21 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m3]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/42 -
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m3]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/14 +
		(13*CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m3]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/42 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m3]*CartesianPair[m1, m5]*CartesianPair[m2, m4])/6 +
		(23*CartesianPair[i1, m4]*CartesianPair[i2, m3]*CartesianPair[i3, m1]*CartesianPair[i4, i5]*CartesianPair[m2, m5])/126 -
		(11*CartesianPair[i1, m3]*CartesianPair[i2, m4]*CartesianPair[i3, m1]*CartesianPair[i4, i5]*CartesianPair[m2, m5])/126 -
		(4*CartesianPair[i1, m4]*CartesianPair[i2, m1]*CartesianPair[i3, m3]*CartesianPair[i4, i5]*CartesianPair[m2, m5])/63 -
		(19*CartesianPair[i1, m1]*CartesianPair[i2, m4]*CartesianPair[i3, m3]*CartesianPair[i4, i5]*CartesianPair[m2, m5])/126 -
		(2*CartesianPair[i1, m3]*CartesianPair[i2, m1]*CartesianPair[i3, m4]*CartesianPair[i4, i5]*CartesianPair[m2, m5])/63 +
		(19*CartesianPair[i1, m1]*CartesianPair[i2, m3]*CartesianPair[i3, m4]*CartesianPair[i4, i5]*CartesianPair[m2, m5])/126 -
		(13*CartesianPair[i1, m4]*CartesianPair[i2, m3]*CartesianPair[i3, i5]*CartesianPair[i4, m1]*CartesianPair[m2, m5])/63 +
		(13*CartesianPair[i1, m3]*CartesianPair[i2, m4]*CartesianPair[i3, i5]*CartesianPair[i4, m1]*CartesianPair[m2, m5])/63 +
		(7*CartesianPair[i1, m4]*CartesianPair[i2, i5]*CartesianPair[i3, m3]*CartesianPair[i4, m1]*CartesianPair[m2, m5])/36 -
		(CartesianPair[i1, i5]*CartesianPair[i2, m4]*CartesianPair[i3, m3]*CartesianPair[i4, m1]*CartesianPair[m2, m5])/7 -
		(79*CartesianPair[i1, m3]*CartesianPair[i2, i5]*CartesianPair[i3, m4]*CartesianPair[i4, m1]*CartesianPair[m2, m5])/252 +
		(CartesianPair[i1, i5]*CartesianPair[i2, m3]*CartesianPair[i3, m4]*CartesianPair[i4, m1]*CartesianPair[m2, m5])/7 +
		(CartesianPair[i1, m4]*CartesianPair[i2, m1]*CartesianPair[i3, i5]*CartesianPair[i4, m3]*CartesianPair[m2, m5])/36 -
		(CartesianPair[i1, m1]*CartesianPair[i2, m4]*CartesianPair[i3, i5]*CartesianPair[i4, m3]*CartesianPair[m2, m5])/36 -
		(79*CartesianPair[i1, m4]*CartesianPair[i2, i5]*CartesianPair[i3, m1]*CartesianPair[i4, m3]*CartesianPair[m2, m5])/252 +
		(CartesianPair[i1, i5]*CartesianPair[i2, m4]*CartesianPair[i3, m1]*CartesianPair[i4, m3]*CartesianPair[m2, m5])/42 -
		(13*CartesianPair[i1, m1]*CartesianPair[i2, i5]*CartesianPair[i3, m4]*CartesianPair[i4, m3]*CartesianPair[m2, m5])/126 -
		(CartesianPair[i1, i5]*CartesianPair[i2, m1]*CartesianPair[i3, m4]*CartesianPair[i4, m3]*CartesianPair[m2, m5])/42 +
		(59*CartesianPair[i1, m3]*CartesianPair[i2, m1]*CartesianPair[i3, i5]*CartesianPair[i4, m4]*CartesianPair[m2, m5])/252 -
		(59*CartesianPair[i1, m1]*CartesianPair[i2, m3]*CartesianPair[i3, i5]*CartesianPair[i4, m4]*CartesianPair[m2, m5])/252 -
		(23*CartesianPair[i1, m3]*CartesianPair[i2, i5]*CartesianPair[i3, m1]*CartesianPair[i4, m4]*CartesianPair[m2, m5])/252 +
		(CartesianPair[i1, i5]*CartesianPair[i2, m3]*CartesianPair[i3, m1]*CartesianPair[i4, m4]*CartesianPair[m2, m5])/6 +
		(79*CartesianPair[i1, m1]*CartesianPair[i2, i5]*CartesianPair[i3, m3]*CartesianPair[i4, m4]*CartesianPair[m2, m5])/126 -
		(CartesianPair[i1, i5]*CartesianPair[i2, m1]*CartesianPair[i3, m3]*CartesianPair[i4, m4]*CartesianPair[m2, m5])/6 -
		(3*CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[i5, m1]*CartesianPair[m2, m5])/28 +
		(17*CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m3]*CartesianPair[i5, m1]*CartesianPair[m2, m5])/63 +
		(19*CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[i5, m1]*CartesianPair[m2, m5])/84 -
		(17*CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m4]*CartesianPair[i5, m1]*CartesianPair[m2, m5])/63 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[i5, m1]*CartesianPair[m2, m5])/6 -
		(41*CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m3]*CartesianPair[i5, m1]*CartesianPair[m2, m5])/252 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m3]*CartesianPair[i5, m1]*CartesianPair[m2, m5])/18 -
		(5*CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[i5, m1]*CartesianPair[m2, m5])/42 +
		(59*CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m4]*CartesianPair[i5, m1]*CartesianPair[m2, m5])/252 -
		(31*CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m4]*CartesianPair[i5, m1]*CartesianPair[m2, m5])/126 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[i5, m3]*CartesianPair[m2, m5])/21 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m1]*CartesianPair[i5, m3]*CartesianPair[m2, m5])/36 +
		(CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[i5, m3]*CartesianPair[m2, m5])/84 -
		(CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, m4]*CartesianPair[i5, m3]*CartesianPair[m2, m5])/36 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[i5, m3]*CartesianPair[m2, m5])/42 -
		(13*CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, m1]*CartesianPair[i5, m3]*CartesianPair[m2, m5])/252 +
		(11*CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, m1]*CartesianPair[i5, m3]*CartesianPair[m2, m5])/126 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[i5, m3]*CartesianPair[m2, m5])/7 +
		(5*CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, m4]*CartesianPair[i5, m3]*CartesianPair[m2, m5])/126 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, m4]*CartesianPair[i5, m3]*CartesianPair[m2, m5])/63 +
		(2*CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[i5, m4]*CartesianPair[m2, m5])/21 -
		(61*CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m1]*CartesianPair[i5, m4]*CartesianPair[m2, m5])/252 -
		(23*CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[i5, m4]*CartesianPair[m2, m5])/84 +
		(61*CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, m3]*CartesianPair[i5, m4]*CartesianPair[m2, m5])/252 -
		(CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[i5, m4]*CartesianPair[m2, m5])/42 +
		(31*CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m1]*CartesianPair[i5, m4]*CartesianPair[m2, m5])/252 -
		(5*CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m1]*CartesianPair[i5, m4]*CartesianPair[m2, m5])/126 +
		(CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[i5, m4]*CartesianPair[m2, m5])/7 -
		(23*CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, m3]*CartesianPair[i5, m4]*CartesianPair[m2, m5])/126 +
		(10*CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, m3]*CartesianPair[i5, m4]*CartesianPair[m2, m5])/63 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/42 +
		(CartesianPair[i1, i5]*CartesianPair[i2, m4]*CartesianPair[i3, i4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/7 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/3 -
		(4*CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/7 -
		(8*CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/21 +
		(31*CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/42 -
		(2*CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/7 +
		(23*CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/42 -
		(2*CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, i5]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/7 +
		(11*CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/42 -
		(17*CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/21 +
		(11*CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/42 -
		(2*CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/21 +
		(3*CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/14 -
		(2*CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m4]*CartesianPair[m1, m3]*CartesianPair[m2, m5])/21 +
		(13*CartesianPair[i1, m3]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/42 -
		(2*CartesianPair[i1, i5]*CartesianPair[i2, m3]*CartesianPair[i3, i4]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/7 -
		(17*CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/21 +
		(15*CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/14 +
		(9*CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/14 -
		(9*CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m3]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/7 +
		(8*CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/21 -
		(17*CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/21 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, i5]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/2 -
		(2*CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/7 +
		(31*CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m3]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/42 -
		(5*CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m3]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/21 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m3]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/14 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m3]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/21 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m3]*CartesianPair[m1, m4]*CartesianPair[m2, m5])/21 +
		(2*CartesianPair[i1, m5]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/21 +
		(2*CartesianPair[i1, i5]*CartesianPair[i2, m5]*CartesianPair[i3, i4]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/21 -
		(2*CartesianPair[i1, m5]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/21 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m5]*CartesianPair[i3, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/21 -
		(CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/6 -
		(CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/21 -
		(CartesianPair[i1, m5]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/42 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m5]*CartesianPair[i4, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/6 +
		(5*CartesianPair[i1, i2]*CartesianPair[i3, m5]*CartesianPair[i4, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/21 +
		(CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/42 -
		(2*CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/21 +
		(2*CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/21 +
		(11*CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/42 -
		(11*CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m5]*CartesianPair[m1, m2]*CartesianPair[m3, m4])/42 +
		(2*CartesianPair[i1, m2]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/21 -
		(11*CartesianPair[i1, i5]*CartesianPair[i2, m2]*CartesianPair[i3, i4]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/42 -
		(5*CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/21 +
		(11*CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, i5]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/42 +
		(3*CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/7 -
		(2*CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m2]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/7 +
		(5*CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/42 -
		(5*CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, i5]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/42 -
		(2*CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/21 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m2]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/7 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m2]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/42 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m2]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/42 -
		(CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m2]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/7 +
		(2*CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m2]*CartesianPair[m1, m5]*CartesianPair[m3, m4])/21 -
		(11*CartesianPair[i1, m1]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/42 +
		(2*CartesianPair[i1, i5]*CartesianPair[i2, m1]*CartesianPair[i3, i4]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/21 +
		(11*CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/42 -
		(5*CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, i5]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/21 -
		(CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/6 +
		(13*CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m1]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/42 +
		(5*CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, i5]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/42 -
		(5*CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, i5]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/42 +
		(CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/42 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m1]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/42 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m1]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/42 -
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m1]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/42 -
		(2*CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m1]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/21 +
		(2*CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m1]*CartesianPair[m2, m5]*CartesianPair[m3, m4])/21 -
		(23*CartesianPair[i1, m4]*CartesianPair[i2, m2]*CartesianPair[i3, m1]*CartesianPair[i4, i5]*CartesianPair[m3, m5])/126 +
		(4*CartesianPair[i1, m2]*CartesianPair[i2, m4]*CartesianPair[i3, m1]*CartesianPair[i4, i5]*CartesianPair[m3, m5])/63 +
		(23*CartesianPair[i1, m4]*CartesianPair[i2, m1]*CartesianPair[i3, m2]*CartesianPair[i4, i5]*CartesianPair[m3, m5])/126 -
		(4*CartesianPair[i1, m1]*CartesianPair[i2, m4]*CartesianPair[i3, m2]*CartesianPair[i4, i5]*CartesianPair[m3, m5])/63 +
		(31*CartesianPair[i1, m2]*CartesianPair[i2, m1]*CartesianPair[i3, m4]*CartesianPair[i4, i5]*CartesianPair[m3, m5])/126 -
		(31*CartesianPair[i1, m1]*CartesianPair[i2, m2]*CartesianPair[i3, m4]*CartesianPair[i4, i5]*CartesianPair[m3, m5])/126 +
		(61*CartesianPair[i1, m4]*CartesianPair[i2, m2]*CartesianPair[i3, i5]*CartesianPair[i4, m1]*CartesianPair[m3, m5])/252 -
		(61*CartesianPair[i1, m2]*CartesianPair[i2, m4]*CartesianPair[i3, i5]*CartesianPair[i4, m1]*CartesianPair[m3, m5])/252 -
		(13*CartesianPair[i1, m4]*CartesianPair[i2, i5]*CartesianPair[i3, m2]*CartesianPair[i4, m1]*CartesianPair[m3, m5])/63 +
		(11*CartesianPair[i1, i5]*CartesianPair[i2, m4]*CartesianPair[i3, m2]*CartesianPair[i4, m1]*CartesianPair[m3, m5])/126 +
		(CartesianPair[i1, m2]*CartesianPair[i2, i5]*CartesianPair[i3, m4]*CartesianPair[i4, m1]*CartesianPair[m3, m5])/36 -
		(11*CartesianPair[i1, i5]*CartesianPair[i2, m2]*CartesianPair[i3, m4]*CartesianPair[i4, m1]*CartesianPair[m3, m5])/126 -
		(61*CartesianPair[i1, m4]*CartesianPair[i2, m1]*CartesianPair[i3, i5]*CartesianPair[i4, m2]*CartesianPair[m3, m5])/252 +
		(61*CartesianPair[i1, m1]*CartesianPair[i2, m4]*CartesianPair[i3, i5]*CartesianPair[i4, m2]*CartesianPair[m3, m5])/252 +
		(13*CartesianPair[i1, m4]*CartesianPair[i2, i5]*CartesianPair[i3, m1]*CartesianPair[i4, m2]*CartesianPair[m3, m5])/63 -
		(11*CartesianPair[i1, i5]*CartesianPair[i2, m4]*CartesianPair[i3, m1]*CartesianPair[i4, m2]*CartesianPair[m3, m5])/126 -
		(CartesianPair[i1, m1]*CartesianPair[i2, i5]*CartesianPair[i3, m4]*CartesianPair[i4, m2]*CartesianPair[m3, m5])/36 +
		(11*CartesianPair[i1, i5]*CartesianPair[i2, m1]*CartesianPair[i3, m4]*CartesianPair[i4, m2]*CartesianPair[m3, m5])/126 -
		(61*CartesianPair[i1, m2]*CartesianPair[i2, m1]*CartesianPair[i3, i5]*CartesianPair[i4, m4]*CartesianPair[m3, m5])/126 +
		(61*CartesianPair[i1, m1]*CartesianPair[i2, m2]*CartesianPair[i3, i5]*CartesianPair[i4, m4]*CartesianPair[m3, m5])/126 +
		(59*CartesianPair[i1, m2]*CartesianPair[i2, i5]*CartesianPair[i3, m1]*CartesianPair[i4, m4]*CartesianPair[m3, m5])/252 -
		(11*CartesianPair[i1, i5]*CartesianPair[i2, m2]*CartesianPair[i3, m1]*CartesianPair[i4, m4]*CartesianPair[m3, m5])/63 -
		(59*CartesianPair[i1, m1]*CartesianPair[i2, i5]*CartesianPair[i3, m2]*CartesianPair[i4, m4]*CartesianPair[m3, m5])/252 +
		(11*CartesianPair[i1, i5]*CartesianPair[i2, m1]*CartesianPair[i3, m2]*CartesianPair[i4, m4]*CartesianPair[m3, m5])/63 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[i5, m1]*CartesianPair[m3, m5])/28 -
		(13*CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m2]*CartesianPair[i5, m1]*CartesianPair[m3, m5])/84 -
		(3*CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[i5, m1]*CartesianPair[m3, m5])/14 +
		(13*CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m4]*CartesianPair[i5, m1]*CartesianPair[m3, m5])/84 +
		(3*CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[i5, m1]*CartesianPair[m3, m5])/14 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m4]*CartesianPair[i5, m1]*CartesianPair[m3, m5])/4 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, m4]*CartesianPair[i5, m1]*CartesianPair[m3, m5])/14 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[i5, m2]*CartesianPair[m3, m5])/28 +
		(13*CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, m1]*CartesianPair[i5, m2]*CartesianPair[m3, m5])/84 +
		(3*CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[i5, m2]*CartesianPair[m3, m5])/14 -
		(13*CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, m4]*CartesianPair[i5, m2]*CartesianPair[m3, m5])/84 -
		(3*CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m4]*CartesianPair[i5, m2]*CartesianPair[m3, m5])/14 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, m4]*CartesianPair[i5, m2]*CartesianPair[m3, m5])/4 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, m4]*CartesianPair[i5, m2]*CartesianPair[m3, m5])/14 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[i5, m4]*CartesianPair[m3, m5])/4 +
		(13*CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m1]*CartesianPair[i5, m4]*CartesianPair[m3, m5])/42 +
		(CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[i5, m4]*CartesianPair[m3, m5])/4 -
		(13*CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, m2]*CartesianPair[i5, m4]*CartesianPair[m3, m5])/42 +
		(3*CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[i5, m4]*CartesianPair[m3, m5])/14 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m1]*CartesianPair[i5, m4]*CartesianPair[m3, m5])/4 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, m1]*CartesianPair[i5, m4]*CartesianPair[m3, m5])/14 -
		(3*CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[i5, m4]*CartesianPair[m3, m5])/14 +
		(CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, m2]*CartesianPair[i5, m4]*CartesianPair[m3, m5])/4 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, m2]*CartesianPair[i5, m4]*CartesianPair[m3, m5])/14 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/42 -
		(CartesianPair[i1, i5]*CartesianPair[i2, m4]*CartesianPair[i3, i4]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/42 +
		(CartesianPair[i1, m4]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/42 +
		(CartesianPair[i1, i4]*CartesianPair[i2, m4]*CartesianPair[i3, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/6 +
		(CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m4]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/42 -
		(5*CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m4]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/21 -
		(CartesianPair[i1, m4]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/42 -
		(CartesianPair[i1, i3]*CartesianPair[i2, m4]*CartesianPair[i4, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/6 +
		(5*CartesianPair[i1, i2]*CartesianPair[i3, m4]*CartesianPair[i4, i5]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/21 +
		(11*CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m4]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/42 -
		(11*CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m4]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/42 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m4]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/42 -
		(2*CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m4]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/21 +
		(2*CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m4]*CartesianPair[m1, m2]*CartesianPair[m3, m5])/21 -
		(5*CartesianPair[i1, m2]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/21 +
		(11*CartesianPair[i1, i5]*CartesianPair[i2, m2]*CartesianPair[i3, i4]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/42 +
		(43*CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/42 -
		(25*CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, i5]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/21 -
		(4*CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/7 +
		(15*CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m2]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/14 -
		(13*CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/21 +
		(13*CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, i5]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/14 -
		(8*CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, i5]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/21 +
		(5*CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/21 -
		(4*CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m2]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/7 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m2]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/6 +
		(5*CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m2]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/42 -
		(2*CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m2]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/7 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m2]*CartesianPair[m1, m4]*CartesianPair[m3, m5])/21 +
		(11*CartesianPair[i1, m1]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/42 -
		(5*CartesianPair[i1, i5]*CartesianPair[i2, m1]*CartesianPair[i3, i4]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/21 -
		(25*CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/21 +
		(43*CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, i5]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/42 +
		(25*CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/42 -
		(17*CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m1]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/21 +
		(31*CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/42 -
		(17*CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, i5]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/21 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, i5]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/7 -
		(5*CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/21 +
		(CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m1]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/3 +
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m1]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/42 -
		(4*CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m1]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/21 +
		(19*CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m1]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/42 -
		(2*CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m1]*CartesianPair[m2, m4]*CartesianPair[m3, m5])/21 +
		(10*CartesianPair[i1, m3]*CartesianPair[i2, m2]*CartesianPair[i3, m1]*CartesianPair[i4, i5]*CartesianPair[m4, m5])/63 -
		(16*CartesianPair[i1, m2]*CartesianPair[i2, m3]*CartesianPair[i3, m1]*CartesianPair[i4, i5]*CartesianPair[m4, m5])/63 -
		(16*CartesianPair[i1, m3]*CartesianPair[i2, m1]*CartesianPair[i3, m2]*CartesianPair[i4, i5]*CartesianPair[m4, m5])/63 -
		(5*CartesianPair[i1, m1]*CartesianPair[i2, m3]*CartesianPair[i3, m2]*CartesianPair[i4, i5]*CartesianPair[m4, m5])/63 -
		(5*CartesianPair[i1, m2]*CartesianPair[i2, m1]*CartesianPair[i3, m3]*CartesianPair[i4, i5]*CartesianPair[m4, m5])/63 +
		(32*CartesianPair[i1, m1]*CartesianPair[i2, m2]*CartesianPair[i3, m3]*CartesianPair[i4, i5]*CartesianPair[m4, m5])/63 -
		(23*CartesianPair[i1, m3]*CartesianPair[i2, m2]*CartesianPair[i3, i5]*CartesianPair[i4, m1]*CartesianPair[m4, m5])/126 +
		(23*CartesianPair[i1, m2]*CartesianPair[i2, m3]*CartesianPair[i3, i5]*CartesianPair[i4, m1]*CartesianPair[m4, m5])/126 +
		(23*CartesianPair[i1, m3]*CartesianPair[i2, i5]*CartesianPair[i3, m2]*CartesianPair[i4, m1]*CartesianPair[m4, m5])/126 +
		(2*CartesianPair[i1, i5]*CartesianPair[i2, m3]*CartesianPair[i3, m2]*CartesianPair[i4, m1]*CartesianPair[m4, m5])/63 -
		(4*CartesianPair[i1, m2]*CartesianPair[i2, i5]*CartesianPair[i3, m3]*CartesianPair[i4, m1]*CartesianPair[m4, m5])/63 -
		(2*CartesianPair[i1, i5]*CartesianPair[i2, m2]*CartesianPair[i3, m3]*CartesianPair[i4, m1]*CartesianPair[m4, m5])/63 +
		(4*CartesianPair[i1, m3]*CartesianPair[i2, m1]*CartesianPair[i3, i5]*CartesianPair[i4, m2]*CartesianPair[m4, m5])/63 -
		(4*CartesianPair[i1, m1]*CartesianPair[i2, m3]*CartesianPair[i3, i5]*CartesianPair[i4, m2]*CartesianPair[m4, m5])/63 -
		(11*CartesianPair[i1, m3]*CartesianPair[i2, i5]*CartesianPair[i3, m1]*CartesianPair[i4, m2]*CartesianPair[m4, m5])/126 +
		(4*CartesianPair[i1, i5]*CartesianPair[i2, m3]*CartesianPair[i3, m1]*CartesianPair[i4, m2]*CartesianPair[m4, m5])/63 -
		(19*CartesianPair[i1, m1]*CartesianPair[i2, i5]*CartesianPair[i3, m3]*CartesianPair[i4, m2]*CartesianPair[m4, m5])/126 -
		(4*CartesianPair[i1, i5]*CartesianPair[i2, m1]*CartesianPair[i3, m3]*CartesianPair[i4, m2]*CartesianPair[m4, m5])/63 +
		(31*CartesianPair[i1, m2]*CartesianPair[i2, m1]*CartesianPair[i3, i5]*CartesianPair[i4, m3]*CartesianPair[m4, m5])/126 -
		(31*CartesianPair[i1, m1]*CartesianPair[i2, m2]*CartesianPair[i3, i5]*CartesianPair[i4, m3]*CartesianPair[m4, m5])/126 -
		(2*CartesianPair[i1, m2]*CartesianPair[i2, i5]*CartesianPair[i3, m1]*CartesianPair[i4, m3]*CartesianPair[m4, m5])/63 +
		(2*CartesianPair[i1, i5]*CartesianPair[i2, m2]*CartesianPair[i3, m1]*CartesianPair[i4, m3]*CartesianPair[m4, m5])/63 +
		(19*CartesianPair[i1, m1]*CartesianPair[i2, i5]*CartesianPair[i3, m2]*CartesianPair[i4, m3]*CartesianPair[m4, m5])/126 -
		(2*CartesianPair[i1, i5]*CartesianPair[i2, m1]*CartesianPair[i3, m2]*CartesianPair[i4, m3]*CartesianPair[m4, m5])/63 +
		(3*CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, m2]*CartesianPair[i5, m1]*CartesianPair[m4, m5])/14 +
		(5*CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[i5, m1]*CartesianPair[m4, m5])/42 -
		(3*CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m3]*CartesianPair[i5, m1]*CartesianPair[m4, m5])/14 -
		(5*CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m2]*CartesianPair[i5, m1]*CartesianPair[m4, m5])/42 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m2]*CartesianPair[i5, m1]*CartesianPair[m4, m5])/7 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[i5, m1]*CartesianPair[m4, m5])/7 +
		(5*CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m3]*CartesianPair[i5, m1]*CartesianPair[m4, m5])/21 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, m3]*CartesianPair[i5, m1]*CartesianPair[m4, m5])/7 -
		(CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[i5, m2]*CartesianPair[m4, m5])/42 -
		(3*CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[i5, m2]*CartesianPair[m4, m5])/14 -
		(5*CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, m1]*CartesianPair[i5, m2]*CartesianPair[m4, m5])/42 +
		(CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, m1]*CartesianPair[i5, m2]*CartesianPair[m4, m5])/7 +
		(CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[i5, m2]*CartesianPair[m4, m5])/7 -
		(5*CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, m3]*CartesianPair[i5, m2]*CartesianPair[m4, m5])/42 +
		(3*CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[i5, m3]*CartesianPair[m4, m5])/14 -
		(3*CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, m1]*CartesianPair[i5, m3]*CartesianPair[m4, m5])/14 -
		(2*CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[i5, m3]*CartesianPair[m4, m5])/21 +
		(3*CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, m2]*CartesianPair[i5, m3]*CartesianPair[m4, m5])/14 -
		(CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[i5, m3]*CartesianPair[m4, m5])/7 +
		(5*CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, m1]*CartesianPair[i5, m3]*CartesianPair[m4, m5])/21 -
		(CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, m1]*CartesianPair[i5, m3]*CartesianPair[m4, m5])/7 +
		(CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[i5, m3]*CartesianPair[m4, m5])/7 -
		(5*CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, m2]*CartesianPair[i5, m3]*CartesianPair[m4, m5])/42 -
		(5*CartesianPair[i1, m3]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/42 -
		(5*CartesianPair[i1, i5]*CartesianPair[i2, m3]*CartesianPair[i3, i4]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/42 +
		(CartesianPair[i1, m3]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/7 -
		(8*CartesianPair[i1, i4]*CartesianPair[i2, m3]*CartesianPair[i3, i5]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/21 +
		(5*CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m3]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/21 +
		(CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m3]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/2 +
		(2*CartesianPair[i1, m3]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/21 +
		(13*CartesianPair[i1, i3]*CartesianPair[i2, m3]*CartesianPair[i4, i5]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/21 -
		(5*CartesianPair[i1, i2]*CartesianPair[i3, m3]*CartesianPair[i4, i5]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/6 -
		(CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m3]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/42 -
		(2*CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m3]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/7 +
		(5*CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m3]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/21 -
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m3]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/42 -
		(2*CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m3]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/7 +
		(5*CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m3]*CartesianPair[m1, m2]*CartesianPair[m4, m5])/21 +
		(5*CartesianPair[i1, m2]*CartesianPair[i2, i5]*CartesianPair[i3, i4]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/42 -
		(17*CartesianPair[i1, m2]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/21 +
		(13*CartesianPair[i1, i4]*CartesianPair[i2, m2]*CartesianPair[i3, i5]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/14 +
		(5*CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m2]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/42 -
		(17*CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m2]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/21 +
		(13*CartesianPair[i1, m2]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/21 -
		(17*CartesianPair[i1, i3]*CartesianPair[i2, m2]*CartesianPair[i4, i5]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/14 +
		(13*CartesianPair[i1, i2]*CartesianPair[i3, m2]*CartesianPair[i4, i5]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/21 -
		(CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m2]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/6 +
		(23*CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m2]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/42 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m2]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/6 -
		(CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m2]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/6 +
		(23*CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m2]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/42 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m2]*CartesianPair[m1, m3]*CartesianPair[m4, m5])/6 +
		(5*CartesianPair[i1, i5]*CartesianPair[i2, m1]*CartesianPair[i3, i4]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/42 +
		(31*CartesianPair[i1, m1]*CartesianPair[i2, i4]*CartesianPair[i3, i5]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/42 -
		(13*CartesianPair[i1, i4]*CartesianPair[i2, m1]*CartesianPair[i3, i5]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/21 -
		(5*CartesianPair[i1, i5]*CartesianPair[i2, i4]*CartesianPair[i3, m1]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/14 +
		(8*CartesianPair[i1, i4]*CartesianPair[i2, i5]*CartesianPair[i3, m1]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/21 -
		(5*CartesianPair[i1, m1]*CartesianPair[i2, i3]*CartesianPair[i4, i5]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/6 +
		(13*CartesianPair[i1, i3]*CartesianPair[i2, m1]*CartesianPair[i4, i5]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/21 +
		(2*CartesianPair[i1, i2]*CartesianPair[i3, m1]*CartesianPair[i4, i5]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/21 +
		(5*CartesianPair[i1, i5]*CartesianPair[i2, i3]*CartesianPair[i4, m1]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/21 -
		(2*CartesianPair[i1, i3]*CartesianPair[i2, i5]*CartesianPair[i4, m1]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/7 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i5]*CartesianPair[i4, m1]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/42 +
		(5*CartesianPair[i1, i4]*CartesianPair[i2, i3]*CartesianPair[i5, m1]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/21 -
		(2*CartesianPair[i1, i3]*CartesianPair[i2, i4]*CartesianPair[i5, m1]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/7 -
		(CartesianPair[i1, i2]*CartesianPair[i3, i4]*CartesianPair[i5, m1]*CartesianPair[m2, m3]*CartesianPair[m4, m5])/42
};


FCPrint[1,"FMCartesianTensorDecomposition loaded."];
End[]
