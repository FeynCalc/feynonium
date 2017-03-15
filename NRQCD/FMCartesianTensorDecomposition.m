(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: FMCartesianTensorDecomposition									*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2016 Vladyslav Shtabovenko
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
			If[MatchQ[OptionValue[FCVerbose], _Integer?Positive | 0],
				ctdVerbose=OptionValue[FCVerbose]
			];
		];

		If[ !OptionValue[FCI],
			ex = FCI[expr],
			ex = expr
		];

		tmp = Uncontract[ex, Sequence@@vecs, CPair -> All, FCI->True];

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

		If[ !MatchQ[projList/.Times->List/. projHead[z_CPair]:>projHead[{z}],{projHead[{__CPair}]..}],
			Message[FMCartesianTensorDecomposition::failmsg,"Incorrect structure of Cartesian tensors."];
			Abort[];
		];

		If[ FCGetDimensions[projList]=!={3},
			Message[FMCartesianTensorDecomposition::failmsg, "Projections in other than 3 dimensions are not supported."];
			Abort[];
		];

		projListEval = projList /. CPair -> CPairContract /. CPairContract -> CPair //. projHead[CPair[a__CMomentum] b_] :> CPair[a] projHead[b] /. projHead[]->1;

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
	projHead[CPair[_CIndex, _CMomentum ]] :>0,

	(* Rank 2*)
	projHead[CPair[i1_CIndex, m1_CMomentum ] CPair[i2_CIndex, m2_CMomentum]] :>
		CPair[m1,m2] CPair[i1,i2]/3,

	(* Rank 3*)
	projHead[CPair[i1_CIndex, m1_CMomentum ] CPair[i2_CIndex, m2_CMomentum] CPair[i3_CIndex, m3_CMomentum]] :>
		-(CPair[i1, m3]*CPair[i2, m2]*CPair[i3, m1])/6 + (CPair[i1, m2]*CPair[i2, m3]*CPair[i3, m1])/6 +
		(CPair[i1, m3]*CPair[i2, m1]*CPair[i3, m2])/6 - (CPair[i1, m1]*CPair[i2, m3]*CPair[i3, m2])/6 -
		(CPair[i1, m2]*CPair[i2, m1]*CPair[i3, m3])/6 + (CPair[i1, m1]*CPair[i2, m2]*CPair[i3, m3])/6,

	(* Rank 4*)
	projHead[CPair[i1_CIndex, m1_CMomentum ] CPair[i2_CIndex, m2_CMomentum] CPair[i3_CIndex, m3_CMomentum] CPair[i4_CIndex, m4_CMomentum]] :>
		(2*CPair[i1, i4]*CPair[i2, i3]*CPair[m1, m4]*CPair[m2, m3])/15 -
		(CPair[i1, i3]*CPair[i2, i4]*CPair[m1, m4]*CPair[m2, m3])/30 -
		(CPair[i1, i2]*CPair[i3, i4]*CPair[m1, m4]*CPair[m2, m3])/30 -
		(CPair[i1, i4]*CPair[i2, i3]*CPair[m1, m3]*CPair[m2, m4])/30 +
		(2*CPair[i1, i3]*CPair[i2, i4]*CPair[m1, m3]*CPair[m2, m4])/15 -
		(CPair[i1, i2]*CPair[i3, i4]*CPair[m1, m3]*CPair[m2, m4])/30 -
		(CPair[i1, i4]*CPair[i2, i3]*CPair[m1, m2]*CPair[m3, m4])/30 -
		(CPair[i1, i3]*CPair[i2, i4]*CPair[m1, m2]*CPair[m3, m4])/30 +
		(2*CPair[i1, i2]*CPair[i3, i4]*CPair[m1, m2]*CPair[m3, m4])/15,

	(* Rank 5*)
	projHead[CPair[i1_CIndex, m1_CMomentum ] CPair[i2_CIndex, m2_CMomentum] CPair[i3_CIndex, m3_CMomentum]*
		CPair[i4_CIndex, m4_CMomentum] CPair[i5_CIndex, m5_CMomentum]] :>
		-(CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m4]*CPair[i5, m3]*CPair[m1, m2])/30 -
		(CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m4]*CPair[i5, m3]*CPair[m1, m2])/30 +
		(CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m3]*CPair[m1, m2])/30 +
		(CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m5]*CPair[i5, m3]*CPair[m1, m2])/30 +
		(CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m4]*CPair[i5, m3]*CPair[m1, m2])/30 +
		(CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m4]*CPair[i5, m3]*CPair[m1, m2])/30 -
		(CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m4]*CPair[i5, m3]*CPair[m1, m2])/10 -
		(CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m3]*CPair[m1, m2])/30 -
		(CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m5]*CPair[i5, m3]*CPair[m1, m2])/30 +
		(CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m5]*CPair[i5, m3]*CPair[m1, m2])/10 +
		(CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m3]*CPair[i5, m4]*CPair[m1, m2])/30 +
		(CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m3]*CPair[i5, m4]*CPair[m1, m2])/30 -
		(CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m4]*CPair[m1, m2])/30 -
		(CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m5]*CPair[i5, m4]*CPair[m1, m2])/30 -
		(CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m3]*CPair[i5, m4]*CPair[m1, m2])/30 -
		(CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m3]*CPair[i5, m4]*CPair[m1, m2])/30 +
		(CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m3]*CPair[i5, m4]*CPair[m1, m2])/10 +
		(CPair[i1, m3]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m4]*CPair[m1, m2])/30 +
		(CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m5]*CPair[i5, m4]*CPair[m1, m2])/30 -
		(CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m5]*CPair[i5, m4]*CPair[m1, m2])/10 -
		(CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m3]*CPair[i5, m5]*CPair[m1, m2])/30 -
		(CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m3]*CPair[i5, m5]*CPair[m1, m2])/30 +
		(CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m4]*CPair[i5, m5]*CPair[m1, m2])/30 +
		(CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m4]*CPair[i5, m5]*CPair[m1, m2])/30 +
		(CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m3]*CPair[i5, m5]*CPair[m1, m2])/30 +
		(CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m3]*CPair[i5, m5]*CPair[m1, m2])/30 -
		(CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m3]*CPair[i5, m5]*CPair[m1, m2])/10 -
		(CPair[i1, m3]*CPair[i2, i3]*CPair[i4, m4]*CPair[i5, m5]*CPair[m1, m2])/30 -
		(CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m4]*CPair[i5, m5]*CPair[m1, m2])/30 +
		(CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m4]*CPair[i5, m5]*CPair[m1, m2])/10 -
		(CPair[i1, m5]*CPair[i2, m4]*CPair[i3, i4]*CPair[i5, m2]*CPair[m1, m3])/30 +
		(CPair[i1, m4]*CPair[i2, m5]*CPair[i3, i4]*CPair[i5, m2]*CPair[m1, m3])/30 +
		(CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m4]*CPair[i5, m2]*CPair[m1, m3])/30 -
		(CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m5]*CPair[i5, m2]*CPair[m1, m3])/30 +
		(CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m4]*CPair[i5, m2]*CPair[m1, m3])/30 -
		(CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m4]*CPair[i5, m2]*CPair[m1, m3])/10 +
		(CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m4]*CPair[i5, m2]*CPair[m1, m3])/30 -
		(CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m2]*CPair[m1, m3])/30 +
		(CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m5]*CPair[i5, m2]*CPair[m1, m3])/10 -
		(CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m5]*CPair[i5, m2]*CPair[m1, m3])/30 +
		(CPair[i1, m5]*CPair[i2, m2]*CPair[i3, i4]*CPair[i5, m4]*CPair[m1, m3])/30 -
		(CPair[i1, m2]*CPair[i2, m5]*CPair[i3, i4]*CPair[i5, m4]*CPair[m1, m3])/30 -
		(CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m2]*CPair[i5, m4]*CPair[m1, m3])/30 +
		(CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m5]*CPair[i5, m4]*CPair[m1, m3])/30 -
		(CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m2]*CPair[i5, m4]*CPair[m1, m3])/30 +
		(CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m2]*CPair[i5, m4]*CPair[m1, m3])/10 -
		(CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m2]*CPair[i5, m4]*CPair[m1, m3])/30 +
		(CPair[i1, m2]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m4]*CPair[m1, m3])/30 -
		(CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m5]*CPair[i5, m4]*CPair[m1, m3])/10 +
		(CPair[i1, i2]*CPair[i3, m2]*CPair[i4, m5]*CPair[i5, m4]*CPair[m1, m3])/30 -
		(CPair[i1, m4]*CPair[i2, m2]*CPair[i3, i4]*CPair[i5, m5]*CPair[m1, m3])/30 +
		(CPair[i1, m2]*CPair[i2, m4]*CPair[i3, i4]*CPair[i5, m5]*CPair[m1, m3])/30 +
		(CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m2]*CPair[i5, m5]*CPair[m1, m3])/30 -
		(CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m4]*CPair[i5, m5]*CPair[m1, m3])/30 +
		(CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m2]*CPair[i5, m5]*CPair[m1, m3])/30 -
		(CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m2]*CPair[i5, m5]*CPair[m1, m3])/10 +
		(CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m2]*CPair[i5, m5]*CPair[m1, m3])/30 -
		(CPair[i1, m2]*CPair[i2, i3]*CPair[i4, m4]*CPair[i5, m5]*CPair[m1, m3])/30 +
		(CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m4]*CPair[i5, m5]*CPair[m1, m3])/10 -
		(CPair[i1, i2]*CPair[i3, m2]*CPair[i4, m4]*CPair[i5, m5]*CPair[m1, m3])/30 -
		(CPair[i1, m5]*CPair[i2, m3]*CPair[i3, i4]*CPair[i5, m2]*CPair[m1, m4])/30 +
		(CPair[i1, m3]*CPair[i2, m5]*CPair[i3, i4]*CPair[i5, m2]*CPair[m1, m4])/30 +
		(CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m3]*CPair[i5, m2]*CPair[m1, m4])/30 -
		(CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m3]*CPair[i5, m2]*CPair[m1, m4])/10 -
		(CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m2]*CPair[m1, m4])/30 +
		(CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m5]*CPair[i5, m2]*CPair[m1, m4])/10 +
		(CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m3]*CPair[i5, m2]*CPair[m1, m4])/30 -
		(CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m3]*CPair[i5, m2]*CPair[m1, m4])/30 -
		(CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m5]*CPair[i5, m2]*CPair[m1, m4])/30 +
		(CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m5]*CPair[i5, m2]*CPair[m1, m4])/30 +
		(CPair[i1, m5]*CPair[i2, m2]*CPair[i3, i4]*CPair[i5, m3]*CPair[m1, m4])/30 -
		(CPair[i1, m2]*CPair[i2, m5]*CPair[i3, i4]*CPair[i5, m3]*CPair[m1, m4])/30 -
		(CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m2]*CPair[i5, m3]*CPair[m1, m4])/30 +
		(CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m2]*CPair[i5, m3]*CPair[m1, m4])/10 +
		(CPair[i1, m2]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m3]*CPair[m1, m4])/30 -
		(CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m5]*CPair[i5, m3]*CPair[m1, m4])/10 -
		(CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m2]*CPair[i5, m3]*CPair[m1, m4])/30 +
		(CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m2]*CPair[i5, m3]*CPair[m1, m4])/30 +
		(CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m5]*CPair[i5, m3]*CPair[m1, m4])/30 -
		(CPair[i1, i2]*CPair[i3, m2]*CPair[i4, m5]*CPair[i5, m3]*CPair[m1, m4])/30 -
		(CPair[i1, m3]*CPair[i2, m2]*CPair[i3, i4]*CPair[i5, m5]*CPair[m1, m4])/30 +
		(CPair[i1, m2]*CPair[i2, m3]*CPair[i3, i4]*CPair[i5, m5]*CPair[m1, m4])/30 +
		(CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m2]*CPair[i5, m5]*CPair[m1, m4])/30 -
		(CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m2]*CPair[i5, m5]*CPair[m1, m4])/10 -
		(CPair[i1, m2]*CPair[i2, i4]*CPair[i3, m3]*CPair[i5, m5]*CPair[m1, m4])/30 +
		(CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m3]*CPair[i5, m5]*CPair[m1, m4])/10 +
		(CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m2]*CPair[i5, m5]*CPair[m1, m4])/30 -
		(CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m2]*CPair[i5, m5]*CPair[m1, m4])/30 -
		(CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m3]*CPair[i5, m5]*CPair[m1, m4])/30 +
		(CPair[i1, i2]*CPair[i3, m2]*CPair[i4, m3]*CPair[i5, m5]*CPair[m1, m4])/30 +
		(CPair[i1, m5]*CPair[i2, m4]*CPair[i3, i4]*CPair[i5, m1]*CPair[m2, m3])/30 -
		(CPair[i1, m4]*CPair[i2, m5]*CPair[i3, i4]*CPair[i5, m1]*CPair[m2, m3])/30 +
		(CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m4]*CPair[i5, m1]*CPair[m2, m3])/30 -
		(CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m1]*CPair[m2, m3])/30 -
		(CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m4]*CPair[i5, m1]*CPair[m2, m3])/10 +
		(CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m4]*CPair[i5, m1]*CPair[m2, m3])/30 +
		(CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m4]*CPair[i5, m1]*CPair[m2, m3])/30 +
		(CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m1]*CPair[m2, m3])/10 -
		(CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m5]*CPair[i5, m1]*CPair[m2, m3])/30 -
		(CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m5]*CPair[i5, m1]*CPair[m2, m3])/30 -
		(CPair[i1, m5]*CPair[i2, m1]*CPair[i3, i4]*CPair[i5, m4]*CPair[m2, m3])/30 +
		(CPair[i1, m1]*CPair[i2, m5]*CPair[i3, i4]*CPair[i5, m4]*CPair[m2, m3])/30 -
		(CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m1]*CPair[i5, m4]*CPair[m2, m3])/30 +
		(CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m4]*CPair[m2, m3])/30 +
		(CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m1]*CPair[i5, m4]*CPair[m2, m3])/10 -
		(CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m1]*CPair[i5, m4]*CPair[m2, m3])/30 -
		(CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m1]*CPair[i5, m4]*CPair[m2, m3])/30 -
		(CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m4]*CPair[m2, m3])/10 +
		(CPair[i1, i3]*CPair[i2, m1]*CPair[i4, m5]*CPair[i5, m4]*CPair[m2, m3])/30 +
		(CPair[i1, i2]*CPair[i3, m1]*CPair[i4, m5]*CPair[i5, m4]*CPair[m2, m3])/30 +
		(CPair[i1, m4]*CPair[i2, m1]*CPair[i3, i4]*CPair[i5, m5]*CPair[m2, m3])/30 -
		(CPair[i1, m1]*CPair[i2, m4]*CPair[i3, i4]*CPair[i5, m5]*CPair[m2, m3])/30 +
		(CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m1]*CPair[i5, m5]*CPair[m2, m3])/30 -
		(CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m4]*CPair[i5, m5]*CPair[m2, m3])/30 -
		(CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m1]*CPair[i5, m5]*CPair[m2, m3])/10 +
		(CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m1]*CPair[i5, m5]*CPair[m2, m3])/30 +
		(CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m1]*CPair[i5, m5]*CPair[m2, m3])/30 +
		(CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m4]*CPair[i5, m5]*CPair[m2, m3])/10 -
		(CPair[i1, i3]*CPair[i2, m1]*CPair[i4, m4]*CPair[i5, m5]*CPair[m2, m3])/30 -
		(CPair[i1, i2]*CPair[i3, m1]*CPair[i4, m4]*CPair[i5, m5]*CPair[m2, m3])/30 +
		(CPair[i1, m5]*CPair[i2, m3]*CPair[i3, i4]*CPair[i5, m1]*CPair[m2, m4])/30 -
		(CPair[i1, m3]*CPair[i2, m5]*CPair[i3, i4]*CPair[i5, m1]*CPair[m2, m4])/30 -
		(CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m3]*CPair[i5, m1]*CPair[m2, m4])/10 +
		(CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m3]*CPair[i5, m1]*CPair[m2, m4])/30 +
		(CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m1]*CPair[m2, m4])/10 -
		(CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m5]*CPair[i5, m1]*CPair[m2, m4])/30 +
		(CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m3]*CPair[i5, m1]*CPair[m2, m4])/30 -
		(CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m3]*CPair[i5, m1]*CPair[m2, m4])/30 -
		(CPair[i1, m3]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m1]*CPair[m2, m4])/30 +
		(CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m5]*CPair[i5, m1]*CPair[m2, m4])/30 -
		(CPair[i1, m5]*CPair[i2, m1]*CPair[i3, i4]*CPair[i5, m3]*CPair[m2, m4])/30 +
		(CPair[i1, m1]*CPair[i2, m5]*CPair[i3, i4]*CPair[i5, m3]*CPair[m2, m4])/30 +
		(CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m1]*CPair[i5, m3]*CPair[m2, m4])/10 -
		(CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m1]*CPair[i5, m3]*CPair[m2, m4])/30 -
		(CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m3]*CPair[m2, m4])/10 +
		(CPair[i1, i4]*CPair[i2, m1]*CPair[i3, m5]*CPair[i5, m3]*CPair[m2, m4])/30 -
		(CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m1]*CPair[i5, m3]*CPair[m2, m4])/30 +
		(CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m1]*CPair[i5, m3]*CPair[m2, m4])/30 +
		(CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m3]*CPair[m2, m4])/30 -
		(CPair[i1, i2]*CPair[i3, m1]*CPair[i4, m5]*CPair[i5, m3]*CPair[m2, m4])/30 +
		(CPair[i1, m3]*CPair[i2, m1]*CPair[i3, i4]*CPair[i5, m5]*CPair[m2, m4])/30 -
		(CPair[i1, m1]*CPair[i2, m3]*CPair[i3, i4]*CPair[i5, m5]*CPair[m2, m4])/30 -
		(CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m1]*CPair[i5, m5]*CPair[m2, m4])/10 +
		(CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m1]*CPair[i5, m5]*CPair[m2, m4])/30 +
		(CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m3]*CPair[i5, m5]*CPair[m2, m4])/10 -
		(CPair[i1, i4]*CPair[i2, m1]*CPair[i3, m3]*CPair[i5, m5]*CPair[m2, m4])/30 +
		(CPair[i1, m3]*CPair[i2, i3]*CPair[i4, m1]*CPair[i5, m5]*CPair[m2, m4])/30 -
		(CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m1]*CPair[i5, m5]*CPair[m2, m4])/30 -
		(CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m3]*CPair[i5, m5]*CPair[m2, m4])/30 +
		(CPair[i1, i2]*CPair[i3, m1]*CPair[i4, m3]*CPair[i5, m5]*CPair[m2, m4])/30 -
		(CPair[i1, m5]*CPair[i2, m2]*CPair[i3, i4]*CPair[i5, m1]*CPair[m3, m4])/10 +
		(CPair[i1, m2]*CPair[i2, m5]*CPair[i3, i4]*CPair[i5, m1]*CPair[m3, m4])/10 +
		(CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m2]*CPair[i5, m1]*CPair[m3, m4])/30 -
		(CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m2]*CPair[i5, m1]*CPair[m3, m4])/30 -
		(CPair[i1, m2]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m1]*CPair[m3, m4])/30 +
		(CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m5]*CPair[i5, m1]*CPair[m3, m4])/30 +
		(CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m2]*CPair[i5, m1]*CPair[m3, m4])/30 -
		(CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m2]*CPair[i5, m1]*CPair[m3, m4])/30 -
		(CPair[i1, m2]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m1]*CPair[m3, m4])/30 +
		(CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m5]*CPair[i5, m1]*CPair[m3, m4])/30 +
		(CPair[i1, m5]*CPair[i2, m1]*CPair[i3, i4]*CPair[i5, m2]*CPair[m3, m4])/10 -
		(CPair[i1, m1]*CPair[i2, m5]*CPair[i3, i4]*CPair[i5, m2]*CPair[m3, m4])/10 -
		(CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m1]*CPair[i5, m2]*CPair[m3, m4])/30 +
		(CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m1]*CPair[i5, m2]*CPair[m3, m4])/30 +
		(CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m2]*CPair[m3, m4])/30 -
		(CPair[i1, i4]*CPair[i2, m1]*CPair[i3, m5]*CPair[i5, m2]*CPair[m3, m4])/30 -
		(CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m1]*CPair[i5, m2]*CPair[m3, m4])/30 +
		(CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m1]*CPair[i5, m2]*CPair[m3, m4])/30 +
		(CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m2]*CPair[m3, m4])/30 -
		(CPair[i1, i3]*CPair[i2, m1]*CPair[i4, m5]*CPair[i5, m2]*CPair[m3, m4])/30 -
		(CPair[i1, m2]*CPair[i2, m1]*CPair[i3, i4]*CPair[i5, m5]*CPair[m3, m4])/10 +
		(CPair[i1, m1]*CPair[i2, m2]*CPair[i3, i4]*CPair[i5, m5]*CPair[m3, m4])/10 +
		(CPair[i1, m2]*CPair[i2, i4]*CPair[i3, m1]*CPair[i5, m5]*CPair[m3, m4])/30 -
		(CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m1]*CPair[i5, m5]*CPair[m3, m4])/30 -
		(CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m2]*CPair[i5, m5]*CPair[m3, m4])/30 +
		(CPair[i1, i4]*CPair[i2, m1]*CPair[i3, m2]*CPair[i5, m5]*CPair[m3, m4])/30 +
		(CPair[i1, m2]*CPair[i2, i3]*CPair[i4, m1]*CPair[i5, m5]*CPair[m3, m4])/30 -
		(CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m1]*CPair[i5, m5]*CPair[m3, m4])/30 -
		(CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m2]*CPair[i5, m5]*CPair[m3, m4])/30 +
		(CPair[i1, i3]*CPair[i2, m1]*CPair[i4, m2]*CPair[i5, m5]*CPair[m3, m4])/30
};

tensorProjRule1 = {
	(* Rank 1*)
	projHead[CPair[i1_CIndex, m1_CMomentum ]] :> CPair[i1,m1],

	(* Rank 2*)
	projHead[CPair[i1_CIndex, m1_CMomentum ] CPair[i2_CIndex, m2_CMomentum]] :>
		-(CPair[i1, m2]*CPair[i2, m1])/2 + (CPair[i1, m1]*CPair[i2, m2])/2,

	(* Rank 3*)
	projHead[CPair[i1_CIndex, m1_CMomentum ] CPair[i2_CIndex, m2_CMomentum] CPair[i3_CIndex, m3_CMomentum]] :>
		-(CPair[i1, m3]*CPair[i2, i3]*CPair[m1, m2])/10 - (CPair[i1, i3]*CPair[i2, m3]*CPair[m1, m2])/10 +
		(2*CPair[i1, i2]*CPair[i3, m3]*CPair[m1, m2])/5 - (CPair[i1, m2]*CPair[i2, i3]*CPair[m1, m3])/10 +
		(2*CPair[i1, i3]*CPair[i2, m2]*CPair[m1, m3])/5 - (CPair[i1, i2]*CPair[i3, m2]*CPair[m1, m3])/10 +
		(2*CPair[i1, m1]*CPair[i2, i3]*CPair[m2, m3])/5 - (CPair[i1, i3]*CPair[i2, m1]*CPair[m2, m3])/10 -
		(CPair[i1, i2]*CPair[i3, m1]*CPair[m2, m3])/10,

	(* Rank 4*)
	projHead[CPair[i1_CIndex, m1_CMomentum ] CPair[i2_CIndex, m2_CMomentum] CPair[i3_CIndex, m3_CMomentum] CPair[i4_CIndex, m4_CMomentum]] :>
		-(CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m3]*CPair[m1, m2])/10 -
		(CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m3]*CPair[m1, m2])/10 +
		(CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m4]*CPair[m1, m2])/10 +
		(CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m4]*CPair[m1, m2])/10 +
		(CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m3]*CPair[m1, m2])/10 +
		(CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m3]*CPair[m1, m2])/10 -
		(3*CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m3]*CPair[m1, m2])/10 -
		(CPair[i1, m3]*CPair[i2, i3]*CPair[i4, m4]*CPair[m1, m2])/10 -
		(CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m4]*CPair[m1, m2])/10 +
		(3*CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m4]*CPair[m1, m2])/10 -
		(CPair[i1, m4]*CPair[i2, m2]*CPair[i3, i4]*CPair[m1, m3])/10 +
		(CPair[i1, m2]*CPair[i2, m4]*CPair[i3, i4]*CPair[m1, m3])/10 +
		(CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m2]*CPair[m1, m3])/10 -
		(CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m4]*CPair[m1, m3])/10 +
		(CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m2]*CPair[m1, m3])/10 -
		(3*CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m2]*CPair[m1, m3])/10 +
		(CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m2]*CPair[m1, m3])/10 -
		(CPair[i1, m2]*CPair[i2, i3]*CPair[i4, m4]*CPair[m1, m3])/10 +
		(3*CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m4]*CPair[m1, m3])/10 -
		(CPair[i1, i2]*CPair[i3, m2]*CPair[i4, m4]*CPair[m1, m3])/10 -
		(CPair[i1, m3]*CPair[i2, m2]*CPair[i3, i4]*CPair[m1, m4])/10 +
		(CPair[i1, m2]*CPair[i2, m3]*CPair[i3, i4]*CPair[m1, m4])/10 +
		(CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m2]*CPair[m1, m4])/10 -
		(3*CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m2]*CPair[m1, m4])/10 -
		(CPair[i1, m2]*CPair[i2, i4]*CPair[i3, m3]*CPair[m1, m4])/10 +
		(3*CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m3]*CPair[m1, m4])/10 +
		(CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m2]*CPair[m1, m4])/10 -
		(CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m2]*CPair[m1, m4])/10 -
		(CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m3]*CPair[m1, m4])/10 +
		(CPair[i1, i2]*CPair[i3, m2]*CPair[i4, m3]*CPair[m1, m4])/10 +
		(CPair[i1, m4]*CPair[i2, m1]*CPair[i3, i4]*CPair[m2, m3])/10 -
		(CPair[i1, m1]*CPair[i2, m4]*CPair[i3, i4]*CPair[m2, m3])/10 +
		(CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m1]*CPair[m2, m3])/10 -
		(CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m4]*CPair[m2, m3])/10 -
		(3*CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m1]*CPair[m2, m3])/10 +
		(CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m1]*CPair[m2, m3])/10 +
		(CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m1]*CPair[m2, m3])/10 +
		(3*CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m4]*CPair[m2, m3])/10 -
		(CPair[i1, i3]*CPair[i2, m1]*CPair[i4, m4]*CPair[m2, m3])/10 -
		(CPair[i1, i2]*CPair[i3, m1]*CPair[i4, m4]*CPair[m2, m3])/10 +
		(CPair[i1, m3]*CPair[i2, m1]*CPair[i3, i4]*CPair[m2, m4])/10 -
		(CPair[i1, m1]*CPair[i2, m3]*CPair[i3, i4]*CPair[m2, m4])/10 -
		(3*CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m1]*CPair[m2, m4])/10 +
		(CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m1]*CPair[m2, m4])/10 +
		(3*CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m3]*CPair[m2, m4])/10 -
		(CPair[i1, i4]*CPair[i2, m1]*CPair[i3, m3]*CPair[m2, m4])/10 +
		(CPair[i1, m3]*CPair[i2, i3]*CPair[i4, m1]*CPair[m2, m4])/10 -
		(CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m1]*CPair[m2, m4])/10 -
		(CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m3]*CPair[m2, m4])/10 +
		(CPair[i1, i2]*CPair[i3, m1]*CPair[i4, m3]*CPair[m2, m4])/10 -
		(3*CPair[i1, m2]*CPair[i2, m1]*CPair[i3, i4]*CPair[m3, m4])/10 +
		(3*CPair[i1, m1]*CPair[i2, m2]*CPair[i3, i4]*CPair[m3, m4])/10 +
		(CPair[i1, m2]*CPair[i2, i4]*CPair[i3, m1]*CPair[m3, m4])/10 -
		(CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m1]*CPair[m3, m4])/10 -
		(CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m2]*CPair[m3, m4])/10 +
		(CPair[i1, i4]*CPair[i2, m1]*CPair[i3, m2]*CPair[m3, m4])/10 +
		(CPair[i1, m2]*CPair[i2, i3]*CPair[i4, m1]*CPair[m3, m4])/10 -
		(CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m1]*CPair[m3, m4])/10 -
		(CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m2]*CPair[m3, m4])/10 +
		(CPair[i1, i3]*CPair[i2, m1]*CPair[i4, m2]*CPair[m3, m4])/10,

	(* Rank 5*)
	projHead[CPair[i1_CIndex, m1_CMomentum ] CPair[i2_CIndex, m2_CMomentum] CPair[i3_CIndex, m3_CMomentum]*
		CPair[i4_CIndex, m4_CMomentum] CPair[i5_CIndex, m5_CMomentum]] :>
		(CPair[i1, m5]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m4]*CPair[m2, m3])/35 +
		(CPair[i1, i5]*CPair[i2, m5]*CPair[i3, i4]*CPair[m1, m4]*CPair[m2, m3])/35 +
		(CPair[i1, m5]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m4]*CPair[m2, m3])/35 -
		(CPair[i1, i4]*CPair[i2, m5]*CPair[i3, i5]*CPair[m1, m4]*CPair[m2, m3])/14 +
		(CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m5]*CPair[m1, m4]*CPair[m2, m3])/35 -
		(CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m5]*CPair[m1, m4]*CPair[m2, m3])/14 -
		(CPair[i1, m5]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m4]*CPair[m2, m3])/14 +
		(CPair[i1, i3]*CPair[i2, m5]*CPair[i4, i5]*CPair[m1, m4]*CPair[m2, m3])/35 +
		(CPair[i1, i2]*CPair[i3, m5]*CPair[i4, i5]*CPair[m1, m4]*CPair[m2, m3])/35 -
		(CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m5]*CPair[m1, m4]*CPair[m2, m3])/14 +
		(CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m5]*CPair[m1, m4]*CPair[m2, m3])/35 +
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m5]*CPair[m1, m4]*CPair[m2, m3])/35 +
		(8*CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m5]*CPair[m1, m4]*CPair[m2, m3])/35 -
		(CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m5]*CPair[m1, m4]*CPair[m2, m3])/14 -
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m5]*CPair[m1, m4]*CPair[m2, m3])/14 +
		(CPair[i1, m4]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m5]*CPair[m2, m3])/35 -
		(CPair[i1, i5]*CPair[i2, m4]*CPair[i3, i4]*CPair[m1, m5]*CPair[m2, m3])/14 +
		(CPair[i1, m4]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m5]*CPair[m2, m3])/35 +
		(CPair[i1, i4]*CPair[i2, m4]*CPair[i3, i5]*CPair[m1, m5]*CPair[m2, m3])/35 -
		(CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m4]*CPair[m1, m5]*CPair[m2, m3])/14 +
		(CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m4]*CPair[m1, m5]*CPair[m2, m3])/35 -
		(CPair[i1, m4]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m5]*CPair[m2, m3])/14 +
		(CPair[i1, i3]*CPair[i2, m4]*CPair[i4, i5]*CPair[m1, m5]*CPair[m2, m3])/35 +
		(CPair[i1, i2]*CPair[i3, m4]*CPair[i4, i5]*CPair[m1, m5]*CPair[m2, m3])/35 +
		(8*CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m4]*CPair[m1, m5]*CPair[m2, m3])/35 -
		(CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m4]*CPair[m1, m5]*CPair[m2, m3])/14 -
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m4]*CPair[m1, m5]*CPair[m2, m3])/14 -
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m4]*CPair[m1, m5]*CPair[m2, m3])/14 +
		(CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m4]*CPair[m1, m5]*CPair[m2, m3])/35 +
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m4]*CPair[m1, m5]*CPair[m2, m3])/35 +
		(CPair[i1, m5]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m3]*CPair[m2, m4])/35 +
		(CPair[i1, i5]*CPair[i2, m5]*CPair[i3, i4]*CPair[m1, m3]*CPair[m2, m4])/35 -
		(CPair[i1, m5]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m3]*CPair[m2, m4])/14 +
		(CPair[i1, i4]*CPair[i2, m5]*CPair[i3, i5]*CPair[m1, m3]*CPair[m2, m4])/35 -
		(CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m5]*CPair[m1, m3]*CPair[m2, m4])/14 +
		(CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m5]*CPair[m1, m3]*CPair[m2, m4])/35 +
		(CPair[i1, m5]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m3]*CPair[m2, m4])/35 -
		(CPair[i1, i3]*CPair[i2, m5]*CPair[i4, i5]*CPair[m1, m3]*CPair[m2, m4])/14 +
		(CPair[i1, i2]*CPair[i3, m5]*CPair[i4, i5]*CPair[m1, m3]*CPair[m2, m4])/35 +
		(CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m5]*CPair[m1, m3]*CPair[m2, m4])/35 -
		(CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m5]*CPair[m1, m3]*CPair[m2, m4])/14 +
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m5]*CPair[m1, m3]*CPair[m2, m4])/35 -
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m5]*CPair[m1, m3]*CPair[m2, m4])/14 +
		(8*CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m5]*CPair[m1, m3]*CPair[m2, m4])/35 -
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m5]*CPair[m1, m3]*CPair[m2, m4])/14 +
		(CPair[i1, m3]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m5]*CPair[m2, m4])/35 -
		(CPair[i1, i5]*CPair[i2, m3]*CPair[i3, i4]*CPair[m1, m5]*CPair[m2, m4])/14 -
		(CPair[i1, m3]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m5]*CPair[m2, m4])/14 +
		(CPair[i1, i4]*CPair[i2, m3]*CPair[i3, i5]*CPair[m1, m5]*CPair[m2, m4])/35 +
		(8*CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m3]*CPair[m1, m5]*CPair[m2, m4])/35 -
		(CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m3]*CPair[m1, m5]*CPair[m2, m4])/14 +
		(CPair[i1, m3]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m5]*CPair[m2, m4])/35 +
		(CPair[i1, i3]*CPair[i2, m3]*CPair[i4, i5]*CPair[m1, m5]*CPair[m2, m4])/35 -
		(CPair[i1, i2]*CPair[i3, m3]*CPair[i4, i5]*CPair[m1, m5]*CPair[m2, m4])/14 -
		(CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m3]*CPair[m1, m5]*CPair[m2, m4])/14 +
		(CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m3]*CPair[m1, m5]*CPair[m2, m4])/35 +
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m3]*CPair[m1, m5]*CPair[m2, m4])/35 +
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m3]*CPair[m1, m5]*CPair[m2, m4])/35 -
		(CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m3]*CPair[m1, m5]*CPair[m2, m4])/14 +
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m3]*CPair[m1, m5]*CPair[m2, m4])/35 -
		(CPair[i1, m4]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m3]*CPair[m2, m5])/14 +
		(CPair[i1, i5]*CPair[i2, m4]*CPair[i3, i4]*CPair[m1, m3]*CPair[m2, m5])/35 +
		(CPair[i1, m4]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m3]*CPair[m2, m5])/35 +
		(CPair[i1, i4]*CPair[i2, m4]*CPair[i3, i5]*CPair[m1, m3]*CPair[m2, m5])/35 +
		(CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m4]*CPair[m1, m3]*CPair[m2, m5])/35 -
		(CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m4]*CPair[m1, m3]*CPair[m2, m5])/14 +
		(CPair[i1, m4]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m3]*CPair[m2, m5])/35 -
		(CPair[i1, i3]*CPair[i2, m4]*CPair[i4, i5]*CPair[m1, m3]*CPair[m2, m5])/14 +
		(CPair[i1, i2]*CPair[i3, m4]*CPair[i4, i5]*CPair[m1, m3]*CPair[m2, m5])/35 -
		(CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m4]*CPair[m1, m3]*CPair[m2, m5])/14 +
		(8*CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m4]*CPair[m1, m3]*CPair[m2, m5])/35 -
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m4]*CPair[m1, m3]*CPair[m2, m5])/14 +
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m4]*CPair[m1, m3]*CPair[m2, m5])/35 -
		(CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m4]*CPair[m1, m3]*CPair[m2, m5])/14 +
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m4]*CPair[m1, m3]*CPair[m2, m5])/35 -
		(CPair[i1, m3]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m4]*CPair[m2, m5])/14 +
		(CPair[i1, i5]*CPair[i2, m3]*CPair[i3, i4]*CPair[m1, m4]*CPair[m2, m5])/35 +
		(CPair[i1, m3]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m4]*CPair[m2, m5])/35 -
		(CPair[i1, i4]*CPair[i2, m3]*CPair[i3, i5]*CPair[m1, m4]*CPair[m2, m5])/14 -
		(CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m3]*CPair[m1, m4]*CPair[m2, m5])/14 +
		(8*CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m3]*CPair[m1, m4]*CPair[m2, m5])/35 +
		(CPair[i1, m3]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m4]*CPair[m2, m5])/35 +
		(CPair[i1, i3]*CPair[i2, m3]*CPair[i4, i5]*CPair[m1, m4]*CPair[m2, m5])/35 -
		(CPair[i1, i2]*CPair[i3, m3]*CPair[i4, i5]*CPair[m1, m4]*CPair[m2, m5])/14 +
		(CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m3]*CPair[m1, m4]*CPair[m2, m5])/35 -
		(CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m3]*CPair[m1, m4]*CPair[m2, m5])/14 +
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m3]*CPair[m1, m4]*CPair[m2, m5])/35 -
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m3]*CPair[m1, m4]*CPair[m2, m5])/14 +
		(CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m3]*CPair[m1, m4]*CPair[m2, m5])/35 +
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m3]*CPair[m1, m4]*CPair[m2, m5])/35 -
		(CPair[i1, m5]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m2]*CPair[m3, m4])/14 -
		(CPair[i1, i5]*CPair[i2, m5]*CPair[i3, i4]*CPair[m1, m2]*CPair[m3, m4])/14 +
		(CPair[i1, m5]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m2]*CPair[m3, m4])/35 +
		(CPair[i1, i4]*CPair[i2, m5]*CPair[i3, i5]*CPair[m1, m2]*CPair[m3, m4])/35 +
		(CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m5]*CPair[m1, m2]*CPair[m3, m4])/35 +
		(CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m5]*CPair[m1, m2]*CPair[m3, m4])/35 +
		(CPair[i1, m5]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m2]*CPair[m3, m4])/35 +
		(CPair[i1, i3]*CPair[i2, m5]*CPair[i4, i5]*CPair[m1, m2]*CPair[m3, m4])/35 -
		(CPair[i1, i2]*CPair[i3, m5]*CPair[i4, i5]*CPair[m1, m2]*CPair[m3, m4])/14 +
		(CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m5]*CPair[m1, m2]*CPair[m3, m4])/35 +
		(CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m5]*CPair[m1, m2]*CPair[m3, m4])/35 -
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m5]*CPair[m1, m2]*CPair[m3, m4])/14 -
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m5]*CPair[m1, m2]*CPair[m3, m4])/14 -
		(CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m5]*CPair[m1, m2]*CPair[m3, m4])/14 +
		(8*CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m5]*CPair[m1, m2]*CPair[m3, m4])/35 -
		(CPair[i1, m2]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m5]*CPair[m3, m4])/14 +
		(8*CPair[i1, i5]*CPair[i2, m2]*CPair[i3, i4]*CPair[m1, m5]*CPair[m3, m4])/35 +
		(CPair[i1, m2]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m5]*CPair[m3, m4])/35 -
		(CPair[i1, i4]*CPair[i2, m2]*CPair[i3, i5]*CPair[m1, m5]*CPair[m3, m4])/14 -
		(CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m2]*CPair[m1, m5]*CPair[m3, m4])/14 +
		(CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m2]*CPair[m1, m5]*CPair[m3, m4])/35 +
		(CPair[i1, m2]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m5]*CPair[m3, m4])/35 -
		(CPair[i1, i3]*CPair[i2, m2]*CPair[i4, i5]*CPair[m1, m5]*CPair[m3, m4])/14 +
		(CPair[i1, i2]*CPair[i3, m2]*CPair[i4, i5]*CPair[m1, m5]*CPair[m3, m4])/35 -
		(CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m2]*CPair[m1, m5]*CPair[m3, m4])/14 +
		(CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m2]*CPair[m1, m5]*CPair[m3, m4])/35 +
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m2]*CPair[m1, m5]*CPair[m3, m4])/35 +
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m2]*CPair[m1, m5]*CPair[m3, m4])/35 +
		(CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m2]*CPair[m1, m5]*CPair[m3, m4])/35 -
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m2]*CPair[m1, m5]*CPair[m3, m4])/14 +
		(8*CPair[i1, m1]*CPair[i2, i5]*CPair[i3, i4]*CPair[m2, m5]*CPair[m3, m4])/35 -
		(CPair[i1, i5]*CPair[i2, m1]*CPair[i3, i4]*CPair[m2, m5]*CPair[m3, m4])/14 -
		(CPair[i1, m1]*CPair[i2, i4]*CPair[i3, i5]*CPair[m2, m5]*CPair[m3, m4])/14 +
		(CPair[i1, i4]*CPair[i2, m1]*CPair[i3, i5]*CPair[m2, m5]*CPair[m3, m4])/35 +
		(CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m1]*CPair[m2, m5]*CPair[m3, m4])/35 -
		(CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m1]*CPair[m2, m5]*CPair[m3, m4])/14 -
		(CPair[i1, m1]*CPair[i2, i3]*CPair[i4, i5]*CPair[m2, m5]*CPair[m3, m4])/14 +
		(CPair[i1, i3]*CPair[i2, m1]*CPair[i4, i5]*CPair[m2, m5]*CPair[m3, m4])/35 +
		(CPair[i1, i2]*CPair[i3, m1]*CPair[i4, i5]*CPair[m2, m5]*CPair[m3, m4])/35 +
		(CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m1]*CPair[m2, m5]*CPair[m3, m4])/35 -
		(CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m1]*CPair[m2, m5]*CPair[m3, m4])/14 +
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m1]*CPair[m2, m5]*CPair[m3, m4])/35 +
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m1]*CPair[m2, m5]*CPair[m3, m4])/35 +
		(CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m1]*CPair[m2, m5]*CPair[m3, m4])/35 -
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m1]*CPair[m2, m5]*CPair[m3, m4])/14 +
		(CPair[i1, m4]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m2]*CPair[m3, m5])/35 +
		(CPair[i1, i5]*CPair[i2, m4]*CPair[i3, i4]*CPair[m1, m2]*CPair[m3, m5])/35 -
		(CPair[i1, m4]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m2]*CPair[m3, m5])/14 -
		(CPair[i1, i4]*CPair[i2, m4]*CPair[i3, i5]*CPair[m1, m2]*CPair[m3, m5])/14 +
		(CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m4]*CPair[m1, m2]*CPair[m3, m5])/35 +
		(CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m4]*CPair[m1, m2]*CPair[m3, m5])/35 +
		(CPair[i1, m4]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m2]*CPair[m3, m5])/35 +
		(CPair[i1, i3]*CPair[i2, m4]*CPair[i4, i5]*CPair[m1, m2]*CPair[m3, m5])/35 -
		(CPair[i1, i2]*CPair[i3, m4]*CPair[i4, i5]*CPair[m1, m2]*CPair[m3, m5])/14 -
		(CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m4]*CPair[m1, m2]*CPair[m3, m5])/14 -
		(CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m4]*CPair[m1, m2]*CPair[m3, m5])/14 +
		(8*CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m4]*CPair[m1, m2]*CPair[m3, m5])/35 +
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m4]*CPair[m1, m2]*CPair[m3, m5])/35 +
		(CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m4]*CPair[m1, m2]*CPair[m3, m5])/35 -
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m4]*CPair[m1, m2]*CPair[m3, m5])/14 +
		(CPair[i1, m2]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m4]*CPair[m3, m5])/35 -
		(CPair[i1, i5]*CPair[i2, m2]*CPair[i3, i4]*CPair[m1, m4]*CPair[m3, m5])/14 -
		(CPair[i1, m2]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m4]*CPair[m3, m5])/14 +
		(8*CPair[i1, i4]*CPair[i2, m2]*CPair[i3, i5]*CPair[m1, m4]*CPair[m3, m5])/35 +
		(CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m2]*CPair[m1, m4]*CPair[m3, m5])/35 -
		(CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m2]*CPair[m1, m4]*CPair[m3, m5])/14 +
		(CPair[i1, m2]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m4]*CPair[m3, m5])/35 -
		(CPair[i1, i3]*CPair[i2, m2]*CPair[i4, i5]*CPair[m1, m4]*CPair[m3, m5])/14 +
		(CPair[i1, i2]*CPair[i3, m2]*CPair[i4, i5]*CPair[m1, m4]*CPair[m3, m5])/35 +
		(CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m2]*CPair[m1, m4]*CPair[m3, m5])/35 +
		(CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m2]*CPair[m1, m4]*CPair[m3, m5])/35 -
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m2]*CPair[m1, m4]*CPair[m3, m5])/14 -
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m2]*CPair[m1, m4]*CPair[m3, m5])/14 +
		(CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m2]*CPair[m1, m4]*CPair[m3, m5])/35 +
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m2]*CPair[m1, m4]*CPair[m3, m5])/35 -
		(CPair[i1, m1]*CPair[i2, i5]*CPair[i3, i4]*CPair[m2, m4]*CPair[m3, m5])/14 +
		(CPair[i1, i5]*CPair[i2, m1]*CPair[i3, i4]*CPair[m2, m4]*CPair[m3, m5])/35 +
		(8*CPair[i1, m1]*CPair[i2, i4]*CPair[i3, i5]*CPair[m2, m4]*CPair[m3, m5])/35 -
		(CPair[i1, i4]*CPair[i2, m1]*CPair[i3, i5]*CPair[m2, m4]*CPair[m3, m5])/14 -
		(CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m1]*CPair[m2, m4]*CPair[m3, m5])/14 +
		(CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m1]*CPair[m2, m4]*CPair[m3, m5])/35 -
		(CPair[i1, m1]*CPair[i2, i3]*CPair[i4, i5]*CPair[m2, m4]*CPair[m3, m5])/14 +
		(CPair[i1, i3]*CPair[i2, m1]*CPair[i4, i5]*CPair[m2, m4]*CPair[m3, m5])/35 +
		(CPair[i1, i2]*CPair[i3, m1]*CPair[i4, i5]*CPair[m2, m4]*CPair[m3, m5])/35 +
		(CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m1]*CPair[m2, m4]*CPair[m3, m5])/35 +
		(CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m1]*CPair[m2, m4]*CPair[m3, m5])/35 -
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m1]*CPair[m2, m4]*CPair[m3, m5])/14 +
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m1]*CPair[m2, m4]*CPair[m3, m5])/35 -
		(CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m1]*CPair[m2, m4]*CPair[m3, m5])/14 +
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m1]*CPair[m2, m4]*CPair[m3, m5])/35 +
		(CPair[i1, m3]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m2]*CPair[m4, m5])/35 +
		(CPair[i1, i5]*CPair[i2, m3]*CPair[i3, i4]*CPair[m1, m2]*CPair[m4, m5])/35 +
		(CPair[i1, m3]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m2]*CPair[m4, m5])/35 +
		(CPair[i1, i4]*CPair[i2, m3]*CPair[i3, i5]*CPair[m1, m2]*CPair[m4, m5])/35 -
		(CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m3]*CPair[m1, m2]*CPair[m4, m5])/14 -
		(CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m3]*CPair[m1, m2]*CPair[m4, m5])/14 -
		(CPair[i1, m3]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m2]*CPair[m4, m5])/14 -
		(CPair[i1, i3]*CPair[i2, m3]*CPair[i4, i5]*CPair[m1, m2]*CPair[m4, m5])/14 +
		(8*CPair[i1, i2]*CPair[i3, m3]*CPair[i4, i5]*CPair[m1, m2]*CPair[m4, m5])/35 +
		(CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m3]*CPair[m1, m2]*CPair[m4, m5])/35 +
		(CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m3]*CPair[m1, m2]*CPair[m4, m5])/35 -
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m3]*CPair[m1, m2]*CPair[m4, m5])/14 +
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m3]*CPair[m1, m2]*CPair[m4, m5])/35 +
		(CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m3]*CPair[m1, m2]*CPair[m4, m5])/35 -
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m3]*CPair[m1, m2]*CPair[m4, m5])/14 +
		(CPair[i1, m2]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m3]*CPair[m4, m5])/35 -
		(CPair[i1, i5]*CPair[i2, m2]*CPair[i3, i4]*CPair[m1, m3]*CPair[m4, m5])/14 +
		(CPair[i1, m2]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m3]*CPair[m4, m5])/35 -
		(CPair[i1, i4]*CPair[i2, m2]*CPair[i3, i5]*CPair[m1, m3]*CPair[m4, m5])/14 +
		(CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m2]*CPair[m1, m3]*CPair[m4, m5])/35 +
		(CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m2]*CPair[m1, m3]*CPair[m4, m5])/35 -
		(CPair[i1, m2]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m3]*CPair[m4, m5])/14 +
		(8*CPair[i1, i3]*CPair[i2, m2]*CPair[i4, i5]*CPair[m1, m3]*CPair[m4, m5])/35 -
		(CPair[i1, i2]*CPair[i3, m2]*CPair[i4, i5]*CPair[m1, m3]*CPair[m4, m5])/14 +
		(CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m2]*CPair[m1, m3]*CPair[m4, m5])/35 -
		(CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m2]*CPair[m1, m3]*CPair[m4, m5])/14 +
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m2]*CPair[m1, m3]*CPair[m4, m5])/35 +
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m2]*CPair[m1, m3]*CPair[m4, m5])/35 -
		(CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m2]*CPair[m1, m3]*CPair[m4, m5])/14 +
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m2]*CPair[m1, m3]*CPair[m4, m5])/35 -
		(CPair[i1, m1]*CPair[i2, i5]*CPair[i3, i4]*CPair[m2, m3]*CPair[m4, m5])/14 +
		(CPair[i1, i5]*CPair[i2, m1]*CPair[i3, i4]*CPair[m2, m3]*CPair[m4, m5])/35 -
		(CPair[i1, m1]*CPair[i2, i4]*CPair[i3, i5]*CPair[m2, m3]*CPair[m4, m5])/14 +
		(CPair[i1, i4]*CPair[i2, m1]*CPair[i3, i5]*CPair[m2, m3]*CPair[m4, m5])/35 +
		(CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m1]*CPair[m2, m3]*CPair[m4, m5])/35 +
		(CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m1]*CPair[m2, m3]*CPair[m4, m5])/35 +
		(8*CPair[i1, m1]*CPair[i2, i3]*CPair[i4, i5]*CPair[m2, m3]*CPair[m4, m5])/35 -
		(CPair[i1, i3]*CPair[i2, m1]*CPair[i4, i5]*CPair[m2, m3]*CPair[m4, m5])/14 -
		(CPair[i1, i2]*CPair[i3, m1]*CPair[i4, i5]*CPair[m2, m3]*CPair[m4, m5])/14 -
		(CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m1]*CPair[m2, m3]*CPair[m4, m5])/14 +
		(CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m1]*CPair[m2, m3]*CPair[m4, m5])/35 +
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m1]*CPair[m2, m3]*CPair[m4, m5])/35 -
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m1]*CPair[m2, m3]*CPair[m4, m5])/14 +
		(CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m1]*CPair[m2, m3]*CPair[m4, m5])/35 +
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m1]*CPair[m2, m3]*CPair[m4, m5])/35
};

tensorProjRule2 = {
	(* Rank 1*)
	projHead[CPair[_CIndex, _CMomentum ]] :>0,

	(* Rank 2*)
	projHead[CPair[i1_CIndex, m1_CMomentum ] CPair[i2_CIndex, m2_CMomentum]] :>
		(CPair[i1, m2]*CPair[i2, m1])/2 + (CPair[i1, m1]*CPair[i2, m2])/2 - (CPair[i1, i2]*CPair[m1, m2])/3,

	(* Rank 3*)
	projHead[CPair[i1_CIndex, m1_CMomentum ] CPair[i2_CIndex, m2_CMomentum] CPair[i3_CIndex, m3_CMomentum]] :>
		-(CPair[i1, m2]*CPair[i2, m3]*CPair[i3, m1])/3 - (CPair[i1, m3]*CPair[i2, m1]*CPair[i3, m2])/3 +
		(2*CPair[i1, m1]*CPair[i2, m2]*CPair[i3, m3])/3 + (CPair[i1, m3]*CPair[i2, i3]*CPair[m1, m2])/6 +
		(CPair[i1, i3]*CPair[i2, m3]*CPair[m1, m2])/6 - (CPair[i1, i2]*CPair[i3, m3]*CPair[m1, m2])/3 +
		(CPair[i1, m2]*CPair[i2, i3]*CPair[m1, m3])/6 - (CPair[i1, i3]*CPair[i2, m2]*CPair[m1, m3])/3 +
		(CPair[i1, i2]*CPair[i3, m2]*CPair[m1, m3])/6 - (CPair[i1, m1]*CPair[i2, i3]*CPair[m2, m3])/3 +
		(CPair[i1, i3]*CPair[i2, m1]*CPair[m2, m3])/6 + (CPair[i1, i2]*CPair[i3, m1]*CPair[m2, m3])/6,

	(* Rank 4*)
	projHead[CPair[i1_CIndex, m1_CMomentum ] CPair[i2_CIndex, m2_CMomentum] CPair[i3_CIndex, m3_CMomentum] CPair[i4_CIndex, m4_CMomentum]] :>
		(2*CPair[i1, m4]*CPair[i2, m3]*CPair[i3, i4]*CPair[m1, m2])/21 +
		(2*CPair[i1, m3]*CPair[i2, m4]*CPair[i3, i4]*CPair[m1, m2])/21 -
		(CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m3]*CPair[m1, m2])/14 -
		(CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m3]*CPair[m1, m2])/14 -
		(CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m4]*CPair[m1, m2])/14 -
		(CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m4]*CPair[m1, m2])/14 -
		(CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m3]*CPair[m1, m2])/14 -
		(CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m3]*CPair[m1, m2])/14 +
		(11*CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m3]*CPair[m1, m2])/42 -
		(CPair[i1, m3]*CPair[i2, i3]*CPair[i4, m4]*CPair[m1, m2])/14 -
		(CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m4]*CPair[m1, m2])/14 +
		(11*CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m4]*CPair[m1, m2])/42 -
		(CPair[i1, m4]*CPair[i2, m2]*CPair[i3, i4]*CPair[m1, m3])/14 -
		(CPair[i1, m2]*CPair[i2, m4]*CPair[i3, i4]*CPair[m1, m3])/14 +
		(2*CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m2]*CPair[m1, m3])/21 -
		(CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m2]*CPair[m1, m3])/14 +
		(2*CPair[i1, m2]*CPair[i2, i4]*CPair[i3, m4]*CPair[m1, m3])/21 -
		(CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m4]*CPair[m1, m3])/14 -
		(CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m2]*CPair[m1, m3])/14 +
		(11*CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m2]*CPair[m1, m3])/42 -
		(CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m2]*CPair[m1, m3])/14 -
		(CPair[i1, m2]*CPair[i2, i3]*CPair[i4, m4]*CPair[m1, m3])/14 +
		(11*CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m4]*CPair[m1, m3])/42 -
		(CPair[i1, i2]*CPair[i3, m2]*CPair[i4, m4]*CPair[m1, m3])/14 -
		(CPair[i1, m3]*CPair[i2, m2]*CPair[i3, i4]*CPair[m1, m4])/14 -
		(CPair[i1, m2]*CPair[i2, m3]*CPair[i3, i4]*CPair[m1, m4])/14 -
		(CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m2]*CPair[m1, m4])/14 +
		(11*CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m2]*CPair[m1, m4])/42 -
		(CPair[i1, m2]*CPair[i2, i4]*CPair[i3, m3]*CPair[m1, m4])/14 +
		(11*CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m3]*CPair[m1, m4])/42 +
		(2*CPair[i1, m3]*CPair[i2, i3]*CPair[i4, m2]*CPair[m1, m4])/21 -
		(CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m2]*CPair[m1, m4])/14 -
		(CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m2]*CPair[m1, m4])/14 +
		(2*CPair[i1, m2]*CPair[i2, i3]*CPair[i4, m3]*CPair[m1, m4])/21 -
		(CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m3]*CPair[m1, m4])/14 -
		(CPair[i1, i2]*CPair[i3, m2]*CPair[i4, m3]*CPair[m1, m4])/14 -
		(CPair[i1, m4]*CPair[i2, m1]*CPair[i3, i4]*CPair[m2, m3])/14 -
		(CPair[i1, m1]*CPair[i2, m4]*CPair[i3, i4]*CPair[m2, m3])/14 -
		(CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m1]*CPair[m2, m3])/14 +
		(2*CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m1]*CPair[m2, m3])/21 -
		(CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m4]*CPair[m2, m3])/14 +
		(2*CPair[i1, i4]*CPair[i2, m1]*CPair[i3, m4]*CPair[m2, m3])/21 +
		(11*CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m1]*CPair[m2, m3])/42 -
		(CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m1]*CPair[m2, m3])/14 -
		(CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m1]*CPair[m2, m3])/14 +
		(11*CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m4]*CPair[m2, m3])/42 -
		(CPair[i1, i3]*CPair[i2, m1]*CPair[i4, m4]*CPair[m2, m3])/14 -
		(CPair[i1, i2]*CPair[i3, m1]*CPair[i4, m4]*CPair[m2, m3])/14 -
		(10*CPair[i1, i4]*CPair[i2, i3]*CPair[m1, m4]*CPair[m2, m3])/21 +
		(4*CPair[i1, i3]*CPair[i2, i4]*CPair[m1, m4]*CPair[m2, m3])/21 +
		(4*CPair[i1, i2]*CPair[i3, i4]*CPair[m1, m4]*CPair[m2, m3])/21 -
		(CPair[i1, m3]*CPair[i2, m1]*CPair[i3, i4]*CPair[m2, m4])/14 -
		(CPair[i1, m1]*CPair[i2, m3]*CPair[i3, i4]*CPair[m2, m4])/14 +
		(11*CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m1]*CPair[m2, m4])/42 -
		(CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m1]*CPair[m2, m4])/14 +
		(11*CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m3]*CPair[m2, m4])/42 -
		(CPair[i1, i4]*CPair[i2, m1]*CPair[i3, m3]*CPair[m2, m4])/14 -
		(CPair[i1, m3]*CPair[i2, i3]*CPair[i4, m1]*CPair[m2, m4])/14 +
		(2*CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m1]*CPair[m2, m4])/21 -
		(CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m1]*CPair[m2, m4])/14 -
		(CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m3]*CPair[m2, m4])/14 +
		(2*CPair[i1, i3]*CPair[i2, m1]*CPair[i4, m3]*CPair[m2, m4])/21 -
		(CPair[i1, i2]*CPair[i3, m1]*CPair[i4, m3]*CPair[m2, m4])/14 +
		(4*CPair[i1, i4]*CPair[i2, i3]*CPair[m1, m3]*CPair[m2, m4])/21 -
		(10*CPair[i1, i3]*CPair[i2, i4]*CPair[m1, m3]*CPair[m2, m4])/21 +
		(4*CPair[i1, i2]*CPair[i3, i4]*CPair[m1, m3]*CPair[m2, m4])/21 +
		(11*CPair[i1, m2]*CPair[i2, m1]*CPair[i3, i4]*CPair[m3, m4])/42 +
		(11*CPair[i1, m1]*CPair[i2, m2]*CPair[i3, i4]*CPair[m3, m4])/42 -
		(CPair[i1, m2]*CPair[i2, i4]*CPair[i3, m1]*CPair[m3, m4])/14 -
		(CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m1]*CPair[m3, m4])/14 -
		(CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m2]*CPair[m3, m4])/14 -
		(CPair[i1, i4]*CPair[i2, m1]*CPair[i3, m2]*CPair[m3, m4])/14 -
		(CPair[i1, m2]*CPair[i2, i3]*CPair[i4, m1]*CPair[m3, m4])/14 -
		(CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m1]*CPair[m3, m4])/14 +
		(2*CPair[i1, i2]*CPair[i3, m2]*CPair[i4, m1]*CPair[m3, m4])/21 -
		(CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m2]*CPair[m3, m4])/14 -
		(CPair[i1, i3]*CPair[i2, m1]*CPair[i4, m2]*CPair[m3, m4])/14 +
		(2*CPair[i1, i2]*CPair[i3, m1]*CPair[i4, m2]*CPair[m3, m4])/21 +
		(4*CPair[i1, i4]*CPair[i2, i3]*CPair[m1, m2]*CPair[m3, m4])/21 +
		(4*CPair[i1, i3]*CPair[i2, i4]*CPair[m1, m2]*CPair[m3, m4])/21 -
		(10*CPair[i1, i2]*CPair[i3, i4]*CPair[m1, m2]*CPair[m3, m4])/21,

	(* Rank 5*)
	projHead[CPair[i1_CIndex, m1_CMomentum ] CPair[i2_CIndex, m2_CMomentum] CPair[i3_CIndex, m3_CMomentum]*
		CPair[i4_CIndex, m4_CMomentum] CPair[i5_CIndex, m5_CMomentum]] :>
		(CPair[i1, m5]*CPair[i2, m4]*CPair[i3, m3]*CPair[i4, i5]*CPair[m1, m2])/7 +
		(CPair[i1, m4]*CPair[i2, m5]*CPair[i3, m3]*CPair[i4, i5]*CPair[m1, m2])/7 -
		(CPair[i1, m5]*CPair[i2, m3]*CPair[i3, m4]*CPair[i4, i5]*CPair[m1, m2])/7 -
		(CPair[i1, m4]*CPair[i2, m3]*CPair[i3, m5]*CPair[i4, i5]*CPair[m1, m2])/7 +
		(CPair[i1, m5]*CPair[i2, i5]*CPair[i3, m4]*CPair[i4, m3]*CPair[m1, m2])/18 -
		(5*CPair[i1, i5]*CPair[i2, m5]*CPair[i3, m4]*CPair[i4, m3]*CPair[m1, m2])/63 +
		(11*CPair[i1, m4]*CPair[i2, i5]*CPair[i3, m5]*CPair[i4, m3]*CPair[m1, m2])/126 +
		(5*CPair[i1, i5]*CPair[i2, m4]*CPair[i3, m5]*CPair[i4, m3]*CPair[m1, m2])/63 +
		(CPair[i1, m5]*CPair[i2, m3]*CPair[i3, i5]*CPair[i4, m4]*CPair[m1, m2])/14 -
		(CPair[i1, m3]*CPair[i2, m5]*CPair[i3, i5]*CPair[i4, m4]*CPair[m1, m2])/14 -
		(31*CPair[i1, m5]*CPair[i2, i5]*CPair[i3, m3]*CPair[i4, m4]*CPair[m1, m2])/126 -
		(CPair[i1, i5]*CPair[i2, m5]*CPair[i3, m3]*CPair[i4, m4]*CPair[m1, m2])/9 -
		(CPair[i1, m3]*CPair[i2, i5]*CPair[i3, m5]*CPair[i4, m4]*CPair[m1, m2])/63 +
		(CPair[i1, i5]*CPair[i2, m3]*CPair[i3, m5]*CPair[i4, m4]*CPair[m1, m2])/9 +
		(CPair[i1, m4]*CPair[i2, m3]*CPair[i3, i5]*CPair[i4, m5]*CPair[m1, m2])/14 -
		(CPair[i1, m3]*CPair[i2, m4]*CPair[i3, i5]*CPair[i4, m5]*CPair[m1, m2])/14 -
		(5*CPair[i1, m4]*CPair[i2, i5]*CPair[i3, m3]*CPair[i4, m5]*CPair[m1, m2])/126 -
		(2*CPair[i1, i5]*CPair[i2, m4]*CPair[i3, m3]*CPair[i4, m5]*CPair[m1, m2])/63 +
		(10*CPair[i1, m3]*CPair[i2, i5]*CPair[i3, m4]*CPair[i4, m5]*CPair[m1, m2])/63 +
		(2*CPair[i1, i5]*CPair[i2, m3]*CPair[i3, m4]*CPair[i4, m5]*CPair[m1, m2])/63 +
		(11*CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m4]*CPair[i5, m3]*CPair[m1, m2])/126 +
		(5*CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m4]*CPair[i5, m3]*CPair[m1, m2])/63 +
		(CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m3]*CPair[m1, m2])/18 -
		(5*CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m5]*CPair[i5, m3]*CPair[m1, m2])/63 +
		(2*CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m4]*CPair[i5, m3]*CPair[m1, m2])/63 +
		(5*CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m4]*CPair[i5, m3]*CPair[m1, m2])/126 -
		(CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m4]*CPair[i5, m3]*CPair[m1, m2])/21 +
		(CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m3]*CPair[m1, m2])/63 +
		(19*CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m5]*CPair[i5, m3]*CPair[m1, m2])/126 -
		(2*CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m5]*CPair[i5, m3]*CPair[m1, m2])/7 +
		(2*CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m3]*CPair[i5, m4]*CPair[m1, m2])/63 -
		(13*CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m3]*CPair[i5, m4]*CPair[m1, m2])/126 +
		(11*CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m4]*CPair[m1, m2])/126 +
		(13*CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m5]*CPair[i5, m4]*CPair[m1, m2])/126 +
		(CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m3]*CPair[i5, m4]*CPair[m1, m2])/63 +
		(19*CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m3]*CPair[i5, m4]*CPair[m1, m2])/126 -
		(2*CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m3]*CPair[i5, m4]*CPair[m1, m2])/7 -
		(4*CPair[i1, m3]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m4]*CPair[m1, m2])/63 -
		(5*CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m5]*CPair[i5, m4]*CPair[m1, m2])/63 +
		(2*CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m5]*CPair[i5, m4]*CPair[m1, m2])/21 -
		(11*CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m3]*CPair[i5, m5]*CPair[m1, m2])/63 -
		(23*CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m3]*CPair[i5, m5]*CPair[m1, m2])/126 -
		(11*CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m4]*CPair[i5, m5]*CPair[m1, m2])/126 +
		(23*CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m4]*CPair[i5, m5]*CPair[m1, m2])/126 +
		(2*CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m3]*CPair[i5, m5]*CPair[m1, m2])/63 +
		(5*CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m3]*CPair[i5, m5]*CPair[m1, m2])/126 -
		(CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m3]*CPair[i5, m5]*CPair[m1, m2])/21 -
		(2*CPair[i1, m3]*CPair[i2, i3]*CPair[i4, m4]*CPair[i5, m5]*CPair[m1, m2])/63 -
		(19*CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m4]*CPair[i5, m5]*CPair[m1, m2])/63 +
		(4*CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m4]*CPair[i5, m5]*CPair[m1, m2])/7 -
		(5*CPair[i1, m5]*CPair[i2, m4]*CPair[i3, m2]*CPair[i4, i5]*CPair[m1, m3])/42 -
		(5*CPair[i1, m4]*CPair[i2, m5]*CPair[i3, m2]*CPair[i4, i5]*CPair[m1, m3])/42 +
		(5*CPair[i1, m5]*CPair[i2, m2]*CPair[i3, m4]*CPair[i4, i5]*CPair[m1, m3])/21 -
		(5*CPair[i1, m2]*CPair[i2, m5]*CPair[i3, m4]*CPair[i4, i5]*CPair[m1, m3])/42 +
		(5*CPair[i1, m4]*CPair[i2, m2]*CPair[i3, m5]*CPair[i4, i5]*CPair[m1, m3])/21 -
		(5*CPair[i1, m2]*CPair[i2, m4]*CPair[i3, m5]*CPair[i4, i5]*CPair[m1, m3])/42 -
		(41*CPair[i1, m5]*CPair[i2, i5]*CPair[i3, m4]*CPair[i4, m2]*CPair[m1, m3])/252 +
		(CPair[i1, i5]*CPair[i2, m5]*CPair[i3, m4]*CPair[i4, m2]*CPair[m1, m3])/9 -
		(13*CPair[i1, m4]*CPair[i2, i5]*CPair[i3, m5]*CPair[i4, m2]*CPair[m1, m3])/252 -
		(CPair[i1, i5]*CPair[i2, m4]*CPair[i3, m5]*CPair[i4, m2]*CPair[m1, m3])/9 -
		(CPair[i1, m5]*CPair[i2, m2]*CPair[i3, i5]*CPair[i4, m4]*CPair[m1, m3])/4 +
		(CPair[i1, m2]*CPair[i2, m5]*CPair[i3, i5]*CPair[i4, m4]*CPair[m1, m3])/4 +
		(59*CPair[i1, m5]*CPair[i2, i5]*CPair[i3, m2]*CPair[i4, m4]*CPair[m1, m3])/252 +
		(CPair[i1, i5]*CPair[i2, m5]*CPair[i3, m2]*CPair[i4, m4]*CPair[m1, m3])/18 +
		(5*CPair[i1, m2]*CPair[i2, i5]*CPair[i3, m5]*CPair[i4, m4]*CPair[m1, m3])/126 -
		(CPair[i1, i5]*CPair[i2, m2]*CPair[i3, m5]*CPair[i4, m4]*CPair[m1, m3])/18 -
		(CPair[i1, m4]*CPair[i2, m2]*CPair[i3, i5]*CPair[i4, m5]*CPair[m1, m3])/4 +
		(CPair[i1, m2]*CPair[i2, m4]*CPair[i3, i5]*CPair[i4, m5]*CPair[m1, m3])/4 +
		(31*CPair[i1, m4]*CPair[i2, i5]*CPair[i3, m2]*CPair[i4, m5]*CPair[m1, m3])/252 -
		(CPair[i1, i5]*CPair[i2, m4]*CPair[i3, m2]*CPair[i4, m5]*CPair[m1, m3])/18 -
		(23*CPair[i1, m2]*CPair[i2, i5]*CPair[i3, m4]*CPair[i4, m5]*CPair[m1, m3])/126 +
		(CPair[i1, i5]*CPair[i2, m2]*CPair[i3, m4]*CPair[i4, m5]*CPair[m1, m3])/18 -
		(13*CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m4]*CPair[i5, m2]*CPair[m1, m3])/252 -
		(CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m4]*CPair[i5, m2]*CPair[m1, m3])/9 -
		(41*CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m2]*CPair[m1, m3])/252 +
		(CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m5]*CPair[i5, m2]*CPair[m1, m3])/9 +
		(5*CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m4]*CPair[i5, m2]*CPair[m1, m3])/126 -
		(23*CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m4]*CPair[i5, m2]*CPair[m1, m3])/252 +
		(5*CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m4]*CPair[i5, m2]*CPair[m1, m3])/126 +
		(19*CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m2]*CPair[m1, m3])/126 -
		(79*CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m5]*CPair[i5, m2]*CPair[m1, m3])/252 +
		(19*CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m5]*CPair[i5, m2]*CPair[m1, m3])/126 -
		(8*CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m2]*CPair[i5, m4]*CPair[m1, m3])/63 +
		(7*CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m2]*CPair[i5, m4]*CPair[m1, m3])/36 +
		(17*CPair[i1, m2]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m4]*CPair[m1, m3])/252 -
		(7*CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m5]*CPair[i5, m4]*CPair[m1, m3])/36 +
		(19*CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m2]*CPair[i5, m4]*CPair[m1, m3])/126 -
		(79*CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m2]*CPair[i5, m4]*CPair[m1, m3])/252 +
		(19*CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m2]*CPair[i5, m4]*CPair[m1, m3])/126 -
		(5*CPair[i1, m2]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m4]*CPair[m1, m3])/63 +
		(23*CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m5]*CPair[i5, m4]*CPair[m1, m3])/126 -
		(5*CPair[i1, i2]*CPair[i3, m2]*CPair[i4, m5]*CPair[i5, m4]*CPair[m1, m3])/63 -
		(CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m2]*CPair[i5, m5]*CPair[m1, m3])/63 +
		(11*CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m2]*CPair[i5, m5]*CPair[m1, m3])/36 +
		(73*CPair[i1, m2]*CPair[i2, i4]*CPair[i3, m4]*CPair[i5, m5]*CPair[m1, m3])/252 -
		(11*CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m4]*CPair[i5, m5]*CPair[m1, m3])/36 +
		(5*CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m2]*CPair[i5, m5]*CPair[m1, m3])/126 -
		(23*CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m2]*CPair[i5, m5]*CPair[m1, m3])/252 +
		(5*CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m2]*CPair[i5, m5]*CPair[m1, m3])/126 -
		(19*CPair[i1, m2]*CPair[i2, i3]*CPair[i4, m4]*CPair[i5, m5]*CPair[m1, m3])/63 +
		(79*CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m4]*CPair[i5, m5]*CPair[m1, m3])/126 -
		(19*CPair[i1, i2]*CPair[i3, m2]*CPair[i4, m4]*CPair[i5, m5]*CPair[m1, m3])/63 +
		(3*CPair[i1, m5]*CPair[i2, m3]*CPair[i3, m2]*CPair[i4, i5]*CPair[m1, m4])/14 -
		(3*CPair[i1, m5]*CPair[i2, m2]*CPair[i3, m3]*CPair[i4, i5]*CPair[m1, m4])/14 -
		(3*CPair[i1, m3]*CPair[i2, m2]*CPair[i3, m5]*CPair[i4, i5]*CPair[m1, m4])/14 +
		(3*CPair[i1, m2]*CPair[i2, m3]*CPair[i3, m5]*CPair[i4, i5]*CPair[m1, m4])/14 -
		(13*CPair[i1, m5]*CPair[i2, m3]*CPair[i3, i5]*CPair[i4, m2]*CPair[m1, m4])/84 +
		(13*CPair[i1, m3]*CPair[i2, m5]*CPair[i3, i5]*CPair[i4, m2]*CPair[m1, m4])/84 +
		(17*CPair[i1, m5]*CPair[i2, i5]*CPair[i3, m3]*CPair[i4, m2]*CPair[m1, m4])/63 -
		(11*CPair[i1, i5]*CPair[i2, m5]*CPair[i3, m3]*CPair[i4, m2]*CPair[m1, m4])/126 +
		(CPair[i1, m3]*CPair[i2, i5]*CPair[i3, m5]*CPair[i4, m2]*CPair[m1, m4])/36 +
		(11*CPair[i1, i5]*CPair[i2, m3]*CPair[i3, m5]*CPair[i4, m2]*CPair[m1, m4])/126 +
		(13*CPair[i1, m5]*CPair[i2, m2]*CPair[i3, i5]*CPair[i4, m3]*CPair[m1, m4])/84 -
		(13*CPair[i1, m2]*CPair[i2, m5]*CPair[i3, i5]*CPair[i4, m3]*CPair[m1, m4])/84 -
		(17*CPair[i1, m5]*CPair[i2, i5]*CPair[i3, m2]*CPair[i4, m3]*CPair[m1, m4])/63 +
		(11*CPair[i1, i5]*CPair[i2, m5]*CPair[i3, m2]*CPair[i4, m3]*CPair[m1, m4])/126 -
		(CPair[i1, m2]*CPair[i2, i5]*CPair[i3, m5]*CPair[i4, m3]*CPair[m1, m4])/36 -
		(11*CPair[i1, i5]*CPair[i2, m2]*CPair[i3, m5]*CPair[i4, m3]*CPair[m1, m4])/126 +
		(13*CPair[i1, m3]*CPair[i2, m2]*CPair[i3, i5]*CPair[i4, m5]*CPair[m1, m4])/42 -
		(13*CPair[i1, m2]*CPair[i2, m3]*CPair[i3, i5]*CPair[i4, m5]*CPair[m1, m4])/42 -
		(61*CPair[i1, m3]*CPair[i2, i5]*CPair[i3, m2]*CPair[i4, m5]*CPair[m1, m4])/252 +
		(11*CPair[i1, i5]*CPair[i2, m3]*CPair[i3, m2]*CPair[i4, m5]*CPair[m1, m4])/63 +
		(61*CPair[i1, m2]*CPair[i2, i5]*CPair[i3, m3]*CPair[i4, m5]*CPair[m1, m4])/252 -
		(11*CPair[i1, i5]*CPair[i2, m2]*CPair[i3, m3]*CPair[i4, m5]*CPair[m1, m4])/63 -
		(23*CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m3]*CPair[i5, m2]*CPair[m1, m4])/252 +
		(61*CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m3]*CPair[i5, m2]*CPair[m1, m4])/252 +
		(19*CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m2]*CPair[m1, m4])/126 -
		(61*CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m5]*CPair[i5, m2]*CPair[m1, m4])/252 +
		(5*CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m3]*CPair[i5, m2]*CPair[m1, m4])/63 -
		(CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m3]*CPair[i5, m2]*CPair[m1, m4])/9 +
		(5*CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m3]*CPair[i5, m2]*CPair[m1, m4])/63 -
		(13*CPair[i1, m3]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m2]*CPair[m1, m4])/126 +
		(7*CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m5]*CPair[i5, m2]*CPair[m1, m4])/36 -
		(13*CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m5]*CPair[i5, m2]*CPair[m1, m4])/126 +
		(23*CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m2]*CPair[i5, m3]*CPair[m1, m4])/252 -
		(61*CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m2]*CPair[i5, m3]*CPair[m1, m4])/252 -
		(19*CPair[i1, m2]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m3]*CPair[m1, m4])/126 +
		(61*CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m5]*CPair[i5, m3]*CPair[m1, m4])/252 -
		(5*CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m2]*CPair[i5, m3]*CPair[m1, m4])/63 +
		(CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m2]*CPair[i5, m3]*CPair[m1, m4])/9 -
		(5*CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m2]*CPair[i5, m3]*CPair[m1, m4])/63 +
		(13*CPair[i1, m2]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m3]*CPair[m1, m4])/126 -
		(7*CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m5]*CPair[i5, m3]*CPair[m1, m4])/36 +
		(13*CPair[i1, i2]*CPair[i3, m2]*CPair[i4, m5]*CPair[i5, m3]*CPair[m1, m4])/126 +
		(61*CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m2]*CPair[i5, m5]*CPair[m1, m4])/252 -
		(61*CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m2]*CPair[i5, m5]*CPair[m1, m4])/126 -
		(61*CPair[i1, m2]*CPair[i2, i4]*CPair[i3, m3]*CPair[i5, m5]*CPair[m1, m4])/252 +
		(61*CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m3]*CPair[i5, m5]*CPair[m1, m4])/126 -
		(23*CPair[i1, m3]*CPair[i2, i3]*CPair[i4, m2]*CPair[i5, m5]*CPair[m1, m4])/126 +
		(11*CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m2]*CPair[i5, m5]*CPair[m1, m4])/36 -
		(23*CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m2]*CPair[i5, m5]*CPair[m1, m4])/126 +
		(23*CPair[i1, m2]*CPair[i2, i3]*CPair[i4, m3]*CPair[i5, m5]*CPair[m1, m4])/126 -
		(11*CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m3]*CPair[i5, m5]*CPair[m1, m4])/36 +
		(23*CPair[i1, i2]*CPair[i3, m2]*CPair[i4, m3]*CPair[i5, m5]*CPair[m1, m4])/126 +
		(2*CPair[i1, m4]*CPair[i2, m3]*CPair[i3, m2]*CPair[i4, i5]*CPair[m1, m5])/63 +
		(4*CPair[i1, m3]*CPair[i2, m4]*CPair[i3, m2]*CPair[i4, i5]*CPair[m1, m5])/63 -
		(2*CPair[i1, m4]*CPair[i2, m2]*CPair[i3, m3]*CPair[i4, i5]*CPair[m1, m5])/63 -
		(4*CPair[i1, m2]*CPair[i2, m4]*CPair[i3, m3]*CPair[i4, i5]*CPair[m1, m5])/63 +
		(2*CPair[i1, m3]*CPair[i2, m2]*CPair[i3, m4]*CPair[i4, i5]*CPair[m1, m5])/63 -
		(2*CPair[i1, m2]*CPair[i2, m3]*CPair[i3, m4]*CPair[i4, i5]*CPair[m1, m5])/63 +
		(11*CPair[i1, m4]*CPair[i2, m3]*CPair[i3, i5]*CPair[i4, m2]*CPair[m1, m5])/126 -
		(11*CPair[i1, m3]*CPair[i2, m4]*CPair[i3, i5]*CPair[i4, m2]*CPair[m1, m5])/126 -
		(CPair[i1, m4]*CPair[i2, i5]*CPair[i3, m3]*CPair[i4, m2]*CPair[m1, m5])/7 +
		(11*CPair[i1, i5]*CPair[i2, m4]*CPair[i3, m3]*CPair[i4, m2]*CPair[m1, m5])/63 +
		(CPair[i1, m3]*CPair[i2, i5]*CPair[i3, m4]*CPair[i4, m2]*CPair[m1, m5])/42 -
		(11*CPair[i1, i5]*CPair[i2, m3]*CPair[i3, m4]*CPair[i4, m2]*CPair[m1, m5])/63 -
		(11*CPair[i1, m4]*CPair[i2, m2]*CPair[i3, i5]*CPair[i4, m3]*CPair[m1, m5])/126 +
		(11*CPair[i1, m2]*CPair[i2, m4]*CPair[i3, i5]*CPair[i4, m3]*CPair[m1, m5])/126 +
		(CPair[i1, m4]*CPair[i2, i5]*CPair[i3, m2]*CPair[i4, m3]*CPair[m1, m5])/7 -
		(11*CPair[i1, i5]*CPair[i2, m4]*CPair[i3, m2]*CPair[i4, m3]*CPair[m1, m5])/63 -
		(CPair[i1, m2]*CPair[i2, i5]*CPair[i3, m4]*CPair[i4, m3]*CPair[m1, m5])/42 +
		(11*CPair[i1, i5]*CPair[i2, m2]*CPair[i3, m4]*CPair[i4, m3]*CPair[m1, m5])/63 -
		(11*CPair[i1, m3]*CPair[i2, m2]*CPair[i3, i5]*CPair[i4, m4]*CPair[m1, m5])/63 +
		(11*CPair[i1, m2]*CPair[i2, m3]*CPair[i3, i5]*CPair[i4, m4]*CPair[m1, m5])/63 +
		(CPair[i1, m3]*CPair[i2, i5]*CPair[i3, m2]*CPair[i4, m4]*CPair[m1, m5])/6 -
		(22*CPair[i1, i5]*CPair[i2, m3]*CPair[i3, m2]*CPair[i4, m4]*CPair[m1, m5])/63 -
		(CPair[i1, m2]*CPair[i2, i5]*CPair[i3, m3]*CPair[i4, m4]*CPair[m1, m5])/6 +
		(22*CPair[i1, i5]*CPair[i2, m2]*CPair[i3, m3]*CPair[i4, m4]*CPair[m1, m5])/63 +
		(19*CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m3]*CPair[i5, m2]*CPair[m1, m5])/126 -
		(11*CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m3]*CPair[i5, m2]*CPair[m1, m5])/126 -
		(2*CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m4]*CPair[i5, m2]*CPair[m1, m5])/63 +
		(11*CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m4]*CPair[i5, m2]*CPair[m1, m5])/126 -
		(5*CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m3]*CPair[i5, m2]*CPair[m1, m5])/63 +
		(CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m3]*CPair[i5, m2]*CPair[m1, m5])/9 -
		(5*CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m3]*CPair[i5, m2]*CPair[m1, m5])/63 +
		(2*CPair[i1, m3]*CPair[i2, i3]*CPair[i4, m4]*CPair[i5, m2]*CPair[m1, m5])/63 +
		(CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m4]*CPair[i5, m2]*CPair[m1, m5])/18 -
		(CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m4]*CPair[i5, m2]*CPair[m1, m5])/9 -
		(19*CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m2]*CPair[i5, m3]*CPair[m1, m5])/126 +
		(11*CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m2]*CPair[i5, m3]*CPair[m1, m5])/126 +
		(2*CPair[i1, m2]*CPair[i2, i4]*CPair[i3, m4]*CPair[i5, m3]*CPair[m1, m5])/63 -
		(11*CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m4]*CPair[i5, m3]*CPair[m1, m5])/126 +
		(5*CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m2]*CPair[i5, m3]*CPair[m1, m5])/63 -
		(CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m2]*CPair[i5, m3]*CPair[m1, m5])/9 +
		(5*CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m2]*CPair[i5, m3]*CPair[m1, m5])/63 -
		(2*CPair[i1, m2]*CPair[i2, i3]*CPair[i4, m4]*CPair[i5, m3]*CPair[m1, m5])/63 -
		(CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m4]*CPair[i5, m3]*CPair[m1, m5])/18 +
		(CPair[i1, i2]*CPair[i3, m2]*CPair[i4, m4]*CPair[i5, m3]*CPair[m1, m5])/9 -
		(23*CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m2]*CPair[i5, m4]*CPair[m1, m5])/126 +
		(11*CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m2]*CPair[i5, m4]*CPair[m1, m5])/63 +
		(23*CPair[i1, m2]*CPair[i2, i4]*CPair[i3, m3]*CPair[i5, m4]*CPair[m1, m5])/126 -
		(11*CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m3]*CPair[i5, m4]*CPair[m1, m5])/63 +
		(CPair[i1, m3]*CPair[i2, i3]*CPair[i4, m2]*CPair[i5, m4]*CPair[m1, m5])/9 -
		(CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m2]*CPair[i5, m4]*CPair[m1, m5])/18 -
		(2*CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m2]*CPair[i5, m4]*CPair[m1, m5])/63 -
		(CPair[i1, m2]*CPair[i2, i3]*CPair[i4, m3]*CPair[i5, m4]*CPair[m1, m5])/9 +
		(CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m3]*CPair[i5, m4]*CPair[m1, m5])/18 +
		(2*CPair[i1, i2]*CPair[i3, m2]*CPair[i4, m3]*CPair[i5, m4]*CPair[m1, m5])/63 -
		(CPair[i1, m5]*CPair[i2, m1]*CPair[i3, m4]*CPair[i4, i5]*CPair[m2, m3])/7 +
		(CPair[i1, m1]*CPair[i2, m5]*CPair[i3, m4]*CPair[i4, i5]*CPair[m2, m3])/7 -
		(CPair[i1, m4]*CPair[i2, m1]*CPair[i3, m5]*CPair[i4, i5]*CPair[m2, m3])/7 +
		(CPair[i1, m1]*CPair[i2, m4]*CPair[i3, m5]*CPair[i4, i5]*CPair[m2, m3])/7 +
		(CPair[i1, m5]*CPair[i2, i5]*CPair[i3, m4]*CPair[i4, m1]*CPair[m2, m3])/6 -
		(5*CPair[i1, i5]*CPair[i2, m5]*CPair[i3, m4]*CPair[i4, m1]*CPair[m2, m3])/63 -
		(CPair[i1, m4]*CPair[i2, i5]*CPair[i3, m5]*CPair[i4, m1]*CPair[m2, m3])/42 +
		(5*CPair[i1, i5]*CPair[i2, m4]*CPair[i3, m5]*CPair[i4, m1]*CPair[m2, m3])/63 +
		(3*CPair[i1, m5]*CPair[i2, m1]*CPair[i3, i5]*CPair[i4, m4]*CPair[m2, m3])/14 -
		(3*CPair[i1, m1]*CPair[i2, m5]*CPair[i3, i5]*CPair[i4, m4]*CPair[m2, m3])/14 -
		(5*CPair[i1, m5]*CPair[i2, i5]*CPair[i3, m1]*CPair[i4, m4]*CPair[m2, m3])/42 +
		(2*CPair[i1, i5]*CPair[i2, m5]*CPair[i3, m1]*CPair[i4, m4]*CPair[m2, m3])/63 -
		(CPair[i1, m1]*CPair[i2, i5]*CPair[i3, m5]*CPair[i4, m4]*CPair[m2, m3])/7 -
		(2*CPair[i1, i5]*CPair[i2, m1]*CPair[i3, m5]*CPair[i4, m4]*CPair[m2, m3])/63 +
		(3*CPair[i1, m4]*CPair[i2, m1]*CPair[i3, i5]*CPair[i4, m5]*CPair[m2, m3])/14 -
		(3*CPair[i1, m1]*CPair[i2, m4]*CPair[i3, i5]*CPair[i4, m5]*CPair[m2, m3])/14 -
		(CPair[i1, m4]*CPair[i2, i5]*CPair[i3, m1]*CPair[i4, m5]*CPair[m2, m3])/42 +
		(CPair[i1, i5]*CPair[i2, m4]*CPair[i3, m1]*CPair[i4, m5]*CPair[m2, m3])/9 +
		(CPair[i1, m1]*CPair[i2, i5]*CPair[i3, m4]*CPair[i4, m5]*CPair[m2, m3])/7 -
		(CPair[i1, i5]*CPair[i2, m1]*CPair[i3, m4]*CPair[i4, m5]*CPair[m2, m3])/9 -
		(CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m4]*CPair[i5, m1]*CPair[m2, m3])/42 +
		(5*CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m4]*CPair[i5, m1]*CPair[m2, m3])/63 +
		(CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m1]*CPair[m2, m3])/6 -
		(5*CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m5]*CPair[i5, m1]*CPair[m2, m3])/63 -
		(CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m4]*CPair[i5, m1]*CPair[m2, m3])/21 +
		(5*CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m4]*CPair[i5, m1]*CPair[m2, m3])/126 +
		(2*CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m4]*CPair[i5, m1]*CPair[m2, m3])/63 -
		(2*CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m1]*CPair[m2, m3])/7 +
		(19*CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m5]*CPair[i5, m1]*CPair[m2, m3])/126 +
		(CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m5]*CPair[i5, m1]*CPair[m2, m3])/63 +
		(4*CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m1]*CPair[i5, m4]*CPair[m2, m3])/21 -
		(13*CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m1]*CPair[i5, m4]*CPair[m2, m3])/126 -
		(CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m4]*CPair[m2, m3])/14 +
		(13*CPair[i1, i4]*CPair[i2, m1]*CPair[i3, m5]*CPair[i5, m4]*CPair[m2, m3])/126 -
		(2*CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m1]*CPair[i5, m4]*CPair[m2, m3])/7 +
		(19*CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m1]*CPair[i5, m4]*CPair[m2, m3])/126 +
		(CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m1]*CPair[i5, m4]*CPair[m2, m3])/63 +
		(2*CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m4]*CPair[m2, m3])/21 -
		(5*CPair[i1, i3]*CPair[i2, m1]*CPair[i4, m5]*CPair[i5, m4]*CPair[m2, m3])/63 -
		(4*CPair[i1, i2]*CPair[i3, m1]*CPair[i4, m5]*CPair[i5, m4]*CPair[m2, m3])/63 +
		(2*CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m1]*CPair[i5, m5]*CPair[m2, m3])/21 -
		(23*CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m1]*CPair[i5, m5]*CPair[m2, m3])/126 -
		(5*CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m4]*CPair[i5, m5]*CPair[m2, m3])/14 +
		(23*CPair[i1, i4]*CPair[i2, m1]*CPair[i3, m4]*CPair[i5, m5]*CPair[m2, m3])/126 -
		(CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m1]*CPair[i5, m5]*CPair[m2, m3])/21 +
		(5*CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m1]*CPair[i5, m5]*CPair[m2, m3])/126 +
		(2*CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m1]*CPair[i5, m5]*CPair[m2, m3])/63 +
		(4*CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m4]*CPair[i5, m5]*CPair[m2, m3])/7 -
		(19*CPair[i1, i3]*CPair[i2, m1]*CPair[i4, m4]*CPair[i5, m5]*CPair[m2, m3])/63 -
		(2*CPair[i1, i2]*CPair[i3, m1]*CPair[i4, m4]*CPair[i5, m5]*CPair[m2, m3])/63 -
		(CPair[i1, m5]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m4]*CPair[m2, m3])/42 +
		(CPair[i1, i5]*CPair[i2, m5]*CPair[i3, i4]*CPair[m1, m4]*CPair[m2, m3])/42 -
		(4*CPair[i1, m5]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m4]*CPair[m2, m3])/21 +
		(5*CPair[i1, i4]*CPair[i2, m5]*CPair[i3, i5]*CPair[m1, m4]*CPair[m2, m3])/42 -
		(CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m5]*CPair[m1, m4]*CPair[m2, m3])/14 +
		(CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m5]*CPair[m1, m4]*CPair[m2, m3])/14 +
		(5*CPair[i1, m5]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m4]*CPair[m2, m3])/21 -
		(CPair[i1, i3]*CPair[i2, m5]*CPair[i4, i5]*CPair[m1, m4]*CPair[m2, m3])/6 -
		(CPair[i1, i2]*CPair[i3, m5]*CPair[i4, i5]*CPair[m1, m4]*CPair[m2, m3])/42 +
		(2*CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m5]*CPair[m1, m4]*CPair[m2, m3])/21 -
		(2*CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m5]*CPair[m1, m4]*CPair[m2, m3])/21 +
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m5]*CPair[m1, m4]*CPair[m2, m3])/42 -
		(11*CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m5]*CPair[m1, m4]*CPair[m2, m3])/42 +
		(11*CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m5]*CPair[m1, m4]*CPair[m2, m3])/42 +
		(CPair[i1, m4]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m5]*CPair[m2, m3])/42 -
		(2*CPair[i1, i5]*CPair[i2, m4]*CPair[i3, i4]*CPair[m1, m5]*CPair[m2, m3])/21 -
		(5*CPair[i1, m4]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m5]*CPair[m2, m3])/21 +
		(5*CPair[i1, i4]*CPair[i2, m4]*CPair[i3, i5]*CPair[m1, m5]*CPair[m2, m3])/21 +
		(2*CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m4]*CPair[m1, m5]*CPair[m2, m3])/7 -
		(2*CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m4]*CPair[m1, m5]*CPair[m2, m3])/7 +
		(5*CPair[i1, m4]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m5]*CPair[m2, m3])/21 -
		(CPair[i1, i3]*CPair[i2, m4]*CPair[i4, i5]*CPair[m1, m5]*CPair[m2, m3])/6 -
		(CPair[i1, i2]*CPair[i3, m4]*CPair[i4, i5]*CPair[m1, m5]*CPair[m2, m3])/42 -
		(11*CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m4]*CPair[m1, m5]*CPair[m2, m3])/42 +
		(11*CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m4]*CPair[m1, m5]*CPair[m2, m3])/42 +
		(2*CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m4]*CPair[m1, m5]*CPair[m2, m3])/21 -
		(2*CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m4]*CPair[m1, m5]*CPair[m2, m3])/21 +
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m4]*CPair[m1, m5]*CPair[m2, m3])/42 -
		(CPair[i1, m3]*CPair[i2, m5]*CPair[i3, m1]*CPair[i4, i5]*CPair[m2, m4])/42 +
		(5*CPair[i1, m5]*CPair[i2, m1]*CPair[i3, m3]*CPair[i4, i5]*CPair[m2, m4])/42 -
		(3*CPair[i1, m1]*CPair[i2, m5]*CPair[i3, m3]*CPair[i4, i5]*CPair[m2, m4])/14 +
		(3*CPair[i1, m3]*CPair[i2, m1]*CPair[i3, m5]*CPair[i4, i5]*CPair[m2, m4])/14 -
		(2*CPair[i1, m1]*CPair[i2, m3]*CPair[i3, m5]*CPair[i4, i5]*CPair[m2, m4])/21 +
		(CPair[i1, m5]*CPair[i2, m3]*CPair[i3, i5]*CPair[i4, m1]*CPair[m2, m4])/28 -
		(CPair[i1, m3]*CPair[i2, m5]*CPair[i3, i5]*CPair[i4, m1]*CPair[m2, m4])/28 -
		(3*CPair[i1, m5]*CPair[i2, i5]*CPair[i3, m3]*CPair[i4, m1]*CPair[m2, m4])/28 +
		(19*CPair[i1, i5]*CPair[i2, m5]*CPair[i3, m3]*CPair[i4, m1]*CPair[m2, m4])/126 +
		(CPair[i1, m3]*CPair[i2, i5]*CPair[i3, m5]*CPair[i4, m1]*CPair[m2, m4])/21 -
		(19*CPair[i1, i5]*CPair[i2, m3]*CPair[i3, m5]*CPair[i4, m1]*CPair[m2, m4])/126 -
		(3*CPair[i1, m5]*CPair[i2, m1]*CPair[i3, i5]*CPair[i4, m3]*CPair[m2, m4])/14 +
		(3*CPair[i1, m1]*CPair[i2, m5]*CPair[i3, i5]*CPair[i4, m3]*CPair[m2, m4])/14 +
		(19*CPair[i1, m5]*CPair[i2, i5]*CPair[i3, m1]*CPair[i4, m3]*CPair[m2, m4])/84 -
		(2*CPair[i1, i5]*CPair[i2, m5]*CPair[i3, m1]*CPair[i4, m3]*CPair[m2, m4])/63 +
		(CPair[i1, m1]*CPair[i2, i5]*CPair[i3, m5]*CPair[i4, m3]*CPair[m2, m4])/84 +
		(2*CPair[i1, i5]*CPair[i2, m1]*CPair[i3, m5]*CPair[i4, m3]*CPair[m2, m4])/63 -
		(CPair[i1, m3]*CPair[i2, m1]*CPair[i3, i5]*CPair[i4, m5]*CPair[m2, m4])/4 +
		(CPair[i1, m1]*CPair[i2, m3]*CPair[i3, i5]*CPair[i4, m5]*CPair[m2, m4])/4 +
		(2*CPair[i1, m3]*CPair[i2, i5]*CPair[i3, m1]*CPair[i4, m5]*CPair[m2, m4])/21 -
		(23*CPair[i1, i5]*CPair[i2, m3]*CPair[i3, m1]*CPair[i4, m5]*CPair[m2, m4])/126 -
		(23*CPair[i1, m1]*CPair[i2, i5]*CPair[i3, m3]*CPair[i4, m5]*CPair[m2, m4])/84 +
		(23*CPair[i1, i5]*CPair[i2, m1]*CPair[i3, m3]*CPair[i4, m5]*CPair[m2, m4])/126 +
		(CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m3]*CPair[i5, m1]*CPair[m2, m4])/42 -
		(23*CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m3]*CPair[i5, m1]*CPair[m2, m4])/252 -
		(9*CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m1]*CPair[m2, m4])/28 +
		(23*CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m5]*CPair[i5, m1]*CPair[m2, m4])/252 -
		(CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m3]*CPair[i5, m1]*CPair[m2, m4])/42 -
		(13*CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m3]*CPair[i5, m1]*CPair[m2, m4])/252 +
		(11*CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m3]*CPair[i5, m1]*CPair[m2, m4])/126 +
		(4*CPair[i1, m3]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m1]*CPair[m2, m4])/21 -
		(8*CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m5]*CPair[i5, m1]*CPair[m2, m4])/63 +
		(2*CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m5]*CPair[i5, m1]*CPair[m2, m4])/63 -
		(9*CPair[i1, m5]*CPair[i2, i4]*CPair[i3, m1]*CPair[i5, m3]*CPair[m2, m4])/28 +
		(19*CPair[i1, i4]*CPair[i2, m5]*CPair[i3, m1]*CPair[i5, m3]*CPair[m2, m4])/126 +
		(CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m5]*CPair[i5, m3]*CPair[m2, m4])/12 -
		(19*CPair[i1, i4]*CPair[i2, m1]*CPair[i3, m5]*CPair[i5, m3]*CPair[m2, m4])/126 +
		(CPair[i1, m5]*CPair[i2, i3]*CPair[i4, m1]*CPair[i5, m3]*CPair[m2, m4])/6 -
		(41*CPair[i1, i3]*CPair[i2, m5]*CPair[i4, m1]*CPair[i5, m3]*CPair[m2, m4])/252 +
		(CPair[i1, i2]*CPair[i3, m5]*CPair[i4, m1]*CPair[i5, m3]*CPair[m2, m4])/18 -
		(CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m5]*CPair[i5, m3]*CPair[m2, m4])/14 +
		(17*CPair[i1, i3]*CPair[i2, m1]*CPair[i4, m5]*CPair[i5, m3]*CPair[m2, m4])/252 +
		(11*CPair[i1, i2]*CPair[i3, m1]*CPair[i4, m5]*CPair[i5, m3]*CPair[m2, m4])/126 -
		(3*CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m1]*CPair[i5, m5]*CPair[m2, m4])/28 +
		(61*CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m1]*CPair[i5, m5]*CPair[m2, m4])/252 +
		(9*CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m3]*CPair[i5, m5]*CPair[m2, m4])/14 -
		(61*CPair[i1, i4]*CPair[i2, m1]*CPair[i3, m3]*CPair[i5, m5]*CPair[m2, m4])/252 +
		(2*CPair[i1, m3]*CPair[i2, i3]*CPair[i4, m1]*CPair[i5, m5]*CPair[m2, m4])/21 -
		(CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m1]*CPair[i5, m5]*CPair[m2, m4])/63 -
		(11*CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m1]*CPair[i5, m5]*CPair[m2, m4])/63 -
		(5*CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m3]*CPair[i5, m5]*CPair[m2, m4])/14 +
		(73*CPair[i1, i3]*CPair[i2, m1]*CPair[i4, m3]*CPair[i5, m5]*CPair[m2, m4])/252 -
		(11*CPair[i1, i2]*CPair[i3, m1]*CPair[i4, m3]*CPair[i5, m5]*CPair[m2, m4])/126 -
		(2*CPair[i1, m5]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m3]*CPair[m2, m4])/21 -
		(CPair[i1, i5]*CPair[i2, m5]*CPair[i3, i4]*CPair[m1, m3]*CPair[m2, m4])/7 +
		(19*CPair[i1, m5]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m3]*CPair[m2, m4])/42 -
		(2*CPair[i1, i4]*CPair[i2, m5]*CPair[i3, i5]*CPair[m1, m3]*CPair[m2, m4])/7 +
		(13*CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m5]*CPair[m1, m3]*CPair[m2, m4])/42 +
		(CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m5]*CPair[m1, m3]*CPair[m2, m4])/21 -
		(2*CPair[i1, m5]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m3]*CPair[m2, m4])/7 +
		(23*CPair[i1, i3]*CPair[i2, m5]*CPair[i4, i5]*CPair[m1, m3]*CPair[m2, m4])/42 -
		(2*CPair[i1, i2]*CPair[i3, m5]*CPair[i4, i5]*CPair[m1, m3]*CPair[m2, m4])/7 -
		(2*CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m5]*CPair[m1, m3]*CPair[m2, m4])/21 +
		(3*CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m5]*CPair[m1, m3]*CPair[m2, m4])/14 -
		(2*CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m5]*CPair[m1, m3]*CPair[m2, m4])/21 +
		(11*CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m5]*CPair[m1, m3]*CPair[m2, m4])/42 -
		(17*CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m5]*CPair[m1, m3]*CPair[m2, m4])/21 +
		(11*CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m5]*CPair[m1, m3]*CPair[m2, m4])/42 -
		(CPair[i1, m3]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m5]*CPair[m2, m4])/6 +
		(3*CPair[i1, i5]*CPair[i2, m3]*CPair[i3, i4]*CPair[m1, m5]*CPair[m2, m4])/7 +
		(25*CPair[i1, m3]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m5]*CPair[m2, m4])/42 -
		(4*CPair[i1, i4]*CPair[i2, m3]*CPair[i3, i5]*CPair[m1, m5]*CPair[m2, m4])/7 -
		(13*CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m3]*CPair[m1, m5]*CPair[m2, m4])/14 +
		(9*CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m3]*CPair[m1, m5]*CPair[m2, m4])/14 -
		(5*CPair[i1, m3]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m5]*CPair[m2, m4])/14 +
		(5*CPair[i1, i3]*CPair[i2, m3]*CPair[i4, i5]*CPair[m1, m5]*CPair[m2, m4])/42 +
		(5*CPair[i1, i2]*CPair[i3, m3]*CPair[i4, i5]*CPair[m1, m5]*CPair[m2, m4])/21 +
		(2*CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m3]*CPair[m1, m5]*CPair[m2, m4])/7 -
		(8*CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m3]*CPair[m1, m5]*CPair[m2, m4])/21 +
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m3]*CPair[m1, m5]*CPair[m2, m4])/42 -
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m3]*CPair[m1, m5]*CPair[m2, m4])/14 +
		(13*CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m3]*CPair[m1, m5]*CPair[m2, m4])/42 -
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m3]*CPair[m1, m5]*CPair[m2, m4])/6 +
		(23*CPair[i1, m4]*CPair[i2, m3]*CPair[i3, m1]*CPair[i4, i5]*CPair[m2, m5])/126 -
		(11*CPair[i1, m3]*CPair[i2, m4]*CPair[i3, m1]*CPair[i4, i5]*CPair[m2, m5])/126 -
		(4*CPair[i1, m4]*CPair[i2, m1]*CPair[i3, m3]*CPair[i4, i5]*CPair[m2, m5])/63 -
		(19*CPair[i1, m1]*CPair[i2, m4]*CPair[i3, m3]*CPair[i4, i5]*CPair[m2, m5])/126 -
		(2*CPair[i1, m3]*CPair[i2, m1]*CPair[i3, m4]*CPair[i4, i5]*CPair[m2, m5])/63 +
		(19*CPair[i1, m1]*CPair[i2, m3]*CPair[i3, m4]*CPair[i4, i5]*CPair[m2, m5])/126 -
		(13*CPair[i1, m4]*CPair[i2, m3]*CPair[i3, i5]*CPair[i4, m1]*CPair[m2, m5])/63 +
		(13*CPair[i1, m3]*CPair[i2, m4]*CPair[i3, i5]*CPair[i4, m1]*CPair[m2, m5])/63 +
		(7*CPair[i1, m4]*CPair[i2, i5]*CPair[i3, m3]*CPair[i4, m1]*CPair[m2, m5])/36 -
		(CPair[i1, i5]*CPair[i2, m4]*CPair[i3, m3]*CPair[i4, m1]*CPair[m2, m5])/7 -
		(79*CPair[i1, m3]*CPair[i2, i5]*CPair[i3, m4]*CPair[i4, m1]*CPair[m2, m5])/252 +
		(CPair[i1, i5]*CPair[i2, m3]*CPair[i3, m4]*CPair[i4, m1]*CPair[m2, m5])/7 +
		(CPair[i1, m4]*CPair[i2, m1]*CPair[i3, i5]*CPair[i4, m3]*CPair[m2, m5])/36 -
		(CPair[i1, m1]*CPair[i2, m4]*CPair[i3, i5]*CPair[i4, m3]*CPair[m2, m5])/36 -
		(79*CPair[i1, m4]*CPair[i2, i5]*CPair[i3, m1]*CPair[i4, m3]*CPair[m2, m5])/252 +
		(CPair[i1, i5]*CPair[i2, m4]*CPair[i3, m1]*CPair[i4, m3]*CPair[m2, m5])/42 -
		(13*CPair[i1, m1]*CPair[i2, i5]*CPair[i3, m4]*CPair[i4, m3]*CPair[m2, m5])/126 -
		(CPair[i1, i5]*CPair[i2, m1]*CPair[i3, m4]*CPair[i4, m3]*CPair[m2, m5])/42 +
		(59*CPair[i1, m3]*CPair[i2, m1]*CPair[i3, i5]*CPair[i4, m4]*CPair[m2, m5])/252 -
		(59*CPair[i1, m1]*CPair[i2, m3]*CPair[i3, i5]*CPair[i4, m4]*CPair[m2, m5])/252 -
		(23*CPair[i1, m3]*CPair[i2, i5]*CPair[i3, m1]*CPair[i4, m4]*CPair[m2, m5])/252 +
		(CPair[i1, i5]*CPair[i2, m3]*CPair[i3, m1]*CPair[i4, m4]*CPair[m2, m5])/6 +
		(79*CPair[i1, m1]*CPair[i2, i5]*CPair[i3, m3]*CPair[i4, m4]*CPair[m2, m5])/126 -
		(CPair[i1, i5]*CPair[i2, m1]*CPair[i3, m3]*CPair[i4, m4]*CPair[m2, m5])/6 -
		(3*CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m3]*CPair[i5, m1]*CPair[m2, m5])/28 +
		(17*CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m3]*CPair[i5, m1]*CPair[m2, m5])/63 +
		(19*CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m4]*CPair[i5, m1]*CPair[m2, m5])/84 -
		(17*CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m4]*CPair[i5, m1]*CPair[m2, m5])/63 +
		(CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m3]*CPair[i5, m1]*CPair[m2, m5])/6 -
		(41*CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m3]*CPair[i5, m1]*CPair[m2, m5])/252 +
		(CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m3]*CPair[i5, m1]*CPair[m2, m5])/18 -
		(5*CPair[i1, m3]*CPair[i2, i3]*CPair[i4, m4]*CPair[i5, m1]*CPair[m2, m5])/42 +
		(59*CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m4]*CPair[i5, m1]*CPair[m2, m5])/252 -
		(31*CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m4]*CPair[i5, m1]*CPair[m2, m5])/126 +
		(CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m1]*CPair[i5, m3]*CPair[m2, m5])/21 +
		(CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m1]*CPair[i5, m3]*CPair[m2, m5])/36 +
		(CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m4]*CPair[i5, m3]*CPair[m2, m5])/84 -
		(CPair[i1, i4]*CPair[i2, m1]*CPair[i3, m4]*CPair[i5, m3]*CPair[m2, m5])/36 -
		(CPair[i1, m4]*CPair[i2, i3]*CPair[i4, m1]*CPair[i5, m3]*CPair[m2, m5])/42 -
		(13*CPair[i1, i3]*CPair[i2, m4]*CPair[i4, m1]*CPair[i5, m3]*CPair[m2, m5])/252 +
		(11*CPair[i1, i2]*CPair[i3, m4]*CPair[i4, m1]*CPair[i5, m3]*CPair[m2, m5])/126 -
		(CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m4]*CPair[i5, m3]*CPair[m2, m5])/7 +
		(5*CPair[i1, i3]*CPair[i2, m1]*CPair[i4, m4]*CPair[i5, m3]*CPair[m2, m5])/126 -
		(CPair[i1, i2]*CPair[i3, m1]*CPair[i4, m4]*CPair[i5, m3]*CPair[m2, m5])/63 +
		(2*CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m1]*CPair[i5, m4]*CPair[m2, m5])/21 -
		(61*CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m1]*CPair[i5, m4]*CPair[m2, m5])/252 -
		(23*CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m3]*CPair[i5, m4]*CPair[m2, m5])/84 +
		(61*CPair[i1, i4]*CPair[i2, m1]*CPair[i3, m3]*CPair[i5, m4]*CPair[m2, m5])/252 -
		(CPair[i1, m3]*CPair[i2, i3]*CPair[i4, m1]*CPair[i5, m4]*CPair[m2, m5])/42 +
		(31*CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m1]*CPair[i5, m4]*CPair[m2, m5])/252 -
		(5*CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m1]*CPair[i5, m4]*CPair[m2, m5])/126 +
		(CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m3]*CPair[i5, m4]*CPair[m2, m5])/7 -
		(23*CPair[i1, i3]*CPair[i2, m1]*CPair[i4, m3]*CPair[i5, m4]*CPair[m2, m5])/126 +
		(10*CPair[i1, i2]*CPair[i3, m1]*CPair[i4, m3]*CPair[i5, m4]*CPair[m2, m5])/63 +
		(CPair[i1, m4]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m3]*CPair[m2, m5])/42 +
		(CPair[i1, i5]*CPair[i2, m4]*CPair[i3, i4]*CPair[m1, m3]*CPair[m2, m5])/7 +
		(CPair[i1, m4]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m3]*CPair[m2, m5])/3 -
		(4*CPair[i1, i4]*CPair[i2, m4]*CPair[i3, i5]*CPair[m1, m3]*CPair[m2, m5])/7 -
		(8*CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m4]*CPair[m1, m3]*CPair[m2, m5])/21 +
		(31*CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m4]*CPair[m1, m3]*CPair[m2, m5])/42 -
		(2*CPair[i1, m4]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m3]*CPair[m2, m5])/7 +
		(23*CPair[i1, i3]*CPair[i2, m4]*CPair[i4, i5]*CPair[m1, m3]*CPair[m2, m5])/42 -
		(2*CPair[i1, i2]*CPair[i3, m4]*CPair[i4, i5]*CPair[m1, m3]*CPair[m2, m5])/7 +
		(11*CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m4]*CPair[m1, m3]*CPair[m2, m5])/42 -
		(17*CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m4]*CPair[m1, m3]*CPair[m2, m5])/21 +
		(11*CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m4]*CPair[m1, m3]*CPair[m2, m5])/42 -
		(2*CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m4]*CPair[m1, m3]*CPair[m2, m5])/21 +
		(3*CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m4]*CPair[m1, m3]*CPair[m2, m5])/14 -
		(2*CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m4]*CPair[m1, m3]*CPair[m2, m5])/21 +
		(13*CPair[i1, m3]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m4]*CPair[m2, m5])/42 -
		(2*CPair[i1, i5]*CPair[i2, m3]*CPair[i3, i4]*CPair[m1, m4]*CPair[m2, m5])/7 -
		(17*CPair[i1, m3]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m4]*CPair[m2, m5])/21 +
		(15*CPair[i1, i4]*CPair[i2, m3]*CPair[i3, i5]*CPair[m1, m4]*CPair[m2, m5])/14 +
		(9*CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m3]*CPair[m1, m4]*CPair[m2, m5])/14 -
		(9*CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m3]*CPair[m1, m4]*CPair[m2, m5])/7 +
		(8*CPair[i1, m3]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m4]*CPair[m2, m5])/21 -
		(17*CPair[i1, i3]*CPair[i2, m3]*CPair[i4, i5]*CPair[m1, m4]*CPair[m2, m5])/21 +
		(CPair[i1, i2]*CPair[i3, m3]*CPair[i4, i5]*CPair[m1, m4]*CPair[m2, m5])/2 -
		(2*CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m3]*CPair[m1, m4]*CPair[m2, m5])/7 +
		(31*CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m3]*CPair[m1, m4]*CPair[m2, m5])/42 -
		(5*CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m3]*CPair[m1, m4]*CPair[m2, m5])/21 +
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m3]*CPair[m1, m4]*CPair[m2, m5])/14 +
		(CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m3]*CPair[m1, m4]*CPair[m2, m5])/21 -
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m3]*CPair[m1, m4]*CPair[m2, m5])/21 +
		(2*CPair[i1, m5]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m2]*CPair[m3, m4])/21 +
		(2*CPair[i1, i5]*CPair[i2, m5]*CPair[i3, i4]*CPair[m1, m2]*CPair[m3, m4])/21 -
		(2*CPair[i1, m5]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m2]*CPair[m3, m4])/21 +
		(CPair[i1, i4]*CPair[i2, m5]*CPair[i3, i5]*CPair[m1, m2]*CPair[m3, m4])/21 -
		(CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m5]*CPair[m1, m2]*CPair[m3, m4])/6 -
		(CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m5]*CPair[m1, m2]*CPair[m3, m4])/21 -
		(CPair[i1, m5]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m2]*CPair[m3, m4])/42 -
		(CPair[i1, i3]*CPair[i2, m5]*CPair[i4, i5]*CPair[m1, m2]*CPair[m3, m4])/6 +
		(5*CPair[i1, i2]*CPair[i3, m5]*CPair[i4, i5]*CPair[m1, m2]*CPair[m3, m4])/21 +
		(CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m5]*CPair[m1, m2]*CPair[m3, m4])/42 -
		(2*CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m5]*CPair[m1, m2]*CPair[m3, m4])/21 +
		(2*CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m5]*CPair[m1, m2]*CPair[m3, m4])/21 +
		(11*CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m5]*CPair[m1, m2]*CPair[m3, m4])/42 -
		(11*CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m5]*CPair[m1, m2]*CPair[m3, m4])/42 +
		(2*CPair[i1, m2]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m5]*CPair[m3, m4])/21 -
		(11*CPair[i1, i5]*CPair[i2, m2]*CPair[i3, i4]*CPair[m1, m5]*CPair[m3, m4])/42 -
		(5*CPair[i1, m2]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m5]*CPair[m3, m4])/21 +
		(11*CPair[i1, i4]*CPair[i2, m2]*CPair[i3, i5]*CPair[m1, m5]*CPair[m3, m4])/42 +
		(3*CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m2]*CPair[m1, m5]*CPair[m3, m4])/7 -
		(2*CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m2]*CPair[m1, m5]*CPair[m3, m4])/7 +
		(5*CPair[i1, m2]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m5]*CPair[m3, m4])/42 -
		(5*CPair[i1, i2]*CPair[i3, m2]*CPair[i4, i5]*CPair[m1, m5]*CPair[m3, m4])/42 -
		(2*CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m2]*CPair[m1, m5]*CPair[m3, m4])/21 +
		(CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m2]*CPair[m1, m5]*CPair[m3, m4])/7 -
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m2]*CPair[m1, m5]*CPair[m3, m4])/42 +
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m2]*CPair[m1, m5]*CPair[m3, m4])/42 -
		(CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m2]*CPair[m1, m5]*CPair[m3, m4])/7 +
		(2*CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m2]*CPair[m1, m5]*CPair[m3, m4])/21 -
		(11*CPair[i1, m1]*CPair[i2, i5]*CPair[i3, i4]*CPair[m2, m5]*CPair[m3, m4])/42 +
		(2*CPair[i1, i5]*CPair[i2, m1]*CPair[i3, i4]*CPair[m2, m5]*CPair[m3, m4])/21 +
		(11*CPair[i1, m1]*CPair[i2, i4]*CPair[i3, i5]*CPair[m2, m5]*CPair[m3, m4])/42 -
		(5*CPair[i1, i4]*CPair[i2, m1]*CPair[i3, i5]*CPair[m2, m5]*CPair[m3, m4])/21 -
		(CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m1]*CPair[m2, m5]*CPair[m3, m4])/6 +
		(13*CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m1]*CPair[m2, m5]*CPair[m3, m4])/42 +
		(5*CPair[i1, i3]*CPair[i2, m1]*CPair[i4, i5]*CPair[m2, m5]*CPair[m3, m4])/42 -
		(5*CPair[i1, i2]*CPair[i3, m1]*CPair[i4, i5]*CPair[m2, m5]*CPair[m3, m4])/42 +
		(CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m1]*CPair[m2, m5]*CPair[m3, m4])/42 +
		(CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m1]*CPair[m2, m5]*CPair[m3, m4])/42 -
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m1]*CPair[m2, m5]*CPair[m3, m4])/42 -
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m1]*CPair[m2, m5]*CPair[m3, m4])/42 -
		(2*CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m1]*CPair[m2, m5]*CPair[m3, m4])/21 +
		(2*CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m1]*CPair[m2, m5]*CPair[m3, m4])/21 -
		(23*CPair[i1, m4]*CPair[i2, m2]*CPair[i3, m1]*CPair[i4, i5]*CPair[m3, m5])/126 +
		(4*CPair[i1, m2]*CPair[i2, m4]*CPair[i3, m1]*CPair[i4, i5]*CPair[m3, m5])/63 +
		(23*CPair[i1, m4]*CPair[i2, m1]*CPair[i3, m2]*CPair[i4, i5]*CPair[m3, m5])/126 -
		(4*CPair[i1, m1]*CPair[i2, m4]*CPair[i3, m2]*CPair[i4, i5]*CPair[m3, m5])/63 +
		(31*CPair[i1, m2]*CPair[i2, m1]*CPair[i3, m4]*CPair[i4, i5]*CPair[m3, m5])/126 -
		(31*CPair[i1, m1]*CPair[i2, m2]*CPair[i3, m4]*CPair[i4, i5]*CPair[m3, m5])/126 +
		(61*CPair[i1, m4]*CPair[i2, m2]*CPair[i3, i5]*CPair[i4, m1]*CPair[m3, m5])/252 -
		(61*CPair[i1, m2]*CPair[i2, m4]*CPair[i3, i5]*CPair[i4, m1]*CPair[m3, m5])/252 -
		(13*CPair[i1, m4]*CPair[i2, i5]*CPair[i3, m2]*CPair[i4, m1]*CPair[m3, m5])/63 +
		(11*CPair[i1, i5]*CPair[i2, m4]*CPair[i3, m2]*CPair[i4, m1]*CPair[m3, m5])/126 +
		(CPair[i1, m2]*CPair[i2, i5]*CPair[i3, m4]*CPair[i4, m1]*CPair[m3, m5])/36 -
		(11*CPair[i1, i5]*CPair[i2, m2]*CPair[i3, m4]*CPair[i4, m1]*CPair[m3, m5])/126 -
		(61*CPair[i1, m4]*CPair[i2, m1]*CPair[i3, i5]*CPair[i4, m2]*CPair[m3, m5])/252 +
		(61*CPair[i1, m1]*CPair[i2, m4]*CPair[i3, i5]*CPair[i4, m2]*CPair[m3, m5])/252 +
		(13*CPair[i1, m4]*CPair[i2, i5]*CPair[i3, m1]*CPair[i4, m2]*CPair[m3, m5])/63 -
		(11*CPair[i1, i5]*CPair[i2, m4]*CPair[i3, m1]*CPair[i4, m2]*CPair[m3, m5])/126 -
		(CPair[i1, m1]*CPair[i2, i5]*CPair[i3, m4]*CPair[i4, m2]*CPair[m3, m5])/36 +
		(11*CPair[i1, i5]*CPair[i2, m1]*CPair[i3, m4]*CPair[i4, m2]*CPair[m3, m5])/126 -
		(61*CPair[i1, m2]*CPair[i2, m1]*CPair[i3, i5]*CPair[i4, m4]*CPair[m3, m5])/126 +
		(61*CPair[i1, m1]*CPair[i2, m2]*CPair[i3, i5]*CPair[i4, m4]*CPair[m3, m5])/126 +
		(59*CPair[i1, m2]*CPair[i2, i5]*CPair[i3, m1]*CPair[i4, m4]*CPair[m3, m5])/252 -
		(11*CPair[i1, i5]*CPair[i2, m2]*CPair[i3, m1]*CPair[i4, m4]*CPair[m3, m5])/63 -
		(59*CPair[i1, m1]*CPair[i2, i5]*CPair[i3, m2]*CPair[i4, m4]*CPair[m3, m5])/252 +
		(11*CPair[i1, i5]*CPair[i2, m1]*CPair[i3, m2]*CPair[i4, m4]*CPair[m3, m5])/63 +
		(CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m2]*CPair[i5, m1]*CPair[m3, m5])/28 -
		(13*CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m2]*CPair[i5, m1]*CPair[m3, m5])/84 -
		(3*CPair[i1, m2]*CPair[i2, i4]*CPair[i3, m4]*CPair[i5, m1]*CPair[m3, m5])/14 +
		(13*CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m4]*CPair[i5, m1]*CPair[m3, m5])/84 +
		(3*CPair[i1, m2]*CPair[i2, i3]*CPair[i4, m4]*CPair[i5, m1]*CPair[m3, m5])/14 -
		(CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m4]*CPair[i5, m1]*CPair[m3, m5])/4 +
		(CPair[i1, i2]*CPair[i3, m2]*CPair[i4, m4]*CPair[i5, m1]*CPair[m3, m5])/14 -
		(CPair[i1, m4]*CPair[i2, i4]*CPair[i3, m1]*CPair[i5, m2]*CPair[m3, m5])/28 +
		(13*CPair[i1, i4]*CPair[i2, m4]*CPair[i3, m1]*CPair[i5, m2]*CPair[m3, m5])/84 +
		(3*CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m4]*CPair[i5, m2]*CPair[m3, m5])/14 -
		(13*CPair[i1, i4]*CPair[i2, m1]*CPair[i3, m4]*CPair[i5, m2]*CPair[m3, m5])/84 -
		(3*CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m4]*CPair[i5, m2]*CPair[m3, m5])/14 +
		(CPair[i1, i3]*CPair[i2, m1]*CPair[i4, m4]*CPair[i5, m2]*CPair[m3, m5])/4 -
		(CPair[i1, i2]*CPair[i3, m1]*CPair[i4, m4]*CPair[i5, m2]*CPair[m3, m5])/14 -
		(CPair[i1, m2]*CPair[i2, i4]*CPair[i3, m1]*CPair[i5, m4]*CPair[m3, m5])/4 +
		(13*CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m1]*CPair[i5, m4]*CPair[m3, m5])/42 +
		(CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m2]*CPair[i5, m4]*CPair[m3, m5])/4 -
		(13*CPair[i1, i4]*CPair[i2, m1]*CPair[i3, m2]*CPair[i5, m4]*CPair[m3, m5])/42 +
		(3*CPair[i1, m2]*CPair[i2, i3]*CPair[i4, m1]*CPair[i5, m4]*CPair[m3, m5])/14 -
		(CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m1]*CPair[i5, m4]*CPair[m3, m5])/4 +
		(CPair[i1, i2]*CPair[i3, m2]*CPair[i4, m1]*CPair[i5, m4]*CPair[m3, m5])/14 -
		(3*CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m2]*CPair[i5, m4]*CPair[m3, m5])/14 +
		(CPair[i1, i3]*CPair[i2, m1]*CPair[i4, m2]*CPair[i5, m4]*CPair[m3, m5])/4 -
		(CPair[i1, i2]*CPair[i3, m1]*CPair[i4, m2]*CPair[i5, m4]*CPair[m3, m5])/14 -
		(CPair[i1, m4]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m2]*CPair[m3, m5])/42 -
		(CPair[i1, i5]*CPair[i2, m4]*CPair[i3, i4]*CPair[m1, m2]*CPair[m3, m5])/42 +
		(CPair[i1, m4]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m2]*CPair[m3, m5])/42 +
		(CPair[i1, i4]*CPair[i2, m4]*CPair[i3, i5]*CPair[m1, m2]*CPair[m3, m5])/6 +
		(CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m4]*CPair[m1, m2]*CPair[m3, m5])/42 -
		(5*CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m4]*CPair[m1, m2]*CPair[m3, m5])/21 -
		(CPair[i1, m4]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m2]*CPair[m3, m5])/42 -
		(CPair[i1, i3]*CPair[i2, m4]*CPair[i4, i5]*CPair[m1, m2]*CPair[m3, m5])/6 +
		(5*CPair[i1, i2]*CPair[i3, m4]*CPair[i4, i5]*CPair[m1, m2]*CPair[m3, m5])/21 +
		(11*CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m4]*CPair[m1, m2]*CPair[m3, m5])/42 -
		(11*CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m4]*CPair[m1, m2]*CPair[m3, m5])/42 +
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m4]*CPair[m1, m2]*CPair[m3, m5])/42 -
		(2*CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m4]*CPair[m1, m2]*CPair[m3, m5])/21 +
		(2*CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m4]*CPair[m1, m2]*CPair[m3, m5])/21 -
		(5*CPair[i1, m2]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m4]*CPair[m3, m5])/21 +
		(11*CPair[i1, i5]*CPair[i2, m2]*CPair[i3, i4]*CPair[m1, m4]*CPair[m3, m5])/42 +
		(43*CPair[i1, m2]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m4]*CPair[m3, m5])/42 -
		(25*CPair[i1, i4]*CPair[i2, m2]*CPair[i3, i5]*CPair[m1, m4]*CPair[m3, m5])/21 -
		(4*CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m2]*CPair[m1, m4]*CPair[m3, m5])/7 +
		(15*CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m2]*CPair[m1, m4]*CPair[m3, m5])/14 -
		(13*CPair[i1, m2]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m4]*CPair[m3, m5])/21 +
		(13*CPair[i1, i3]*CPair[i2, m2]*CPair[i4, i5]*CPair[m1, m4]*CPair[m3, m5])/14 -
		(8*CPair[i1, i2]*CPair[i3, m2]*CPair[i4, i5]*CPair[m1, m4]*CPair[m3, m5])/21 +
		(5*CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m2]*CPair[m1, m4]*CPair[m3, m5])/21 -
		(4*CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m2]*CPair[m1, m4]*CPair[m3, m5])/7 +
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m2]*CPair[m1, m4]*CPair[m3, m5])/6 +
		(5*CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m2]*CPair[m1, m4]*CPair[m3, m5])/42 -
		(2*CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m2]*CPair[m1, m4]*CPair[m3, m5])/7 +
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m2]*CPair[m1, m4]*CPair[m3, m5])/21 +
		(11*CPair[i1, m1]*CPair[i2, i5]*CPair[i3, i4]*CPair[m2, m4]*CPair[m3, m5])/42 -
		(5*CPair[i1, i5]*CPair[i2, m1]*CPair[i3, i4]*CPair[m2, m4]*CPair[m3, m5])/21 -
		(25*CPair[i1, m1]*CPair[i2, i4]*CPair[i3, i5]*CPair[m2, m4]*CPair[m3, m5])/21 +
		(43*CPair[i1, i4]*CPair[i2, m1]*CPair[i3, i5]*CPair[m2, m4]*CPair[m3, m5])/42 +
		(25*CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m1]*CPair[m2, m4]*CPair[m3, m5])/42 -
		(17*CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m1]*CPair[m2, m4]*CPair[m3, m5])/21 +
		(31*CPair[i1, m1]*CPair[i2, i3]*CPair[i4, i5]*CPair[m2, m4]*CPair[m3, m5])/42 -
		(17*CPair[i1, i3]*CPair[i2, m1]*CPair[i4, i5]*CPair[m2, m4]*CPair[m3, m5])/21 +
		(CPair[i1, i2]*CPair[i3, m1]*CPair[i4, i5]*CPair[m2, m4]*CPair[m3, m5])/7 -
		(5*CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m1]*CPair[m2, m4]*CPair[m3, m5])/21 +
		(CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m1]*CPair[m2, m4]*CPair[m3, m5])/3 +
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m1]*CPair[m2, m4]*CPair[m3, m5])/42 -
		(4*CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m1]*CPair[m2, m4]*CPair[m3, m5])/21 +
		(19*CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m1]*CPair[m2, m4]*CPair[m3, m5])/42 -
		(2*CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m1]*CPair[m2, m4]*CPair[m3, m5])/21 +
		(10*CPair[i1, m3]*CPair[i2, m2]*CPair[i3, m1]*CPair[i4, i5]*CPair[m4, m5])/63 -
		(16*CPair[i1, m2]*CPair[i2, m3]*CPair[i3, m1]*CPair[i4, i5]*CPair[m4, m5])/63 -
		(16*CPair[i1, m3]*CPair[i2, m1]*CPair[i3, m2]*CPair[i4, i5]*CPair[m4, m5])/63 -
		(5*CPair[i1, m1]*CPair[i2, m3]*CPair[i3, m2]*CPair[i4, i5]*CPair[m4, m5])/63 -
		(5*CPair[i1, m2]*CPair[i2, m1]*CPair[i3, m3]*CPair[i4, i5]*CPair[m4, m5])/63 +
		(32*CPair[i1, m1]*CPair[i2, m2]*CPair[i3, m3]*CPair[i4, i5]*CPair[m4, m5])/63 -
		(23*CPair[i1, m3]*CPair[i2, m2]*CPair[i3, i5]*CPair[i4, m1]*CPair[m4, m5])/126 +
		(23*CPair[i1, m2]*CPair[i2, m3]*CPair[i3, i5]*CPair[i4, m1]*CPair[m4, m5])/126 +
		(23*CPair[i1, m3]*CPair[i2, i5]*CPair[i3, m2]*CPair[i4, m1]*CPair[m4, m5])/126 +
		(2*CPair[i1, i5]*CPair[i2, m3]*CPair[i3, m2]*CPair[i4, m1]*CPair[m4, m5])/63 -
		(4*CPair[i1, m2]*CPair[i2, i5]*CPair[i3, m3]*CPair[i4, m1]*CPair[m4, m5])/63 -
		(2*CPair[i1, i5]*CPair[i2, m2]*CPair[i3, m3]*CPair[i4, m1]*CPair[m4, m5])/63 +
		(4*CPair[i1, m3]*CPair[i2, m1]*CPair[i3, i5]*CPair[i4, m2]*CPair[m4, m5])/63 -
		(4*CPair[i1, m1]*CPair[i2, m3]*CPair[i3, i5]*CPair[i4, m2]*CPair[m4, m5])/63 -
		(11*CPair[i1, m3]*CPair[i2, i5]*CPair[i3, m1]*CPair[i4, m2]*CPair[m4, m5])/126 +
		(4*CPair[i1, i5]*CPair[i2, m3]*CPair[i3, m1]*CPair[i4, m2]*CPair[m4, m5])/63 -
		(19*CPair[i1, m1]*CPair[i2, i5]*CPair[i3, m3]*CPair[i4, m2]*CPair[m4, m5])/126 -
		(4*CPair[i1, i5]*CPair[i2, m1]*CPair[i3, m3]*CPair[i4, m2]*CPair[m4, m5])/63 +
		(31*CPair[i1, m2]*CPair[i2, m1]*CPair[i3, i5]*CPair[i4, m3]*CPair[m4, m5])/126 -
		(31*CPair[i1, m1]*CPair[i2, m2]*CPair[i3, i5]*CPair[i4, m3]*CPair[m4, m5])/126 -
		(2*CPair[i1, m2]*CPair[i2, i5]*CPair[i3, m1]*CPair[i4, m3]*CPair[m4, m5])/63 +
		(2*CPair[i1, i5]*CPair[i2, m2]*CPair[i3, m1]*CPair[i4, m3]*CPair[m4, m5])/63 +
		(19*CPair[i1, m1]*CPair[i2, i5]*CPair[i3, m2]*CPair[i4, m3]*CPair[m4, m5])/126 -
		(2*CPair[i1, i5]*CPair[i2, m1]*CPair[i3, m2]*CPair[i4, m3]*CPair[m4, m5])/63 +
		(3*CPair[i1, i4]*CPair[i2, m3]*CPair[i3, m2]*CPair[i5, m1]*CPair[m4, m5])/14 +
		(5*CPair[i1, m2]*CPair[i2, i4]*CPair[i3, m3]*CPair[i5, m1]*CPair[m4, m5])/42 -
		(3*CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m3]*CPair[i5, m1]*CPair[m4, m5])/14 -
		(5*CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m2]*CPair[i5, m1]*CPair[m4, m5])/42 +
		(CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m2]*CPair[i5, m1]*CPair[m4, m5])/7 -
		(CPair[i1, m2]*CPair[i2, i3]*CPair[i4, m3]*CPair[i5, m1]*CPair[m4, m5])/7 +
		(5*CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m3]*CPair[i5, m1]*CPair[m4, m5])/21 -
		(CPair[i1, i2]*CPair[i3, m2]*CPair[i4, m3]*CPair[i5, m1]*CPair[m4, m5])/7 -
		(CPair[i1, m3]*CPair[i2, i4]*CPair[i3, m1]*CPair[i5, m2]*CPair[m4, m5])/42 -
		(3*CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m3]*CPair[i5, m2]*CPair[m4, m5])/14 -
		(5*CPair[i1, i3]*CPair[i2, m3]*CPair[i4, m1]*CPair[i5, m2]*CPair[m4, m5])/42 +
		(CPair[i1, i2]*CPair[i3, m3]*CPair[i4, m1]*CPair[i5, m2]*CPair[m4, m5])/7 +
		(CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m3]*CPair[i5, m2]*CPair[m4, m5])/7 -
		(5*CPair[i1, i3]*CPair[i2, m1]*CPair[i4, m3]*CPair[i5, m2]*CPair[m4, m5])/42 +
		(3*CPair[i1, m2]*CPair[i2, i4]*CPair[i3, m1]*CPair[i5, m3]*CPair[m4, m5])/14 -
		(3*CPair[i1, i4]*CPair[i2, m2]*CPair[i3, m1]*CPair[i5, m3]*CPair[m4, m5])/14 -
		(2*CPair[i1, m1]*CPair[i2, i4]*CPair[i3, m2]*CPair[i5, m3]*CPair[m4, m5])/21 +
		(3*CPair[i1, i4]*CPair[i2, m1]*CPair[i3, m2]*CPair[i5, m3]*CPair[m4, m5])/14 -
		(CPair[i1, m2]*CPair[i2, i3]*CPair[i4, m1]*CPair[i5, m3]*CPair[m4, m5])/7 +
		(5*CPair[i1, i3]*CPair[i2, m2]*CPair[i4, m1]*CPair[i5, m3]*CPair[m4, m5])/21 -
		(CPair[i1, i2]*CPair[i3, m2]*CPair[i4, m1]*CPair[i5, m3]*CPair[m4, m5])/7 +
		(CPair[i1, m1]*CPair[i2, i3]*CPair[i4, m2]*CPair[i5, m3]*CPair[m4, m5])/7 -
		(5*CPair[i1, i3]*CPair[i2, m1]*CPair[i4, m2]*CPair[i5, m3]*CPair[m4, m5])/42 -
		(5*CPair[i1, m3]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m2]*CPair[m4, m5])/42 -
		(5*CPair[i1, i5]*CPair[i2, m3]*CPair[i3, i4]*CPair[m1, m2]*CPair[m4, m5])/42 +
		(CPair[i1, m3]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m2]*CPair[m4, m5])/7 -
		(8*CPair[i1, i4]*CPair[i2, m3]*CPair[i3, i5]*CPair[m1, m2]*CPair[m4, m5])/21 +
		(5*CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m3]*CPair[m1, m2]*CPair[m4, m5])/21 +
		(CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m3]*CPair[m1, m2]*CPair[m4, m5])/2 +
		(2*CPair[i1, m3]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m2]*CPair[m4, m5])/21 +
		(13*CPair[i1, i3]*CPair[i2, m3]*CPair[i4, i5]*CPair[m1, m2]*CPair[m4, m5])/21 -
		(5*CPair[i1, i2]*CPair[i3, m3]*CPair[i4, i5]*CPair[m1, m2]*CPair[m4, m5])/6 -
		(CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m3]*CPair[m1, m2]*CPair[m4, m5])/42 -
		(2*CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m3]*CPair[m1, m2]*CPair[m4, m5])/7 +
		(5*CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m3]*CPair[m1, m2]*CPair[m4, m5])/21 -
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m3]*CPair[m1, m2]*CPair[m4, m5])/42 -
		(2*CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m3]*CPair[m1, m2]*CPair[m4, m5])/7 +
		(5*CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m3]*CPair[m1, m2]*CPair[m4, m5])/21 +
		(5*CPair[i1, m2]*CPair[i2, i5]*CPair[i3, i4]*CPair[m1, m3]*CPair[m4, m5])/42 -
		(17*CPair[i1, m2]*CPair[i2, i4]*CPair[i3, i5]*CPair[m1, m3]*CPair[m4, m5])/21 +
		(13*CPair[i1, i4]*CPair[i2, m2]*CPair[i3, i5]*CPair[m1, m3]*CPair[m4, m5])/14 +
		(5*CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m2]*CPair[m1, m3]*CPair[m4, m5])/42 -
		(17*CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m2]*CPair[m1, m3]*CPair[m4, m5])/21 +
		(13*CPair[i1, m2]*CPair[i2, i3]*CPair[i4, i5]*CPair[m1, m3]*CPair[m4, m5])/21 -
		(17*CPair[i1, i3]*CPair[i2, m2]*CPair[i4, i5]*CPair[m1, m3]*CPair[m4, m5])/14 +
		(13*CPair[i1, i2]*CPair[i3, m2]*CPair[i4, i5]*CPair[m1, m3]*CPair[m4, m5])/21 -
		(CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m2]*CPair[m1, m3]*CPair[m4, m5])/6 +
		(23*CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m2]*CPair[m1, m3]*CPair[m4, m5])/42 -
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m2]*CPair[m1, m3]*CPair[m4, m5])/6 -
		(CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m2]*CPair[m1, m3]*CPair[m4, m5])/6 +
		(23*CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m2]*CPair[m1, m3]*CPair[m4, m5])/42 -
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m2]*CPair[m1, m3]*CPair[m4, m5])/6 +
		(5*CPair[i1, i5]*CPair[i2, m1]*CPair[i3, i4]*CPair[m2, m3]*CPair[m4, m5])/42 +
		(31*CPair[i1, m1]*CPair[i2, i4]*CPair[i3, i5]*CPair[m2, m3]*CPair[m4, m5])/42 -
		(13*CPair[i1, i4]*CPair[i2, m1]*CPair[i3, i5]*CPair[m2, m3]*CPair[m4, m5])/21 -
		(5*CPair[i1, i5]*CPair[i2, i4]*CPair[i3, m1]*CPair[m2, m3]*CPair[m4, m5])/14 +
		(8*CPair[i1, i4]*CPair[i2, i5]*CPair[i3, m1]*CPair[m2, m3]*CPair[m4, m5])/21 -
		(5*CPair[i1, m1]*CPair[i2, i3]*CPair[i4, i5]*CPair[m2, m3]*CPair[m4, m5])/6 +
		(13*CPair[i1, i3]*CPair[i2, m1]*CPair[i4, i5]*CPair[m2, m3]*CPair[m4, m5])/21 +
		(2*CPair[i1, i2]*CPair[i3, m1]*CPair[i4, i5]*CPair[m2, m3]*CPair[m4, m5])/21 +
		(5*CPair[i1, i5]*CPair[i2, i3]*CPair[i4, m1]*CPair[m2, m3]*CPair[m4, m5])/21 -
		(2*CPair[i1, i3]*CPair[i2, i5]*CPair[i4, m1]*CPair[m2, m3]*CPair[m4, m5])/7 -
		(CPair[i1, i2]*CPair[i3, i5]*CPair[i4, m1]*CPair[m2, m3]*CPair[m4, m5])/42 +
		(5*CPair[i1, i4]*CPair[i2, i3]*CPair[i5, m1]*CPair[m2, m3]*CPair[m4, m5])/21 -
		(2*CPair[i1, i3]*CPair[i2, i4]*CPair[i5, m1]*CPair[m2, m3]*CPair[m4, m5])/7 -
		(CPair[i1, i2]*CPair[i3, i4]*CPair[i5, m1]*CPair[m2, m3]*CPair[m4, m5])/42
};


FCPrint[1,"FMCartesianTensorDecomposition loaded."];
End[]
