(* ::Package:: *)

(* :Title: ElEl-ElEl-CoulombPotential														*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2014-2021 Vladyslav Shtabovenko
*)

(* :Summary:  El El -> El El, QED, Coulomb potential, tree			*)

(* ------------------------------------------------------------------------ *)



(* ::Title:: *)
(*Coulomb potential from QED*)


(* ::Section:: *)
(*Load FeynCalc and the necessary add-ons or other packages*)


description="El El -> El El, QED, Coulomb potential, tree";
If[ $FrontEnd === Null,
	$FeynCalcStartupMessages = False;
	Print[description];
];
If[ $Notebooks === False,
	$FeynCalcStartupMessages = False
];
$LoadAddOns={"FeynArts","FeynOnium"};
<<FeynCalc`
$FAVerbose = 0;

FCCheckVersion[9,3,1];


(* ::Section:: *)
(*Generate Feynman diagrams*)


(* ::Text:: *)
(*Nicer typesetting*)


MakeBoxes[p1,TraditionalForm]:="\!\(\*SubscriptBox[\(p\), \(1\)]\)";
MakeBoxes[p2,TraditionalForm]:="\!\(\*SubscriptBox[\(p\), \(2\)]\)";
MakeBoxes[k1,TraditionalForm]:="\!\(\*SubscriptBox[\(k\), \(1\)]\)";
MakeBoxes[k2,TraditionalForm]:="\!\(\*SubscriptBox[\(k\), \(2\)]\)";


diags = InsertFields[CreateTopologies[0, 2 -> 2], {F[2, {1}], F[2, {1}]} ->
		{F[ 2, {1}], F[2, {1}]}, InsertionLevel -> {Classes},
		Restrictions->QEDOnly];

Paint[DiagramExtract[diags,1], ColumnsXRows -> {2, 1}, Numbering -> Simple,
	SheetHeader->None,ImageSize->{512,256}];


(* ::Section:: *)
(*Obtain the amplitude*)


amp[0] = FCFAConvert[CreateFeynAmp[DiagramExtract[diags,1],PreFactor->-1], IncomingMomenta->{p1,k1},
	OutgoingMomenta->{p2,k2},UndoChiralSplittings->True,ChangeDimension->4,
	List->False, SMP->True, Contract->True]


(* ::Section:: *)
(*Fix the kinematics*)


FCClearScalarProducts[];
me=SMP["m_e"];
(*4-momentum scalar products*)
SP[k1,k1]=me^2;
SP[k2,k2]=me^2;
SP[p1,p1]=me^2;
SP[p2,p2]=me^2;
(*temporal components of 4-momenta*)
TC[k1]=FCI[Sqrt[me^2+CSP[k1,k1]]];
TC[k2]=FCI[Sqrt[me^2+CSP[k2,k2]]];
TC[p1]=FCI[Sqrt[me^2+CSP[p1,p1]]];
TC[p2]=FCI[Sqrt[me^2+CSP[p2,p2]]];
(*rest frame kinematics of the 3-momenta,
the auxiliary variable sc will be used as 
the expansion parameter*)
CartesianMomentum[p1]=sc CartesianMomentum[q1];
CartesianMomentum[k1]=- sc CartesianMomentum[q1];
CartesianMomentum[p2]= sc CartesianMomentum[q2];
CartesianMomentum[k2]=-sc CartesianMomentum[q2];


(*trick to speed up the expansions*)
Unprotect[Power];
Power[me^2,1/2]:=me;
Protect[Power];


(* ::Section:: *)
(*Expand the amplitude*)


amp[1]=amp[0]//FMSpinorChainExplicit2//Contract//DotSimplify//FeynAmpDenominatorExplicit//LorentzToCartesian;


(* ::Text:: *)
(*sc is just a bookkeeping variable for doing nonrelativistic expansions. At the very end*)
(*of the calculation we can always set it to unity.*)


amp[2]=amp[1]//Series[#,{sc,0,-1}]&//Normal


(* ::Text:: *)
(*This way we obtain the leading order contribution to the repulsive Coulomb potential in the momentum space*)


amp[2]/.sc->1


(* ::Section:: *)
(*Check the final results*)


knownResult = ((-I)*(2 SMP["e"] SMP["m_e"] PauliXi[-I].PauliXi[I])^2)/(CSP[p1-p2]) /. sc->1;
FCCompareResults[amp[2],knownResult,
Text->{"\tCompare to Peskin and Schroeder, An Introduction to QFT, \
Eq 4.134:", "CORRECT.","WRONG!"}, Interrupt->{Hold[Quit[1]],Automatic}];
Print["\tCPU Time used: ", Round[N[TimeUsed[],4],0.001], " s."];



