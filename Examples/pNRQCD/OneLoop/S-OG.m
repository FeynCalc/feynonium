(* ::Package:: *)

(* :Title: S-OG															*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2014-2020 Vladyslav Shtabovenko
*)

(* :Summary:  S -> OG, pNRQCD, logs, 1-loop					*)

(* ------------------------------------------------------------------------ *)



(* ::Title:: *)
(*Running of VA and VB*)


(* ::Section:: *)
(*Load FeynCalc and the necessary add-ons or other packages*)


description="S -> OG, pNRQCD, logs, 1-loop";
If[ $FrontEnd === Null,
	$FeynCalcStartupMessages = False;
	Print[description];
];
If[ $Notebooks === False,
	$FeynCalcStartupMessages = False
];
$LoadAddOns={"FeynOnium"};
<<FeynCalc`

FCCheckVersion[9,3,1];


(* ::Section:: *)
(*Fix the kinematics*)


FCClearScalarProducts[];
TC[l]=E0;


(* ::Section:: *)
(*Enter the amplitudes*)


(* ::Text:: *)
(*The 1/(2Pi)^D prefactor is implicit.*)


(* ::Text:: *)
(*We enter the amplitude for the 1-loop correction to the S -> O g vertex that contributes to the running of V_A. This corresponds to the diagrams in Fig. 7 b) of hep-ph/9907240*)


ampVA[0] = ((
FMOctetGluonSingletVertex[{"V_A",r},a,{-k,i,c}].FMOctetPropagator[{l-k,
V0,n},{a,cp}].FMOctetGluonOctetVertex[{"1"},ap,{-(p-k),0,bp},
cp]FMCoulombGaugeGluonPropagator[k,{i,c},{j,e}]
FMCoulombGaugeGluonPropagator[p-k,{0,bp},{0,g}]
GluonVertex[{k,CartesianIndex[j,D-1],e},{p-k,0,g},{-p,0,f}]
) + (
FMOctetGluonGluonSingletVertex[{"V_A",r},ap,{-k,i,c},{-(p-k),0,b}]
FMCoulombGaugeGluonPropagator[k,{i,c},{j,e}]
FMCoulombGaugeGluonPropagator[p-k,{0,b},{0,g}]
GluonVertex[{k,CartesianIndex[j,D-1],e},{p-k,0,g},{-p,0,f}]
))//Explicit


(* ::Text:: *)
(*We also need the amplitude for the 1-loop correction to the O -> O g vertex that contributes to the running of V_B. This corresponds to the diagrams in Fig. 8 b) of hep-ph/9907240*)


ampVB[0] = (2( 
FMOctetGluonOctetVertex[{"V_B",r},a,{-k,i,c},u].FMOctetPropagator[{l-k,V0,n},{a,cp}].
FMOctetGluonOctetVertex[{"1"},ap,{-(p-k),0,bp},cp]
FMCoulombGaugeGluonPropagator[k,{i,c},{j,e}]
FMCoulombGaugeGluonPropagator[p-k,{0,bp},{0,g}]
GluonVertex[{k,CartesianIndex[j,D-1],e},{p-k,0,g},{-p,0,f}]
) + (
FMOctetGluonGluonOctetVertex[{"V_B",r},ap,{-k,i,c},{-(p-k),0,b},u]
FMCoulombGaugeGluonPropagator[k,{i,c},{j,e}]
FMCoulombGaugeGluonPropagator[p-k,{0,b},{0,g}]
GluonVertex[{k,CartesianIndex[j,D-1],e},{p-k,0,g},{-p,0,f}]
))//Explicit


(* ::Text:: *)
(*Let us consider the sum of the two amplitudes*)


amp[0]=ampVA[0]+ampVB[0];


(* ::Section:: *)
(*Calculate the amplitudes*)


(* ::Text:: *)
(*|n><n| is not relevant here, so set it to unity*)


amp[1]=amp[0]/. FMKet[n].FMBra[n]->1;


amp[2]=amp[1]//DotSimplify//SUNSimplify[#,SUNNToCACF->False,Explicit->True]&//
	ReplaceAll[#,SUNTrace[x__]:>SUNTrace[x,Explicit->True]]&//Factor//
MomentumExpand//ExpandScalarProduct//ReplaceAll[#,E0-V0->DE]&


(* ::Text:: *)
(*The occurring loop integrals have following numerators*)


FCLoopExtract[amp[2],{k},loop,Numerator->False]//Last


{ampFree,ampInt,intList}=
	FCLoopExtract[amp[2],{k},loop]/.loop[x_]:>loop[FeynAmpDenominatorSplit[x]];


(* ::Text:: *)
(*We integrate over k^0 by closing the contour below and picking up the residue at k^0 = |k| - i eta*)


repRuleResidueInt=
	Thread[Rule[intList,intList/.{
	FCI[SFAD[{{k, 0}, {0, 1}, 1}]]->-2Pi*I*1/(2)*GFAD[Sqrt[CSPD[k]]]*
	1/(2Pi),FCI[TC[k]]->Sqrt[CSPD[k]]}/.loop->Identity]]


(* ::Text:: *)
(*After the residue integration we end up with purely Cartesian integral*)


amp[3]=ampFree+ampInt/.repRuleResidueInt//Simplify


(* ::Text:: *)
(*Simplify the integrals by doing tensor reduction and clever partial fractioning*)


amp[4]=amp[3]//FCMultiLoopTID[#,{k}]&;


amp[5]=ApartFF[amp[4] CFAD[k],CSPD[k],{k}]//ApartFF[#,{k}]&;


amp[6]=ApartFF[amp[5] GFAD[Sqrt[CSPD[k]]],Sqrt@CSPD[k],{k},FeynAmpDenominator->False]//
	ApartFF[#,{k}]&


(* ::Text:: *)
(*Build up a list of the occurring loop integrals. Calculate those integrals by hand, keeping only the log piece that*)
(*we are interested in.*)


{ampFree2,ampLoop2,loopInts2}=FCLoopExtract[amp[6],{k},loop];


ruleUVLogs={
loop[CFAD[k-p]]->0,
loop[CFAD[{{k-p,0},{0,-1},1}] Sqrt[CSPD[k,k]]]->(CSPD[p,p]*Log[mu/p])/(6*Pi^2),
loop[GFAD[{{DE-Sqrt[CSPD[k,k]],1},1}]]->-((DE)^2*Log[mu/(DE)])/(2*Pi^2),
loop[GFAD[{{Sqrt[CSPD[k,k]],1},1}]]->0(*scaleless*),
loop[CFAD[{{k,0},{0,-1},1}] GFAD[{{DE-Sqrt[CSPD[k,k]],1},1}]]->-  Log[mu/p]/(2*Pi^2),
loop[CFAD[{{k,0},{0,-1},1}] GFAD[{{Sqrt[CSPD[k,k]],1},1}]]->0(*scaleless*),
loop[CFAD[{{k-p,0},{0,-1},1}] GFAD[{{DE-Sqrt[CSPD[k,k]],1},1}]]->-  Log[mu/p]/(2*Pi^2),
loop[CFAD[{{k-p,0},{0,-1},1}] GFAD[{{Sqrt[CSPD[k,k]],1},1}]] ->(Log[mu/p])/(2*Pi^2),
loop[CFAD[{{k,0},{0,-1},1},{{k-p,0},{0,-1},1}] GFAD[{{DE-Sqrt[CSPD[k,k]],1},1}]]->0(*UV-finite*),
loop[CFAD[{{k,0},{0,-1},1},{{k-p,0},{0,-1},1}] GFAD[{{Sqrt[CSPD[k,k]],1},1}]]->0(*UV-finite*),
loop[CFAD[{{k,0},{0,-1},1}]*Sqrt[CSPD[k,k]]]->0,
loop[CFAD[{{k,0},{0,-1},1},{{k,0},{0,-1},1}]*Sqrt[CSPD[k,k]]]->0,
loop[CFAD[{{k,0},{0,-1},1},{{k-p,0},{0,-1},1}]*Sqrt[CSPD[k,k]]]->(Log[mu/p])/(2*Pi^2),
loop[CFAD[{{k,0},{0,-1},1},{{k,0},{0,-1},1},{{k-p,0},{0,-1},1}]*Sqrt[CSPD[k,k]]]->-Log[mu/p]/(2*Pi^2*CSPD[p,p])
}/.loop[x_]:>loop[FeynAmpDenominatorCombine[x]]


(* ::Text:: *)
(*Substituting the results we end up with*)


amp[7]=
	Collect2[FCI[ampFree2+ampLoop2/.ruleUVLogs],p,Factoring->Simplify]//
	SelectFree[#,FCI@CSPD[p]]&


ampLoVA=FMOctetGluonSingletVertex[{"V_A",r},ap,{-p,0,f}]//Explicit//ExpandScalarProduct
ampLoVB=FMOctetGluonOctetVertex[{"V_B",r},ap,{-p,0,f},u]//Explicit//ExpandScalarProduct


(* ::Text:: *)
(*Diving the 1-loop amplitude by the corresponding tree-level expressions we find the a_s corrections and hence the running*)


resRunningVB=(SelectNotFree2[amp[7],SMP["V_B"]]/ampLoVB)/.SMP["g_s"]^2->4Pi SMP["alpha_s"]


resRunningVA=SelectNotFree2[amp[7],SMP["V_A"]]/ampLoVA/.SMP["g_s"]^2->4Pi SMP["alpha_s"]


(* ::Text:: *)
(*In this case the a_s corrections obviously vanish at 1-loop*)


resFinalVA=(mu D[resRunningVA,mu])
resFinalVB=(mu D[resRunningVB,mu])


(* ::Section:: *)
(*Check the final results*)


knownResults = {0,0};
FCCompareResults[{resFinalVA,resFinalVB},knownResults,
Text->{"\tCompare to hep-ph/0007197, Eq. 11:",
"CORRECT.","WRONG!"}, Interrupt->{Hold[Quit[1]],Automatic}];
Print["\tCPU Time used: ", Round[N[TimeUsed[],4],0.001], " s."];



