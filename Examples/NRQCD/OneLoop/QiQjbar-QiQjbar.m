(* ::Package:: *)

(* :Title: QiQjbar-QiQjbar															*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2014-2020 Vladyslav Shtabovenko
*)

(* :Summary:  Qi Qjbar -> Qi Qjbar, NRQCD, matching, 1-loop			*)

(* ------------------------------------------------------------------------ *)


(* ::Title:: *)
(*Matching coefficients for dimension six NRQCD 4-fermion operators in the unequal mass case*)


(* ::Section:: *)
(*Load FeynCalc and the necessary add-ons or other packages*)


description="Qi Qjbar -> Qi Qjbar, NRQCD, matching, 1-loop";
If[ $FrontEnd === Null,
	$FeynCalcStartupMessages = False;
	Print[description];
];
If[ $Notebooks === False,
	$FeynCalcStartupMessages = False
];
$LoadAddOns={"FeynArts", "FeynOnium","FeynHelpers"};
<<FeynCalc`
$FAVerbose = 0;

FCCheckVersion[9,4,0];


(* ::Section:: *)
(*Generate Feynman diagrams*)


(* ::Text:: *)
(*Nicer typesetting*)


MapThread[FCAttachTypesettingRule[#1,{SubscriptBox,"p",#2}]&,
{{p1,p2,p3,p4},Range[4]}];


MapThread[FCAttachTypesettingRule[#1,{SubscriptBox,"m",#2}]&,
{{m1,m2},Range[2]}];


FCAttachTypesettingRule[ST1,{SubscriptBox,"S","T,1"}]
FCAttachTypesettingRule[ST2,{SubscriptBox,"S","T,2"}]


FCAttachTypesettingRule[mc["d_ss"],{SubscriptBox,"d","ss"}]
FCAttachTypesettingRule[mc["d_sv"],{SubscriptBox,"d","sv"}]
FCAttachTypesettingRule[mc["d_vs"],{SubscriptBox,"d","vs"}]
FCAttachTypesettingRule[mc["d_vv"],{SubscriptBox,"d","vv"}]


diags = InsertFields[CreateTopologies[1, 2 -> 2,BoxesOnly], 
{F[3, {1,Col1}],-F[3, {2,Col2}]} -> {F[3, {1,Col3}],
-F[3, {2,Col4}]}, InsertionLevel -> {Classes}, Model -> "SMQCD",
ExcludeParticles -> {S[_], V[1|2|3|4]}];
Paint[diags, ColumnsXRows -> {2, 1}, Numbering -> None,
SheetHeader->None,ImageSize->{512,256}];


(* ::Section:: *)
(*Obtain the amplitude*)


amp[0] = FCFAConvert[CreateFeynAmp[diags,PreFactor->-1],
IncomingMomenta->{p1,p2},OutgoingMomenta->{p3,p4},
LoopMomenta->{l},DropSumOver->True,ChangeDimension->D,
UndoChiralSplittings->True,List->False,SMP->True,
FinalSubstitutions->{SMP["m_u"]->m1,SMP["m_c"]->m2},Contract->True]


(* ::Text:: *)
(*Define rules for applying Fierz identities to color matrices*)


ruleColor={SUNTF[{SUNIndex[a_],SUNIndex[b_]},
i1_SUNFIndex,i2_SUNFIndex] SUNTF[{SUNIndex[a_],SUNIndex[b_]},
i3_SUNFIndex,i4_SUNFIndex]:>
CF hold[(CA/2-CF)]SUNFDelta[i1,i2]SUNFDelta[i3,i4]-
2hold[(CA/2-CF)] SUNTF[{SUNIndex[a]},i1,i2]SUNTF[{SUNIndex[a]},i3,i4],

SUNTF[{SUNIndex[a_],SUNIndex[b_]},
i1_SUNFIndex,i2_SUNFIndex] SUNTF[{SUNIndex[b_],SUNIndex[a_]},
i3_SUNFIndex,i4_SUNFIndex]:>
CF hold[(CA/2-CF)]SUNFDelta[i1,i2]SUNFDelta[i3,i4]+
(CF-hold[(CA/2-CF)]) SUNTF[{SUNIndex[a]},i1,i2]SUNTF[{SUNIndex[a]},i3,i4]};


(* ::Section:: *)
(*Fix the kinematics*)


(* ::Text:: *)
(*All particles are on-shell*)


FCClearScalarProducts[];
SPD[p1,p1]=m1^2;
SPD[p2,p2]=m2^2;
SPD[p3,p3]=m1^2;
SPD[p4,p4]=m2^2;
SPD[p1,p2]=m1 m2;
SPD[p3,p4]=m1 m2;
SPD[p1,p3]=m1^2;
SPD[p2,p4]=m2^2;
SPD[p1,p4]=m1 m2;
SPD[p2,p3]=m1 m2;


(* ::Text:: *)
(*and at rest*)


TC[p1]= m1;
TC[p2]= m2;
TC[p3]= m1;
TC[p4]= m2;
CartesianMomentum[p1,D-1]=0;
CartesianMomentum[p2,D-1]=0;
CartesianMomentum[p3,D-1]=0;
CartesianMomentum[p4,D-1]=0;
CartesianMomentum[p1]=0;
CartesianMomentum[p2]=0;
CartesianMomentum[p3]=0;
CartesianMomentum[p4]=0;


(* ::Section:: *)
(*Evaluate the amplitude*)


(* ::Text:: *)
(*Use "naive" scheme for Pauli matrices in D-1 dimensions, i.e. the *)
(*anticommutator relation is applied with a D-1 dimensional epsilon tensor*)


FCSetPauliSigmaScheme["Naive"];


(* ::Text:: *)
(*Tensor reduction of the 1-loop integrals and simplification of the Dirac*)
(*and color algebra*)


amp[1]=amp[0]//SUNSimplify//TID[#,l,UsePaVeBasis->True,ToPaVe->True,
Isolate->False]&//DiracSimplify;


(* ::Text:: *)
(*Nonrelativistic expansion of spinor chains and subsequent simplification of the Pauli*)
(*algebra. Here we explicitly allows PauliSimplify to reduce all chains of Pauli matrices to*)
(*at most one matrix via 3-dimensional relations*)


amp[2]=FMSpinorChainExplicit2[amp[1],
	FMSpinorNormalization->"nonrelativistic"]//Contract//
	PauliSimplify[#,PauliReduce->True]&//Contract[#,EpsContract->False]&//
	ExpandScalarProduct;


(* ::Text:: *)
(*For convenience, we substitute the remaining Pauli structures with a single matrix by*)
(*suitable Cartesian vectors*)


amp[3]=amp[2]//ReplaceAll[#,{PauliEta[-I].PauliSigma[x_,D-1].PauliEta[I]:>
	CartesianPair[CartesianMomentum[ST1,D-1],x],
	PauliXi[-I].PauliSigma[x_,D-1].PauliXi[I]:>
	CartesianPair[CartesianMomentum[ST2,D-1],x]}]&//
	Contract[#,EpsContract->False]&//
	FCCanonicalizeDummyIndices[#,Head->{LorentzIndex,CartesianIndex}]&//
	Collect2[#,{ST1,ST2,Eps},IsolateNames->KK]&;


(* ::Text:: *)
(*This simulates the prescription of arXiv:hep-ph/9802365, i.e. eps^ijk  eps^ijk' = (D-2) d^kk'*)


amp[4]=amp[3]/.FCI[CLCD[a_,b_][p1_]CLCD[a_,b_][p2_]:>(D-2)CSPD[p1,p2]]


(* ::Text:: *)
(*Evaluation of the Passarino-Veltman functions*)


amp[5]=PaXEvaluateUVIRSplit[amp[4]//FRH,
PaXAnalytic->True,PaXImplicitPrefactor->1/(2Pi)^D]//
	FCHideEpsilon;


(* ::Text:: *)
(*Expansion around ep=0 for D=4-2*ep*)


amp[6]=amp[5]//FCReplaceD[#,D->4-2EpsilonIR]&//DotSimplify//
	FCShowEpsilon//Series[#,{EpsilonIR,0,0}]&//Normal//FCHideEpsilon;


(* ::Text:: *)
(*Extract the finite part and separate color singlet and color octet contributions from each other*)


{ampFin[0],ampDiv[0]}=FCSplit[amp[6],{SMP["Delta_IR"]}];
ampFin[1]=(ampFin[0]/.D->4)//Expand2[#,SUNTF]&//ReplaceAll[#,ruleColor]&;


(* ::Text:: *)
(*Final splitting into spin singlet, spin triplet, color singlet and color octet pieces*)


{spinSingletFin,spinTripletFin}=FCSplit[ampFin[1],{ST1,ST2}];


{spinSingletColorSingletFin,spinSingletColorOctetFin}=
FullSimplify/@(FCSplit[spinSingletFin,{SUNTF}]);


{spinTripletColorSingletFin,spinTripletColorOctetFin}=
FullSimplify/@(FCSplit[spinTripletFin,{SUNTF}]);


(* ::Section:: *)
(*Final matching coefficients*)


getMatchingCoeff[ex_,ru_]:=
(m1 m2 I ex//PowerExpand//Simplify//ReplaceAll[#,ru]&//
ReplaceAll[#,{SMP["g_s"]^4->16Pi^2 SMP["alpha_s"]^2,
FCI[CSP[ST1,ST2]]:>1,DOT[x_,y_]:>1,
SUNFDelta[__]:>1,SUNTF[__]:>1}]&//Simplify)/.hold->Identity


rulesMC={
mc["d_ss"]->getMatchingCoeff[spinSingletColorSingletFin,
{Log[m1]->1/2Log[(m1/ScaleMu)^2]+
Log[ScaleMu],Log[m2]->1/2Log[(m2/ScaleMu)^2]+Log[ScaleMu]}],

mc["d_sv"]->getMatchingCoeff[spinTripletColorSingletFin,
{Log[m1]->1/2Log[(m1/m2)^2]+Log[m2]}],

mc["d_vs"]->getMatchingCoeff[spinSingletColorOctetFin,
{Log[m1]->1/2Log[(m1/ScaleMu)^2]+Log[ScaleMu],
Log[m2]->1/2Log[(m2/ScaleMu)^2]+Log[ScaleMu]}]//Collect2[#,CA,CF]&,

mc["d_vv"]->getMatchingCoeff[spinTripletColorOctetFin,
{Log[m1]->1/2Log[(m1/ScaleMu)^2]+
Log[ScaleMu],Log[m2]->1/2Log[(m2/ScaleMu)^2]+Log[ScaleMu]}]//
Collect2[#,CA,CF]&
}


(* ::Section:: *)
(*Check the final results*)


knownResult = {
- CF(CA/2-CF) SMP["alpha_s"]^2/
(m1^2-m2^2)(m1^2(Log[m2^2/ScaleMu^2]+1/3)-m2^2(Log[m1^2/ScaleMu^2]+1/3)),
CF(CA/2-CF) SMP["alpha_s"]^2/
(m1^2-m2^2)m1 m2 Log[m1^2/m2^2],
-2CF SMP["alpha_s"]^2/
(m1^2-m2^2)(m1^2(Log[m2^2/ScaleMu^2]+1/3)-m2^2(Log[m1^2/ScaleMu^2]+
1/3))+CA SMP["alpha_s"]^2/(4(m1^2-m2^2))(
3(m1^2(Log[m2^2/ScaleMu^2]+1/3)-m2^2(Log[m1^2/ScaleMu^2]+1/3))
+1/(m1 m2) (m1^4(Log[m2^2/ScaleMu^2]+10/3)-
m2^4(Log[m1^2/ScaleMu^2]+10/3))),
2CF SMP["alpha_s"]^2/
(m1^2-m2^2) m1 m2 Log[m1^2/m2^2]+CA SMP["alpha_s"]^2/
(4(m1^2-m2^2))((m1^2(Log[m2^2/ScaleMu^2]+3)-
m2^2(Log[m1^2/ScaleMu^2]+3))-3 m1 m2 Log[m1^2/m2^2])
};
FCCompareResults[PowerExpand[({mc["d_ss"],mc["d_sv"],
mc["d_vs"],mc["d_vv"]}/.rulesMC)],PowerExpand[knownResult],
Text->{"\tCompare to Eqs. 3.1-3.4 in arXiv:hep-ph/9802365:",
"CORRECT.","WRONG!"}, Interrupt->{Hold[Quit[1]],Automatic}];
Print["\tCPU Time used: ", Round[N[TimeUsed[],4],0.001], " s."];



