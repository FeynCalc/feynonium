(* ::Package:: *)

(* :Title: NRQCD-QQbarPrimeToQQbarPrime-OneLoop.m                            *)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2017 Vladyslav Shtabovenko
*)

(* :Summary:   Computation of the 1-loop matching coefficients
				for the dimension 6 4-fermion operators of the
				NRQCD Lagrangian in the unequal mass case. *)

(* ------------------------------------------------------------------------ *)


(* ::Section:: *)
(*One-loop matching between QCD and NRQCD for QQbar' -> QQbar'*)


(* ::Subsection:: *)
(*Load FeynCalc, FeynArts and FeynHelpers*)


If[ $FrontEnd === Null,
		$FeynCalcStartupMessages = False;
		Print["Computation of the 1-loop matching coefficients \
for the dimension 6 4-fermion operators of the \
NRQCD Lagrangian in the unequal mass case."];
];
$LoadAddOns={"FeynHelpers","FeynOnium"};
$LoadFeynArts = True;
<<FeynCalc`
$FAVerbose=0;


(* ::Subsection:: *)
(*Generate Feynman diagrams*)


diags = InsertFields[CreateTopologies[1, 2 -> 2,BoxesOnly], {F[3, {1,Col1}], -F[3, {2,Col2}]} -> {F[3, {1,Col3}],
		-F[3, {2,Col4}]}, InsertionLevel -> {Classes}, Model -> "SMQCD",
		ExcludeParticles -> {S[_], V[1|2|3|4]}];
Paint[diags, ColumnsXRows -> {2, 1}, Numbering -> None,SheetHeader->None,ImageSize->{512,256}];


amp=FCFAConvert[CreateFeynAmp[diags,PreFactor->-1],IncomingMomenta->{p1,p2},OutgoingMomenta->{p3,p4},
LoopMomenta->{l},DropSumOver->True,ChangeDimension->D,UndoChiralSplittings->True,List->False,SMP->True,
FinalSubstitutions->{SMP["m_u"]->m1,SMP["m_c"]->m2}]//Contract


ruleColor={SUNTF[{SUNIndex[a_],SUNIndex[b_]},i1_SUNFIndex,i2_SUNFIndex] SUNTF[{SUNIndex[a_],SUNIndex[b_]},i3_SUNFIndex,i4_SUNFIndex]:>
CF hold[(CA/2-CF)]SUNFDelta[i1,i2]SUNFDelta[i3,i4]-2hold[(CA/2-CF)] SUNTF[{SUNIndex[a]},i1,i2]SUNTF[{SUNIndex[a]},i3,i4],

SUNTF[{SUNIndex[a_],SUNIndex[b_]},i1_SUNFIndex,i2_SUNFIndex] SUNTF[{SUNIndex[b_],SUNIndex[a_]},i3_SUNFIndex,i4_SUNFIndex]:>
CF hold[(CA/2-CF)]SUNFDelta[i1,i2]SUNFDelta[i3,i4]+(CF-hold[(CA/2-CF)]) SUNTF[{SUNIndex[a]},i1,i2]SUNTF[{SUNIndex[a]},i3,i4]};


(* ::Subsection:: *)
(*On-shell kinematics*)


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


(* ::Subsection:: *)
(*Calculation of the box amplitudes in QCD*)


(* ::Text:: *)
(*Tensor reduction of the 1-loop integrals and simplification of the Dirac algebra*)


AbsoluteTiming[amp1=TID[amp,l,UsePaVeBasis->True,ToPaVe->True,FCVerbose->0,Isolate->False]//DiracSimplify//DiracSimplify;]//First


(* ::Text:: *)
(*Using "naive" scheme for Pauli matrices in D-1 dimensions, i.e. the anticommutator relation is applied with a D-1 dimensional epsilon tensor*)


FCSetPauliSigmaScheme["Naive"];


(* ::Text:: *)
(*Nonrelativistic expansion of spinor chains*)


AbsoluteTiming[amp2=amp1//Collect2[#,DiracSpinor]&//FMSpinorChainExplicit2[#,FMSpinorNormalization->"nonrelativistic"]&//ReplaceAll[#,{PauliEta[-I].PauliSigma[x_,D-1].PauliEta[I]:>CartesianPair[CartesianMomentum[ST1,D-1],x],
PauliXi[-I].PauliSigma[x_,D-1].PauliXi[I]:>CartesianPair[CartesianMomentum[ST2,D-1],x]}]&//Contract//Collect2[#,{ST1,ST2}]&;]//First


(* ::Text:: *)
(*Evaluation of the Passarino-Veltman functions*)


AbsoluteTiming[amp3=amp2//Collect2[#,{PaVe,D0}]&//ReplaceAll[#,(x:_PaVe|_D0):>PaXEvaluateUVIRSplit[x,
PaXAnalytic->True,PaXImplicitPrefactor->1/( 2Pi)^D,FCVerbose->0]]&//FCHideEpsilon;]//First


(* ::Text:: *)
(*This simulates the prescription of arXiv:hep-ph/9802365, i.e. eps^ijk  eps^ijk' = (D-2) d^kk'*)


amp4=(amp3/.{FCI[CSPD[ST1,ST2]]->FCI[CSPD[ST1,ST2]]/(D-3)});


(* ::Text:: *)
(*Expanding around eps=0 for D=4-2eps*)


AbsoluteTiming[amp5=Series[amp4//FCReplaceD[#,D->4-2EpsilonIR]&//DotSimplify//FCShowEpsilon,{EpsilonIR,0,0}]//Normal
//FCHideEpsilon;]//First


(* ::Text:: *)
(*Pick up the finite part and separate color singlet and color octet contributions from each other*)


{finitePart,divergentPart}=FCSplit[amp5,{SMP["Delta_IR"]}];
AbsoluteTiming[finitePartEval=(finitePart/.D->4)//SUNSimplify//Expand2[#,SUNTF]&//ReplaceAll[#,ruleColor]&;]//First


(* ::Text:: *)
(*Final splitting into spin singlet, spin triplet, color singlet and color octet pieces*)


{spinSingletFin,spinTripletFin}=FCSplit[finitePartEval,{ST1,ST2}];
{spinSingletColorSingletFin,spinSingletColorOctetFin}=FullSimplify/@(FCSplit[spinSingletFin,{SUNTF}]);
{spinTripletColorSingletFin,spinTripletColorOctetFin}=FullSimplify/@(FCSplit[spinTripletFin,{SUNTF}]);


(* ::Subsection:: *)
(*Final matching coefficients*)


getMatchingCoeff[ex_,ru_]:=
(m1 m2 I ex//PowerExpand//Simplify//ReplaceAll[#,ru]&//
ReplaceAll[#,{SMP["g_s"]^4->16Pi^2 SMP["alpha_s"]^2,FCI[CSP[ST1,ST2]]:>1,DOT[x_,y_]:>1,
SUNFDelta[__]:>1,SUNTF[__]:>1}]&//Simplify)/.hold->Identity


matchingCoeff["d_ss"]=getMatchingCoeff[spinSingletColorSingletFin,{Log[m1]->1/2Log[(m1/ScaleMu)^2]+
Log[ScaleMu],Log[m2]->1/2Log[(m2/ScaleMu)^2]+Log[ScaleMu]}]


matchingCoeff["d_sv"]=getMatchingCoeff[spinTripletColorSingletFin,{Log[m1]->1/2Log[(m1/m2)^2]+Log[m2]}]


matchingCoeff["d_vs"]=getMatchingCoeff[spinSingletColorOctetFin,{Log[m1]->1/2Log[(m1/ScaleMu)^2]+Log[ScaleMu],
Log[m2]->1/2Log[(m2/ScaleMu)^2]+Log[ScaleMu]}]//Collect2[#,CA,CF]&


matchingCoeff["d_vv"]=getMatchingCoeff[spinTripletColorOctetFin,{Log[m1]->1/2Log[(m1/ScaleMu)^2]+
Log[ScaleMu],Log[m2]->1/2Log[(m2/ScaleMu)^2]+Log[ScaleMu]}]//Collect2[#,CA,CF]&


(* ::Subsection:: *)
(*Check with the literature*)


(* ::Text:: *)
(*Compare our results to arXiv:hep-ph/9802365, Eq. 3.1 - 3.4*)


matchingCoeffPinedaSoto["d_ss"]=- CF(CA/2-CF) SMP["alpha_s"]^2/(m1^2-m2^2)(m1^2(Log[m2^2/ScaleMu^2]+1/3)-m2^2(Log[m1^2/ScaleMu^2]+1/3));
matchingCoeffPinedaSoto["d_sv"]= CF(CA/2-CF) SMP["alpha_s"]^2/(m1^2-m2^2)m1 m2 Log[m1^2/m2^2];
matchingCoeffPinedaSoto["d_vs"]= -2CF SMP["alpha_s"]^2/(m1^2-m2^2)(m1^2(Log[m2^2/ScaleMu^2]+1/3)-m2^2(Log[m1^2/ScaleMu^2]+1/3))+CA SMP["alpha_s"]^2/(4(m1^2-m2^2))(
3(m1^2(Log[m2^2/ScaleMu^2]+1/3)-m2^2(Log[m1^2/ScaleMu^2]+1/3))
+1/(m1 m2) (m1^4(Log[m2^2/ScaleMu^2]+10/3)-m2^4(Log[m1^2/ScaleMu^2]+10/3)));
matchingCoeffPinedaSoto["d_vv"]= 2CF SMP["alpha_s"]^2/(m1^2-m2^2) m1 m2 Log[m1^2/m2^2]+
 CA SMP["alpha_s"]^2/(4(m1^2-m2^2))((m1^2(Log[m2^2/ScaleMu^2]+3)-m2^2(Log[m1^2/ScaleMu^2]+3))-3 m1 m2 Log[m1^2/m2^2]);


resLit=(8 (-9+\[Pi]^2) CSP[ST,STcc] SMP["alpha_fs"]^3 SMP["e_Q"]^6)/(9 SMP["m_Q"]^2);
Print["Check with Eq. 3.1-3.4 in arXiv:hep-ph/9802365: ",
			If[Simplify[PowerExpand[{matchingCoeff["d_ss"]-matchingCoeffPinedaSoto["d_ss"],
matchingCoeff["d_sv"]-matchingCoeffPinedaSoto["d_sv"],
matchingCoeff["d_vs"]-matchingCoeffPinedaSoto["d_vs"],
matchingCoeff["d_vv"]-matchingCoeffPinedaSoto["d_vv"]}]]==={0,0,0,0}, "CORRECT.", "!!! WRONG !!!"]];
