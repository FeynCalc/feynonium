(* ::Package:: *)

(* :Title: H-QQbarGa-LCDA															*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2014-2020 Vladyslav Shtabovenko
*)

(* :Summary:  H -> Q Qbar Ga, LCDA-NRQCD, matching, tree					*)

(* ------------------------------------------------------------------------ *)


(* ::Title:: *)
(*Exclusive electromagnetic decays of a Higgs into a heavy quarkonum in LCDA-NRQCD*)


(* ::Section:: *)
(*Load FeynCalc and the necessary add-ons or other packages*)


description="H -> Q Qbar Ga, LCDA-NRQCD, matching, tree";
If[ $FrontEnd === Null,
	$FeynCalcStartupMessages = False;
	Print[description];
];
If[ $Notebooks === False,
	$FeynCalcStartupMessages = False
];
$LoadAddOns={"FeynArts", "FeynOnium"};
<<FeynCalc`
$FAVerbose = 0;

FCCheckVersion[9,4,0];


(* ::Section:: *)
(*Enter the amplitude*)


(* ::Text:: *)
(*Here we follow 1907.06473, with the LC amplitude given in Eq. 19*)


amp[1]=-1/(SP[nbar,P])DF[x-1/2-SP[nbar,Q]/SP[nbar,P]]*
SpinorUBar[p1,QMass].GS[nbar,Polarization[kp,
-I,Transversality->True]].SpinorV[p2,QMass]


(* ::Section:: *)
(*Helpful auxiliary functions*)


(* ::Text:: *)
(*This is for applying the Dirac equation backwards*)


diracRule={DOT[Spinor[sign_. mom_Momentum,m_,1],x___,
	s_Spinor]/;EvenQ[Length[{x}]]:>
sign(1/m)DOT[Spinor[ sign mom,m,1],DiracGamma[mom],x,s]};


(* ::Text:: *)
(*and this is for switching to P and q momenta*)


switchMomenta[x_]:=FixedPoint[FCReplaceMomenta[#,
	{p1->1/2P+Q,p2->1/2P-Q},ExpandScalarProduct->True,
	EpsEvaluate->True]&,x];


(* ::Section:: *)
(*Fix the kinematics*)


QMass=SMP["m_Q"];
MH=SMP["m_H"];


(* ::Text:: *)
(*All particles are on-shell*)


FCClearScalarProducts[]
SP[kp, kp] = 0;
SP[kphat, kphat] = 0;
SP[p1, p1] = QMass^2;
SP[p2, p2] = QMass^2;
SP[P, Q] = 0;
SP[P, P] = 4Eq^2;
SP[Q, Q] = FCI[- CSP[q,q]];


(* ::Text:: *)
(*Eq is the the zero component of the heavy quark momenta.*)


Eq=FCI[Sqrt[CSP[q,q]+SMP["m_Q"]^2]];


(* ::Text:: *)
(*Temporal components of 4-momenta*)


TC[kphat]=1
TC[q]=0;
TC[q1hat]=0;
TC[P]=FCI[Sqrt[4 Eq^2+CSP[P,P]]];
TC[Q]=FCI[CSP[P,q]/(2 Eq)];
TC[Polarization[kp,-I,Transversality->True]]=0;
TC[kp]=kpvec;
TC[p1]=(1/2)TC[P]+TC[Q]
TC[p2]=(1/2)TC[P]-TC[Q];
TC[nbar]=MH/(MH TC[kp])TC[kp];


(* ::Text:: *)
(*Cartesian scalar products*)


CSP[kp,Polarization[kp,-I,Transversality->True]]=0;
CSP[kphat,Polarization[kp,-I,Transversality->True]]=0;
CSP[kphat]=1;
CSP[q1hat]=1;
CSP[kphat,kphat]=1;
CSP[q1vhat,q1vhat]=1;


(* ::Text:: *)
(*Photon polarization*)


CartesianPair[CartesianMomentum[kp|kphat],
	CartesianMomentum[Polarization[kp,I,Transversality->True]]]=0;
CartesianPair[CartesianMomentum[kp|kphat],
	CartesianMomentum[Polarization[kp,-I,Transversality->True]]]=0;


(* ::Text:: *)
(*Extract absolute values of Cartesian 3-momenta*)


CartesianMomentum[kp]=kpvec CartesianMomentum[kphat];
CartesianMomentum[P]=-kpvec CartesianMomentum[kphat];
CartesianMomentum[Q]=FCI[CartesianMomentum[q]+
	CartesianMomentum[P]CSP[P,q]/CSP[P,P](TC[P]/(2Eq)-1)];
CartesianMomentum[q]=SoftScale q1vabs CartesianMomentum[q1hat];
CartesianMomentum[nbar]=MH/(MH TC[kp])CartesianMomentum[kp];


(* ::Text:: *)
(*The absolute value of the photon 3-momentum expressed through Eq*)


kpvec=FCI[1/(2 MH)(MH^2-4Eq^2)];


(* ::Text:: *)
(*To avoid excessive use of PowerExpand later on...*)


Unprotect[Power];
\!\(\*
TagBox[
StyleBox[
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"SMP", "[", "\"\<m_Q\>\"", "]"}], ",", "2"}], "]"}], ",", 
RowBox[{"Rational", "[", 
RowBox[{"1", ",", "2"}], "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\):=SMP["m_Q"];
\!\(\*
TagBox[
StyleBox[
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"q1vabs", ",", "2"}], "]"}], ",", 
RowBox[{"Rational", "[", 
RowBox[{"1", ",", "2"}], "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\):=q1vabs;
\!\(\*
TagBox[
StyleBox[
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"q1vabs", ",", "2"}], "]"}], ",", 
RowBox[{"Rational", "[", 
RowBox[{
RowBox[{"-", "1"}], ",", "2"}], "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\):=1/q1vabs;
Protect[Power];


(* ::Section:: *)
(*Expand the amplitude*)


(* ::Text:: *)
(*Apply the Dirac equation backwards to have only vector and axial-vector contributions after the*)
(*SPVAT decomposition.Then rewrite the spinor chain in terms of nonrelativistic quantities*)


amp[2]=(FCI[amp[1]]/.diracRule)//DiracReduce//LorentzToCartesian//
	FMToStandardSpinorChains//Contract;


(* ::Text:: *)
(*Naive expansion in SoftScale is requires too much time due to many nested square roots.*)
(*Instead, we will canonicalize the indices and collect unique terms in the numerators and denominators to minimize the number of expressions that need to be extended.*)


amp[3]=Uncontract[amp[2],FMStandardSpinorChain,Pair->All,
	CartesianPair->All]//
	FCCanonicalizeDummyIndices[#,
	Momentum->{FMStandardSpinorChain}]&//
	FeynAmpDenominatorExplicit//Collect2[#,FMStandardSpinorChain]&;


amp[4]=Isolate[amp[3],{FMStandardSpinorChain},IsolateFast->True,
	IsolateTimes->True];


amp[5]=FCLoopIsolate[amp[4],{FMStandardSpinorChain},Factoring->prefHead,
	Head->chainHead]


(* ::Text:: *)
(*Here we separately expand Dirac chains and all other prefactors (including denominators). Then we create the corresponding substitution rules and plug them back into the original expression.*)


chains=Cases2[amp[5],chainHead];
prefs=Cases2[amp[5],prefHead];


prefEval=(FRH[prefs/.prefHead->Identity]//LorentzToCartesian//
	switchMomenta//PauliSigmaExpand//EpsEvaluate//
	DotSimplify)/.Sqrt[x_]:>Simplify[PowerExpand[Sqrt[Simplify[x]]]];


prefsExpanded0=Map[(Series[PowerExpand[#],{SoftScale,0,4}]//
	Normal)&,prefEval];


prefsExpanded=Map[Isolate[#,SoftScale,IsolateFast->True,
	IsolateTimes->True]&,prefsExpanded0];


prefsRule=Thread[Rule[prefs,prefsExpanded]];


chainFull=FMSpinorChainsExplicit[chains,{p1,QMass},{p2,QMass},
	FMKinematicsOfHeavyFermions->"TwoBodyLabFrame",
	FMSpinorNormalization->"nonrelativistic",
	FinalSubstitutions->{FCGV["Jacobi QR"]->q,FCGV["Jacobi P"]->P}];


chainsEval=((chainFull/.chainHead->Identity)//switchMomenta//
	PauliSimplify[#,PauliReduce->True]&//PauliSigmaExpand//
	EpsEvaluate//DotSimplify)/.{
	Sqrt[x_]:>Simplify[PowerExpand[Sqrt[Simplify[x]]]]};


chainsExpanded=Map[Isolate[(Series[#,{SoftScale,0,4}]//Normal),
	{SoftScale},IsolateFast->True,IsolateTimes->True]&,chainsEval];


chainsRule=Thread[Rule[chains,chainsExpanded]];


(* ::Text:: *)
(*With everything inserted we expand again (this time everything is linear in SoftScale), contract*)
(*and collect*)


amp[6]=Series[PowerExpand[amp[5]/.chainsRule/.prefsRule],
	{SoftScale,0,4}]//Normal;


amp[7]=FRH[amp[6]]//Contract;


amp[8]=Collect2[amp[7],SoftScale,PauliSigma,Factoring->Simplify];


(* ::Text:: *)
(*Substitute Pauli chains containing a single Pauli matrix with a 3-vector ST*)


amp[9]=amp[8]/.{PauliXi[-I].PauliSigma[x_].PauliEta[I]:>
	CartesianPair[x,CartesianMomentum[ST[-I]]],
	PauliXi[-I].PauliEta[I]->SS[-I]};


(* ::Text:: *)
(*Project out J = 0, 1, 2 contributions*)


ampQCD$J0[0]=FMCartesianTensorDecomposition[amp[9],{q1hat,ST[-I]},0];


ampQCD$J1[0]=FMCartesianTensorDecomposition[amp[9],{q1hat,ST[-I]},1];


ampQCD$J2[0]=FMCartesianTensorDecomposition[amp[9],{q1hat,ST[-I]},2]//
Collect2[#,SoftScale,CartesianPair,Eps]&;


(* ::Text:: *)
(*There is no J =  0 contribution. For the J =  1 contribution we ignore odd derivatives of the Dirac delta to ensure that only C = -1 contributions (hc and Jpsi) are kept. No matching is done for J = 2.*)


ampQCD$J0[0]


ampQCD$J1[1]=ampQCD$J1[0]//Collect2[#,SoftScale,CartesianPair,Eps]&//
	ReplaceAll[#,Derivative[i_?OddQ][DF][-1/2+x]->0]&


(* ::Section:: *)
(*Enter the NRQCD-factorized LCDA amplitude*)


(* ::Text:: *)
(*Perturbative LCDA amplitude for the matching*)


ampLCDA$J1[0]=(
CSP[c0,ST[-I]]+(1/QMass)CSP[c1,q]SS[-I]+
(1/QMass^2)CSP[c2,ST[-I]]CSP[q,q]+
(1/QMass^2)(CSP[c3,q]CSP[q,ST[-I]]-1/3CSP[c3,ST[-I]]CSP[q,q])+
(1/QMass^3)CSP[c4,q]CSP[q,q]SS[-I]+
(1/QMass^4)CSP[c5,ST[-I]]CSP[q,q]^2+
(1/QMass^4)(CSP[c6,q]CSP[q,ST[-I]]-1/3CSP[c6,ST[-I]]CSP[q,q])CSP[q,q]
);


ampLCDA$J1[1]=Series[FCI[ampLCDA$J1[0]],{SoftScale,0,4}]//Normal


(* ::Section:: *)
(*Matching to LCDA for J=1*)


(* ::Text:: *)
(*The matching is done order by order in qabs. Yet the determination of the tensor short distance coefficients is cumbersome to automatize.*)


(* ::Text:: *)
(*Usually, it is easier to look at the matching equation at the given order in qabs and *)
(*guess the correct short distance coefficient by first figuring out the tensor structure and*)
(*then fixing the scalar coefficients.*)


(* ::Subsection:: *)
(*0th order in qabs*)


sdCoeff[c0]=FCI[CV[c0,i_]]->1/(2QMass)DF[x-1/2] *
	CV[CartesianMomentum[Polarization[kp,-I,Transversality->True]],i]


(* ::Text:: *)
(*Check*)


Simplify[Contract[(Uncontract[Coefficient[ampLCDA$J1[1],SoftScale,0],c0,CartesianPair->All]/.sdCoeff[c0])]-
	Coefficient[ampQCD$J1[1],SoftScale,0]]


(* ::Subsection:: *)
(*1st order in qabs*)


sdCoeff[c1]=FCI[CV[c1,i_]]->-1/(2QMass)I DF[-(1/2)+x]*Eps[CartesianIndex[i],
	CartesianMomentum[kphat],CartesianMomentum[Polarization[kp,
	-I,Transversality->True]]]


(* ::Text:: *)
(*Check*)


Simplify[Contract[(Uncontract[Coefficient[ampLCDA$J1[1],SoftScale,1],c1,
	CartesianPair->All]/.sdCoeff[c1])]-
	Coefficient[ampQCD$J1[1],SoftScale,1]]


(* ::Subsection:: *)
(*2nd order in qabs*)


sdCoeff[c2]=FCI[CV[c2, i_]] -> (CV[Polarization[kp, -I, Transversality -> True], i]*
   (-20*DF[-1/2 + x] + Derivative[2][DF][-1/2 + x]))/(48*SMP["m_Q"])


sdCoeff[c3]=FCI[CV[c3, i_]] -> (CV[Polarization[kp, -I, Transversality -> True], i]*
   (20*DF[-1/2 + x] - Derivative[2][DF][-1/2 + x]))/(80*SMP["m_Q"])


(* ::Text:: *)
(*Check*)


Simplify[Contract[(Uncontract[Coefficient[ampLCDA$J1[1],SoftScale,2],
	c2,c3,CartesianPair->All]/.sdCoeff[c2]/.sdCoeff[c3])]-
	Coefficient[ampQCD$J1[1],SoftScale,2]]


(* ::Subsection:: *)
(*3rd order in qabs*)


sdCoeff[c4]=FCI[CV[c4, i_]] -> ((I/80)*Eps[CartesianIndex[i], 
	CartesianMomentum[kphat], CartesianMomentum[Polarization[kp,
	-I, Transversality -> True]]]*
   (40*DF[-1/2 + x] - Derivative[2][DF][-1/2 + x]))/SMP["m_Q"]


(* ::Text:: *)
(*Check*)


Simplify[Contract[(Uncontract[Coefficient[ampLCDA$J1[1],SoftScale,3],
	c4,CartesianPair->All]/.sdCoeff[c4])]-
	Coefficient[ampQCD$J1[1],SoftScale,3]]


(* ::Subsection:: *)
(*4th order in qabs*)


sdCoeff[c5]=FCI[CV[c5, i_]] -> (CV[Polarization[kp, -I, 
	Transversality -> True], i]*(1520*DF[-1/2 + x] - 
	152*Derivative[2][DF][-1/2 + x] + Derivative[4][DF][-1/2 + x]))/
  (3840*SMP["m_Q"])


sdCoeff[c6]=FCI[CV[c6, i_]] -> (CV[Polarization[kp, -I, 
	Transversality -> True], i]*(-1400*DF[-1/2 + x] + 
	140*Derivative[2][DF][-1/2 + x] - Derivative[4][DF][-1/2 + x]))/
  (4480*SMP["m_Q"])


(* ::Text:: *)
(*Check*)


Simplify[Contract[(Uncontract[Coefficient[ampLCDA$J1[1],SoftScale,4],c5,c6,
CartesianPair->All]/.sdCoeff[c5]/.sdCoeff[c6])]-
Coefficient[ampQCD$J1[1],SoftScale,4]]


(* ::Section:: *)
(*Consistency check for the short distance coefficients*)


(* ::Text:: *)
(*Set of the final short distance coefficients*)


finalSdCoeffs={sdCoeff[c0],sdCoeff[c1],sdCoeff[c2],
	sdCoeff[c3],sdCoeff[c4],sdCoeff[c5],sdCoeff[c6]}


check=Contract[Uncontract[ampLCDA$J1[1],c0,c1,c2,c3,c4,c5,c6,
	CartesianPair->All]/.finalSdCoeffs]-ampQCD$J1[1]//Simplify


FCCompareResults[{check},{0},
Text->{"\tExpanded QCD and LCD amplitudes match exactly:",
"CORRECT.","WRONG!"}, Interrupt->{Hold[Quit[1]],Automatic}];


(* ::Text:: *)
(*The c - coefficients are related to the one' s in the paper (Eqs. 20 in 1907.06473) in the following way :*)


(* ::Text:: *)
(*c0 ~ tilde c _ 0 up to the polarization vector*)
(*c2 is tilde c _ {D^2} up to the polarization vector*)
(*c3 is tilde c _ {D^(i D^j)} up to the polarization vector*)
(*c5 is tilde c _ {D^4} up to the polarization vector*)
(*c6 is tilde c _ {D^2 D^(i D^j)} up to the polarization vector*)


(* ::Section:: *)
(*Check the final results*)


knownResult ={CartesianPair[CartesianIndex[i_], CartesianMomentum[c0]] -> 
  (CV[CartesianMomentum[Polarization[kp, -I, Transversality -> True]], i]*
    DF[-1/2 + x])/(2*SMP["m_Q"]), 
 CartesianPair[CartesianIndex[i_], CartesianMomentum[c1]] -> 
  ((-I/2)*DF[-1/2 + x]*Eps[CartesianIndex[i], CartesianMomentum[kphat], 
     CartesianMomentum[Polarization[kp, -I, Transversality -> True]]])/
   SMP["m_Q"], CartesianPair[CartesianIndex[i_], CartesianMomentum[c2]] -> 
  (CV[Polarization[kp, -I, Transversality -> True], i]*
    (-20*DF[-1/2 + x] + Derivative[2][DF][-1/2 + x]))/(48*SMP["m_Q"]), 
 CartesianPair[CartesianIndex[i_], CartesianMomentum[c3]] -> 
  (CV[Polarization[kp, -I, Transversality -> True], i]*
    (20*DF[-1/2 + x] - Derivative[2][DF][-1/2 + x]))/(80*SMP["m_Q"]), 
 CartesianPair[CartesianIndex[i_], CartesianMomentum[c4]] -> 
  ((I/80)*Eps[CartesianIndex[i], CartesianMomentum[kphat], 
     CartesianMomentum[Polarization[kp, -I, Transversality -> True]]]*
    (40*DF[-1/2 + x] - Derivative[2][DF][-1/2 + x]))/SMP["m_Q"], 
 CartesianPair[CartesianIndex[i_], CartesianMomentum[c5]] -> 
  (CV[Polarization[kp, -I, Transversality -> True], i]*
    (1520*DF[-1/2 + x] - 152*Derivative[2][DF][-1/2 + x] + 
     Derivative[4][DF][-1/2 + x]))/(3840*SMP["m_Q"]), 
 CartesianPair[CartesianIndex[i_], CartesianMomentum[c6]] -> 
  (CV[Polarization[kp, -I, Transversality -> True], i]*
    (-1400*DF[-1/2 + x] + 140*Derivative[2][DF][-1/2 + x] - 
     Derivative[4][DF][-1/2 + x]))/(4480*SMP["m_Q"])};
FCCompareResults[finalSdCoeffs,knownResult,
Text->{"\tCompare to Eqs. 20 in 1907.06473:",
"CORRECT.","WRONG!"}, Interrupt->{Hold[Quit[1]],Automatic}];
Print["\tCPU Time used: ", Round[N[TimeUsed[],4],0.001], " s."];



