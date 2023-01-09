(* ::Package:: *)

(* :Title: H-QQbarGaGl-LCDA															*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2017-2023 Vladyslav Shtabovenko
*)

(* :Summary:  H -> Q Qbar Ga Gl, LCDA-NRQCD, matching, tree					*)

(* ------------------------------------------------------------------------ *)


(* ::Title:: *)
(*Exclusive electromagnetic decays of a Higgs into a heavy quarkonum in LCDA-NRQCD*)


(* ::Section:: *)
(*Load FeynCalc and the necessary add-ons or other packages*)


description="H -> Q Qbar Ga Gl, LCDA-NRQCD, matching, tree";
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

FCCheckVersion[9,3,1];


(* ::Section:: *)
(*Enter the amplitude*)


(* ::Text:: *)
(*Here we follow 1907.06473, with the LC amplitudes given in Eq. 21*)


amp[1]={
SUNTF[a,b,c]I SMP["g_s"]DF[x-1/2-SP[nbar,p1-p2+kg]/(2SP[nbar,P])]*
	SpinorUBar[p1,QMass].GS[Polarization[kg,-I,
	Transversality->True]].(I(GS[p1+kg]+QMass)).GS[nbar,
	Polarization[kp,-I,Transversality->True]].SpinorV[p2,
	QMass](SFAD[{{0,2p1.kg}},{{0,nbar.P}},Dimension->4]),
SUNTF[a,b,c]I SMP["g_s"]DF[x-1/2-SP[nbar,p1-p2-kg]/(2SP[nbar,P])]*
	SpinorUBar[p1,QMass].GS[nbar,Polarization[kp,-I,
	Transversality->True]].(I(GS[-p2-kg]+QMass)).GS[Polarization[kg,
	-I,Transversality->True]].SpinorV[p2,QMass](SFAD[{{0,
	2p2.kg}},{{0,nbar.P}},Dimension->4]),
-SUNTF[a,b,c]I SMP["g_s"]DF[x-1/2-SP[nbar,p1-p2+kg]/(2SP[nbar,P])]*
	SpinorUBar[p1,QMass].GS[nbar,Polarization[kp,-I,
	Transversality->True]].SpinorV[p2,QMass](I*
	SP[Polarization[kg,-I,Transversality->True],
	nbar])(SFAD[{{0,nbar.kg}},{{0,nbar.P}},Dimension->4]),
-SUNTF[a,b,c]I SMP["g_s"]DF[x-1/2-SP[nbar,p1-p2-kg]/(2SP[nbar,P])]*
	SpinorUBar[p1,QMass].GS[nbar,Polarization[kp,-I,
	Transversality->True]].SpinorV[p2,QMass](-I*
	SP[Polarization[kg,-I,Transversality->True],nbar])*
	(SFAD[{{0,nbar.kg}},{{0,nbar.P}},Dimension->4])
};


(* ::Section:: *)
(*Helpful auxiliary functions*)


(* ::Text:: *)
(*This is for applying the Dirac equation backwards*)


diracRule={DOT[Spinor[sign_. mom_Momentum,m_,1],x___,s_Spinor]/;
	EvenQ[Length[{x}]]:>
	sign(1/m)DOT[Spinor[ sign mom,m,1],DiracGamma[mom],x,s]};


(* ::Text:: *)
(*and this is for switching to P and q1 and q2 momenta*)


switchMomenta[x_]:=FixedPoint[FCReplaceMomenta[#/.
	Polarization[kg,a___]:>Polarization[KG,a]/.
		Polarization[KGR,a___]:>Polarization[kgR,a],
		{p1->1/3P+Q1-Q2,p2->1/3P-Q1-Q2,kg->1/3P+2Q2,
p1R->1/3PR+q1-q2,p2R->1/3PR-q1-q2,kgR->1/3PR+2q2
},ExpandScalarProduct->True,EpsEvaluate->True]&,x];


(* ::Text:: *)
(*This helper function is useful to reveal the scalings*)


explicitSoftScale[ex_]:=
FixedPoint[ExpandScalarProduct[ReplaceRepeated[ExpandScalarProduct[#],{
CartesianMomentum[q1]->SoftScale CartesianMomentum[q1v],
CartesianMomentum[q2]->SoftScale CartesianMomentum[q2v]}]]&,ex,5];


(* ::Section:: *)
(*Fix the kinematics*)


MH=SMP["m_H"];
QMass=SMP["m_Q"];
EL=SMP["e"];
GF=SMP["G_F"];
QCharge=SMP["e_Q"];


(* ::Text:: *)
(*All particles are on-shell*)


FCClearScalarProducts[]
SP[kp, kp] = 0;
SP[kg, kg] = 0;
SP[kphat, kphat] = 0;
SP[p1, p1] = QMass^2;
SP[p2, p2] = QMass^2;


(* ::Text:: *)
(*Eq is the the zero component of the heavy quark momenta.*)


Eq=FCI[Sqrt[CSP[q,q]+SMP["m_Q"]^2]];


(* ::Text:: *)
(*Temporal components of 4-momenta. Notice that the 0th zero component of the gluon polarization vector is not zero in the lab frame!*)


TC[Polarization[kp,-I,Transversality->True]]=0;
(*Notice that the 0th zero component of kg is not zero in the lab frame!*)
TC[Polarization[kgR,-I,Transversality->True]]=0;
TC[p1R]=ExpandScalarProduct[Sqrt[CSP[q1-q2]+QMass^2]];
TC[p2R]=ExpandScalarProduct[Sqrt[CSP[q1+q2]+QMass^2]];
TC[kgR]=FCI[2Sqrt[CSP[q2]]];
TC[P]=MH-kpvec;
TC[kp]=kpvec;
TC[q1]=ExpandScalarProduct[1/2(TC[p1R]-TC[p2R])]
TC[q2]=ExpandScalarProduct[1/6(2TC[kgR]-TC[p1R]-TC[p2R])]
TC[nbar]=MH/(MH TC[kp])TC[kp];

TC[PR]=ExpandScalarProduct[Sqrt[CSP[q1-q2]+QMass^2]+
	Sqrt[CSP[q1+q2]+QMass^2]+2Sqrt[CSP[q2]]];
TC[Q1]=ExpandScalarProduct[1/TC[PR](TC[P]TC[q1]+CSP[P,q1])]
TC[Q2]=ExpandScalarProduct[1/TC[PR](TC[P]TC[q2]+CSP[P,q2])]
TC[Polarization[KG,-I,Transversality->True]]=
	1/TC[PR]CSP[P,Polarization[kgR,-I,Transversality->True]]


(* ::Text:: *)
(*Cartesian scalar products*)


CSP[kphat]=1;
CSP[Phat]=1;
CSP[q1vhat]=1;
CSP[q2vhat]=1;


(* ::Text:: *)
(*Photon and gluon polarizations*)


CSP[q2,Polarization[kgR,-I,Transversality->True]]=0;
CSP[q2v,Polarization[kgR,-I,Transversality->True]]=0;
CSP[q2vhat,Polarization[kgR,-I,Transversality->True]]=0;
CSP[kgR,Polarization[kgR,-I,Transversality->True]]=0;
CSP[kp,Polarization[kp,-I,Transversality->True]]=0;
CSP[kphat,Polarization[kp,-I,Transversality->True]]=0;


(* ::Text:: *)
(*Extract absolute values of Cartesian 3-momenta*)


CartesianMomentum[kp]=kpvec CartesianMomentum[kphat];
CartesianMomentum[P]=-kpvec CartesianMomentum[kphat];
CartesianMomentum[Q]=FCI[CartesianMomentum[q]+
	CartesianMomentum[P]CSP[P,q]/CSP[P,P](TC[P]/(2Eq)-1)];
CartesianMomentum[q]=SoftScale q1vabs CartesianMomentum[q1hat];
CartesianMomentum[nbar]=MH/(MH TC[kp])CartesianMomentum[kp];


(* ::Text:: *)
(*The absolute value of the photon 3-momentum expressed through the 0th components*)
(*of P in the rest frame*)


kpvec=ExpandScalarProduct[(MH^2-TC[PR]^2)/(2MH)];


(* ::Text:: *)
(*To avoid excessive use of PowerExpand later on...*)


CartesianMomentum[P]=-kpvec CartesianMomentum[kphat];
CartesianMomentum[PR]=0;
CartesianMomentum[kp]=kpvec CartesianMomentum[kphat];
CartesianMomentum[Phat]=- CartesianMomentum[kphat];
CartesianMomentum[Polarization[KG,-I,Transversality->True]]=FCI[
CartesianMomentum[Polarization[kgR,-I,Transversality->True]]+
(TC[P]/TC[PR]-1)CSP[Phat,Polarization[kgR,-I,Transversality->True]]*
	CartesianMomentum[Phat]];
CartesianMomentum[Q1]=FCI[CartesianMomentum[P]TC[q1]/TC[PR]+CartesianMomentum[q1]+(TC[P]/TC[PR]-1)CSP[Phat,q1]CartesianMomentum[Phat]];
CartesianMomentum[Q2]=FCI[CartesianMomentum[P]TC[q2]/TC[PR]+CartesianMomentum[q2]+(TC[P]/TC[PR]-1)CSP[Phat,q2]CartesianMomentum[Phat]];
CartesianMomentum[nbar]=MH/(MH TC[kp])CartesianMomentum[kp];


(* ::Text:: *)
(*To avoid excessive use of PowerExpand later on...*)


Unprotect[Power];
\!\(\*
TagBox[
StyleBox[
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"QMass", ",", "2"}], "]"}], ",", 
RowBox[{"Rational", "[", 
RowBox[{"1", ",", "2"}], "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\):=QMass;
\!\(\*
TagBox[
StyleBox[
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"q2vabs", ",", "2"}], "]"}], ",", 
RowBox[{"Rational", "[", 
RowBox[{"1", ",", "2"}], "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\):=q2vabs;
\!\(\*
TagBox[
StyleBox[
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"q2vabs", ",", "2"}], "]"}], ",", 
RowBox[{"Rational", "[", 
RowBox[{
RowBox[{"-", "1"}], ",", "2"}], "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\):=1/q2vabs;
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
(*Simplify the Dirac algebra and apply the Dirac equation backwards to have only vector and axial-vector contributions after the SPVAT decomposition.Then rewrite the spinor chain in terms of nonrelativistic quantities*)


amp[2]=(DiracSimplify[amp[1]/.SUNFDelta[__]:>1]/.diracRule)//
	DiracReduce//FMToStandardSpinorChains//Total//LorentzToCartesian//
	Collect2[#,FMStandardSpinorChain]&;


(* ::Text:: *)
(*Naive expansion in SoftScale is requires too much time due to many nested square roots.*)
(*Instead, we will canonicalize the indices and collect unique terms in the numerators and denominators to minimize the number of expressions that need to be extended.*)


amp[3]=Uncontract[amp[2],FMStandardSpinorChain,Pair->All,
	CartesianPair->All]//FCCanonicalizeDummyIndices[#,
	Momentum->{FMStandardSpinorChain}]&//
	FeynAmpDenominatorExplicit[#,Head->prop]&//
	Collect2[#,FMStandardSpinorChain,prop]&;


amp[4]=Collect2[amp[3],{FMStandardSpinorChain,prop},IsolateNames->KK,
	IsolateFast->True];


amp[5]=FCLoopIsolate[amp[4],{FMStandardSpinorChain,prop},Factoring->prefHead,
	Head->chainHead]//.chainHead[a_prop b_]:>a chainHead[b];


(* ::Text:: *)
(*Here we separately expand Dirac chains, propagators and all other prefactors. Then we create the corresponding substitution rules and plug them back into the original expression.*)


chains=Cases2[amp[5],chainHead];
prefs=Cases2[amp[5],prefHead];
props=Cases2[amp[5],prop];


propsEval=(FRH[props/.prop->Identity]//LorentzToCartesian//switchMomenta);


propsExpanded0=Map[(Series[PowerExpand[#/.Dispatch[{
CartesianMomentum[q1]->SoftScale CartesianMomentum[q1v],
CartesianMomentum[q2]->SoftScale CartesianMomentum[q2v]}]],
	{SoftScale,0,3}]//Normal)&,propsEval];


prefEval=(FRH[prefs/.prefHead->Identity]//LorentzToCartesian//
	switchMomenta);


(* ::Text:: *)
(*This expansion takes about 20 seconds*)


prefsExpanded0=Map[(Series[PowerExpand[#/.Dispatch[{
	CartesianMomentum[q1]->SoftScale CartesianMomentum[q1v],
	CartesianMomentum[q2]->SoftScale CartesianMomentum[q2v]}]],
	{SoftScale,0,3}]//Normal)&,prefEval];


prefsExpanded=Collect2[#,SoftScale,LorentzIndex,CartesianIndex,Eps,DOT,
	IsolateNames->KK,Factoring->False,IsolateFast->True]&/@prefsExpanded0;


chainFull=FMSpinorChainsExplicit[chains,{p1,QMass},{p2,QMass},
	FMKinematicsOfHeavyFermions->"ThreeBodyLabFrame",
	FMNormalization->"nonrelativistic",
	FinalSubstitutions->{FCGV["Jacobi Q1R"]->q1,FCGV["Jacobi Q2R"]->q2,
	FCGV["Jacobi P"]->P,FCGV["m3"]->0}];


chainsEval=(FRH[chainFull/.chainHead->Identity]//
	LorentzToCartesian//PauliSimplify[#,PauliReduce->True]&//
	switchMomenta);


chainsExpanded0=Map[(Series[PowerExpand@DotSimplify[#/.
	Dispatch[{CartesianMomentum[q1]->SoftScale CartesianMomentum[q1v],
	CartesianMomentum[q2]->SoftScale CartesianMomentum[q2v]}],
	Expanding->False],{SoftScale,0,3}]//Normal)&,chainsEval];


chainsExpanded=Collect2[DotSimplify[#],SoftScale,CartesianIndex,Eps,DOT,
	Factoring->Function[x,Factor2[PowerExpand[Factor[x]]]],
	IsolateNames->KK]&/@chainsExpanded0;


propEval=(FRH[props/.propHead->Identity]//LorentzToCartesian//switchMomenta);


propsExpanded0=Map[(Series[PowerExpand[#/.
	Dispatch[{CartesianMomentum[q1]->SoftScale CartesianMomentum[q1v],
	CartesianMomentum[q2]->SoftScale CartesianMomentum[q2v]}]],
	{SoftScale,0,3}]//Normal)&,propsEval];


propsExpanded=Collect2[#,{SoftScale},IsolateNames->KK]&/@propsExpanded0;


prefsRule=Thread[Rule[prefs,prefsExpanded]];
chainsRule=Thread[Rule[chains,chainsExpanded]];
propsRule=Thread[Rule[props,propsExpanded]];


(* ::Text:: *)
(*With everything inserted we expand again (this time everything is linear in SoftScale), contract*)
(*and collect*)


amp[6]=Series[amp[5]/.chainsRule/.prefsRule/.propsRule,{SoftScale,0,2}]//Normal;


(* ::Text:: *)
(*Substitute Pauli chains containing a single Pauli matrix with a 3-vector ST*)


amp[7]=(amp[6]/.{PauliXi[-I].PauliSigma[x_].PauliEta[I]:>
	CartesianPair[x,CartesianMomentum[ST[-I]]],
	PauliXi[-I].PauliEta[I]->SS[-I],PauliXi[-I].PauliEta[I]->SS[-I]})//Contract;


coeffSimplify[ex_,n_]:=
	Collect2[(Coefficient[ex,SoftScale,n]//FRH)/.
	Dispatch[{CartesianMomentum[q1v]->q1vabs CartesianMomentum[q1vhat],
	CartesianMomentum[q2v]->q2vabs CartesianMomentum[q2vhat]}],ST,SS,
	CartesianPair,Eps];


amp[8]=coeffSimplify[amp[7],0]+coeffSimplify[amp[7],1]SoftScale+
	coeffSimplify[amp[7],2]SoftScale^2;


(* ::Text:: *)
(*Project out J = 0, 1, 2 contributions. There is no J =  0 contribution. For the J =  1 contribution we ignore odd derivatives of the Dirac delta to ensure that only C = -1 contributions (h_c and J/psi) are kept. No matching is done for J = 2.*)


amp[9]=Collect2[(amp[8]/.Derivative[i_?OddQ][DF][-1/2+x]->0),
	SoftScale,Factoring->Together];


ampQCD$J0[0]=FMCartesianTensorDecomposition[amp[9],{q1vhat,q2vhat,
	Polarization[kgR,-I,Transversality->True],ST[-I]},0];


ampQCD$J1[0]=FMCartesianTensorDecomposition[amp[9],{q1vhat,q2vhat,
	Polarization[kgR,-I,Transversality->True],ST[-I]},1];


ampQCD$J2[0]=FMCartesianTensorDecomposition[amp[9],{q1vhat,q2vhat,
	Polarization[kgR,-I,Transversality->True],ST[-I]},2];


(* ::Text:: *)
(*Apply Schouten's identity repeatedly to prove that the J=0 contribution vanishes*)


(*There is no J=0 contribution*)
FixedPoint[FMCartesianSchoutenBruteForce[#,{kphat,q1vhat,q2vhat,
	Polarization[kp,-I,Transversality->True],Polarization[kgR,-I,
	Transversality->True]}]&,ampQCD$J0[0]]


(* ::Text:: *)
(*Before we match, it is necessary to simplify the J=1 projections even further using Schouten's identity*)


{tmpJ1SS0,tmpJ1ST0}=FCSplit[Coefficient[ampQCD$J1[0],SoftScale,0],{ST}];
{tmpJ1SS1,tmpJ1ST1}=FCSplit[Coefficient[ampQCD$J1[0],SoftScale,1],{ST}];
{tmpJ1SS2,tmpJ1ST2}=FCSplit[Coefficient[ampQCD$J1[0],SoftScale,2],{ST}];


simpJ1SS0=FixedPoint[FMCartesianSchoutenBruteForce[#,{kphat,kphat,q1vhat,
	q1vhat,q2vhat,q2vhat,Polarization[kp,-I,Transversality->True],
	Polarization[kgR,-I,Transversality->True]}]&,tmpJ1SS0];


simpJ1SS1=FixedPoint[FMCartesianSchoutenBruteForce[#,{kphat,kphat,q1vhat,
q1vhat,q2vhat,q2vhat,Polarization[kp,-I,Transversality->True],
	Polarization[kgR,-I,Transversality->True]}]&,tmpJ1SS1];


simpJ1SS2=FixedPoint[FMCartesianSchoutenBruteForce[#,{kphat,kphat,q1vhat,
q1vhat,q2vhat,q2vhat,Polarization[kp,-I,Transversality->True],
	Polarization[kgR,-I,Transversality->True]}]&,tmpJ1SS2];


(* ::Text:: *)
(*There is nothing to simplify for the spin triplet contributions*)


{simpJ1ST0,simpJ1ST1,simpJ1ST2}={tmpJ1ST0,tmpJ1ST1,tmpJ1ST2};


ampQCD$J1[1]=Collect2[((simpJ1SS0+simpJ1ST0)+(simpJ1SS1+simpJ1ST1)SoftScale+
	(simpJ1SS2+simpJ1ST2)SoftScale^2),{q1vhat,q2vhat,q1vabs,q2vabs,
	ST,Polarization,SoftScale},Factoring->Simplify,Denominator->True];


(* ::Text:: *)
(**)


(* ::Section:: *)
(*Enter the NRQCD-factorized LCDA amplitude*)


(* ::Text:: *)
(*Color singlet matching coefficients previously obtained from the H-QQbarGa calculation.*)


sdCoeff[c0]=FCI[CV[c0,i_]]->1/(2QMass)DF[x-1/2]*
	CV[CartesianMomentum[Polarization[kp,-I,Transversality->True]],i];
sdCoeff[c1]=FCI[CV[c1,i_]]->-1/(2QMass)I DF[-(1/2)+x]*Eps[CartesianIndex[i],
	CartesianMomentum[kphat],CartesianMomentum[Polarization[kp,
	-I,Transversality->True]]];
sdCoeff[c2]=FCI[CV[c2, i_]] -> (CV[Polarization[kp, -I, Transversality -> True], i]*
   (-20*DF[-1/2 + x] + Derivative[2][DF][-1/2 + x]))/(48*SMP["m_Q"]);
sdCoeff[c3]=FCI[CV[c3, i_]] -> (CV[Polarization[kp, -I, Transversality -> True], i]*
   (20*DF[-1/2 + x] - Derivative[2][DF][-1/2 + x]))/(80*SMP["m_Q"]);
sdCoeff[c4]=FCI[CV[c4, i_]] -> ((I/80)*Eps[CartesianIndex[i], 
	CartesianMomentum[kphat], CartesianMomentum[Polarization[kp,
	-I, Transversality -> True]]]*
   (40*DF[-1/2 + x] - Derivative[2][DF][-1/2 + x]))/SMP["m_Q"];
sdCoeff[c5]=FCI[CV[c5, i_]] -> (CV[Polarization[kp, -I, 
	Transversality -> True], i]*(1520*DF[-1/2 + x] - 
	152*Derivative[2][DF][-1/2 + x] + Derivative[4][DF][-1/2 + x]))/
  (3840*SMP["m_Q"]);
sdCoeff[c6]=FCI[CV[c6, i_]] -> (CV[Polarization[kp, -I, 
	Transversality -> True], i]*(-1400*DF[-1/2 + x] + 
	140*Derivative[2][DF][-1/2 + x] - Derivative[4][DF][-1/2 + x]))/
  (4480*SMP["m_Q"]);


(* ::Subsection::Closed:: *)
(*Lagrangian insertions*)


(* ::Text:: *)
(*Helpful shortcuts for entering NRQCD Feynman rules for Lagrangian insertions*)


NRQCDProp[x_]:=ExpandScalarProduct[1/( TC[x]-  Sqrt[CSP[x]+ QMass^2])]


NRQCDVertex["D^2",{p_,kg_},s_]:=
	s*I *CSP[p,Polarization[kg,-I,Transversality->True]]/QMass;
NRQCDVertex["D^4",{p_,kg_},s_]:=
	-s*I *CSP[p,Polarization[kg,-I,Transversality->True]]*
	(CSP[p]+CSP[p,kg]+CSP[kg]/2)/(2QMass^3);

NRQCDVertex["D^6",{p_,kg_},s_]:=s*I*CSP[p,Polarization[kg,-I,
	Transversality->True]]*(CSP[kg]^2+4 CSP[kg]CSP[kg,p]+
	3CSP[kg]CSP[p]+4CSP[kg,p]^2+6CSP[kg,p]CSP[p]+3CSP[p]^2)/(8QMass^5);


NRQCDVertex["s.B",i_,{kg_}]:=-1/(2QMass) Eps[CartesianIndex[i],
	CartesianMomentum[kg],CartesianMomentum[Polarization[kg,-I,
	Transversality->True]]]


NRQCDVertex["{D^2, B^i}",i_,{p_,kg_}]:=1/(8QMass^3) Eps[CartesianIndex[i],
	CartesianMomentum[kg],CartesianMomentum[Polarization[kg,-I,
	Transversality->True]]](2CSP[p]+2CSP[p,kg]+CSP[kg])


NRQCDVertex["[Dx,E]^i",i_,{p_,kg_}]:=(1/(8QMass^2) TC[kg]Eps[CartesianIndex[i],
	CartesianMomentum[kg+2p],CartesianMomentum[Polarization[kg,-I,
	Transversality->True]]])


NRQCDVertex["{D^2, [Dx,E]^i}",i_,{p_,kg_}]:=-(3/(64QMass^4) TC[kg]*
	Eps[CartesianIndex[i],CartesianMomentum[kg+2p],
	CartesianMomentum[Polarization[kg,-I,Transversality->True]]])*
	(2CSP[p]+2CSP[p,kg]+CSP[kg])


NRQCDVectorInsertions[i_,{p_,kg_}]:=(NRQCDVertex["s.B",i,{kg}]+
	NRQCDVertex["{D^2, B^i}",i,{p,kg}]+NRQCDVertex["[Dx,E]^i",i,{p,kg}]+
	NRQCDVertex["{D^2, [Dx,E]^i}",i,{p,kg}])//ExpandScalarProduct//EpsEvaluate;


NRQCDScalarInsertions[{p_,kg_},s_]:=(NRQCDVertex["D^2",{p,kg},s]+
	NRQCDVertex["D^4",{p,kg},s]+ NRQCDVertex["D^6",{p,kg},s])//
	ExpandScalarProduct//EpsEvaluate;


(* ::Text:: *)
(*And the actual insertions:*)


(* ::Text:: *)
(*Insertions to < H | psi^+ sigma chi | 0 >*)


insertion0= SMP["g_s"]*((
	NRQCDProp[p1R+ kgR]*(
  CSP[ST[-I],c0]*NRQCDScalarInsertions[{p1R,kgR},-1]+
	(NRQCDVectorInsertions[i,{p1R,kgR}]*
	(CartesianPair[CartesianIndex[j],CartesianMomentum[c0]]SS[-I]+
	I*(-1)Eps[CartesianMomentum[c0],CartesianIndex[j],
	CartesianMomentum[ST[-I]]])KD[i,j]))+
	NRQCDProp[p2R+kgR]*(
  CSP[ST[-I],c0]*NRQCDScalarInsertions[{p2R,kgR},1]+
	(NRQCDVectorInsertions[i,{p2R,kgR}](CartesianPair[CartesianIndex[j],
	CartesianMomentum[c0]]SS[-I]-I*(-1)Eps[CartesianMomentum[c0],
	CartesianIndex[j],CartesianMomentum[ST[-I]]])KD[i,j])))
)//ExpandScalarProduct//EpsEvaluate//Contract;


(* ::Text:: *)
(*Insertions to < H | psi^+  (-i/2 D) chi | 0 > *)


insertion1= (1/QMass)*SMP["g_s"]*(
	NRQCDProp[p1R+kgR]*(
		CSP[-p2R,c1]*NRQCDScalarInsertions[{p1R,kgR},-1]SS[-I]+
		NRQCDVectorInsertions[i,{p1R,kgR}]CartesianPair[CartesianIndex[j],
		CartesianMomentum[ST[-I]]]KD[i,j]CSP[-p2R,c1])+
	NRQCDProp[p2R+kgR]*(CSP[p1R,c1]*NRQCDScalarInsertions[{p2R,kgR},1]SS[-I]+
		NRQCDVectorInsertions[i,{p2R,kgR}]CartesianPair[CartesianIndex[j],
		CartesianMomentum[ST[-I]]]KD[i,j]CSP[p1R,c1]))//
		ExpandScalarProduct//EpsEvaluate//Contract[#,EpsContract->False]&;


(* ::Text:: *)
(*Insertions to < H | psi^+ sigma - i/2*D^2 chi | 0 >*)


insertion2=(1/QMass^2)*SMP["g_s"]*(
 NRQCDProp[p1R+kgR]*(
 CSP[ST[-I],c2]*NRQCDScalarInsertions[{p1R,kgR},-1]+
  NRQCDVectorInsertions[i,{p1R,kgR}](CartesianPair[CartesianIndex[j],
  CartesianMomentum[c2]]SS[-I]+ (-1)I Eps[CartesianMomentum[c2],
  CartesianIndex[j],CartesianMomentum[ST[-I]]])
	KD[i,j])*CSP[p2R]+
	NRQCDProp[p2R+kgR]*(
 CSP[ST[-I],c2]*NRQCDScalarInsertions[{p2R,kgR},1]+
 NRQCDVectorInsertions[i,{p2R,kgR}](CartesianPair[CartesianIndex[j],
 CartesianMomentum[c2]]SS[-I]-I(-1)Eps[CartesianMomentum[c2],
 CartesianIndex[j],CartesianMomentum[ST[-I]]])KD[i,j])*CSP[p1R]
)//ExpandScalarProduct//EpsEvaluate//Contract[#,EpsContract->False]&;


insertion3=(1/QMass^2)* SMP["g_s"]*(
 NRQCDProp[p1R+kgR]*(
	1/2(2CSP[ST[-I],-p2R]CSP[c3,-p2R]-2/3CSP[ST[-I],c3]CSP[-p2R])*
	NRQCDScalarInsertions[{p1R,kgR},-1]+
NRQCDVectorInsertions[i,{p1R,kgR}]KD[i,j](
(1/2 2CartesianPair[CartesianIndex[j],CartesianMomentum[-p2R]]CSP[c3,-p2R]-
	(1/2)2/3CartesianPair[CartesianIndex[j],
		CartesianMomentum[c3]]CSP[-p2R])SS[-I]
	- I(1/2 2CSP[c3,-p2R](-1)Eps[CartesianIndex[j],CartesianMomentum[-p2R],
		CartesianMomentum[ST[-I]]]+
	-(1/2)(1)2/3CSP[-p2R](-1)Eps[CartesianIndex[j],CartesianMomentum[c3],
	CartesianMomentum[ST[-I]]])))+
NRQCDProp[p2R+kgR]*(
	1/2(2CSP[ST[-I],p1R]CSP[c3,p1R]-
	2/3CSP[ST[-I],c3]CSP[p1R])*NRQCDScalarInsertions[{p2R,kgR},1]+
	NRQCDVectorInsertions[i,{p2R,kgR}]KD[i,j](
	(1/2 2CV[p1R,j]CSP[p1R,c3]-(-1/2)(-1) 2/3CV[c3,j]CSP[p1R])SS[-I]
	+I(1/2 2CSP[c3,p1R](-1)Eps[CartesianIndex[j],CartesianMomentum[p1R],
		CartesianMomentum[ST[-I]]]+
	-(1/2)(1)2/3CSP[p1R](-1)Eps[CartesianIndex[j],CartesianMomentum[c3],
	CartesianMomentum[ST[-I]]])))
)//ExpandScalarProduct//EpsEvaluate//Contract[#,EpsContract->False]&;


allInsertionsJ1=((insertion0+insertion1+insertion2+insertion3)
)//Contract[#,EpsContract->False]&//switchMomenta//
	ReplaceAll[#,Dispatch[{CartesianMomentum[q1]->
	SoftScale q1vabs CartesianMomentum[q1vhat],
	CartesianMomentum[q2]->
	SoftScale q2vabs CartesianMomentum[q2vhat]}]]&//
	DotSimplify[#,Expanding->False]&//PowerExpand//
	Series[#,{SoftScale,0,2}]&//Normal//Cancel//
	Collect2[#,{SoftScale,q2vabs}]&;


(* ::Subsection::Closed:: *)
(*Color singlet operators*)


auxCS= (
	I(- SMP["g_s"])(CSP[c1,Polarization[kgR,-I,
		Transversality->True]]SS[-I]/QMass )+
	I(-SMP["g_s"])(2 CSP[q1,Polarization[kgR,-I,
		Transversality->True]] CSP[c2,ST[-I]] /QMass^2)+
	I (-SMP["g_s"])/QMass^2( CSP[q1,c3]CSP[ST[-I],
		Polarization[kgR,-I,Transversality->True]]+
	CSP[q1,ST[-I]]CSP[Polarization[kgR,-I,Transversality->True],c3]-
	2/3CSP[q1,Polarization[kgR,-I,Transversality->True]]CSP[ST[-I],c3])+
	I(-SMP["g_s"])( 2 CSP[q1,Polarization[kgR,-I,Transversality->True]]*
		CSP[c4,q1]+CSP[q1]CSP[c4,Polarization[kgR,-I,
		Transversality->True]])SS[-I]/QMass^3
 );


csOperatorsJ1=auxCS//Contract[#,EpsContract->False]&//switchMomenta//
	ReplaceAll[#,Dispatch[{
	CartesianMomentum[q1]->SoftScale q1vabs CartesianMomentum[q1vhat],
	CartesianMomentum[q2]->SoftScale q2vabs CartesianMomentum[q2vhat]}]]&//
	DotSimplify[#,Expanding->False]&//PowerExpand//
	Series[#,{SoftScale,0,2}]&//Normal//Cancel//
	Collect2[#,{SoftScale,q2vabs}]&;


(* ::Subsection::Closed:: *)
(*Color octet operators*)


auxCO=I(
	(* <H| psi^+ B^i chi |0>*)
	((-I*SMP["g_s"])/QMass^2)CLC[][d0,kgR,Polarization[kgR,
		-I,Transversality->True]]SS[-I]+

	(* <H| psi^+ E^i chi |0>*)
	((-I*SMP["g_s"])/QMass^2)Sqrt[CSP[kgR]]CSP[Polarization[kgR,
		-I,Transversality->True],d1]SS[-I]+

	(* <H| psi^+  1/2 [sigma x g ExD - sigma x D x E] chi |0>*)
	1/2(4SMP["g_s"]/QMass^3)Sqrt[CSP[kgR]]Eps[CartesianMomentum[d2],
		CartesianMomentum[ST[-I]],CartesianIndex[dummy1]](
		Eps[CartesianIndex[dummy1],CartesianMomentum[q1],
		CartesianMomentum[Polarization[kgR,-I,Transversality->True]]])+

	(* <H| psi^+ 1/2 (g sigma x BxD + sigma x D x B) chi |0>*)
	+1/2(4SMP["g_s"]/QMass^3)*Eps[CartesianMomentum[d3],
		CartesianMomentum[ST[-I]],CartesianIndex[dummy1]](
		Eps[CartesianIndex[dummy1],CartesianMomentum[q1],
		CartesianIndex[dummy2]]Eps[CartesianIndex[dummy2],
		CartesianMomentum[kgR],CartesianMomentum[Polarization[kgR,-I,
		Transversality->True]]])

	(* <H| psi^+ I/2 g(DxE + ExD) chi |0> , d4*)
	+I/2(-2 SMP["g_s"]/QMass^3)Sqrt[CSP[kgR]]
	(CLC[][d4,kgR,Polarization[kgR,-I,Transversality->True]])SS[-I]

	(* <H| psi^+ I/2 g(DxB + BxD) chi |0>, d5*)
	+I/2(-2SMP["g_s"]/QMass^3)*(Eps[CartesianMomentum[d5],
		CartesianMomentum[kgR],CartesianIndex[dummy1]]*
		Eps[CartesianIndex[dummy1],CartesianMomentum[kgR],
		CartesianMomentum[Polarization[kgR,-I,Transversality->True]]])SS[-I]

	(* <H| psi^+ 1/3 g sigma (D.E + E.D) chi |0> d6*)
	+1/3*4(SMP["g_s"]/QMass^3)Sqrt[CSP[kgR]]CSP[q1,
		Polarization[kgR,-I,Transversality->True]]CSP[d6,ST[-I]]

	(* 1/3 <H| psi^+ g sigma (D.B + B.D) chi |0> d7 *)
	+1/3 4(SMP["g_s"]/QMass^3)CLC[][q1,kgR,Polarization[kgR,
		-I,Transversality->True]]CSP[d7,ST[-I]]

	(* <H| psi^+ g sigma^j (E^(i) D^(j) + E^(i) D^(j) ) chi |0> d8*)
	+(2SMP["g_s"]/QMass^3)Sqrt[CSP[kgR]]*(CSP[d8,Polarization[kgR,
		-I,Transversality->True]]CSP[ST[-I],q1]+
	CSP[ST[-I],Polarization[kgR,-I,Transversality->True]]CSP[d8,q1]-
	2/3CSP[d8,ST[-I]]CSP[q1,Polarization[kgR,-I,Transversality->True]])

	(* <H| psi^+ g sigma^j (B^(i) D^(j) + B^(i) D^(j) ) chi |0> d9*)
	+2(SMP["g_s"]/QMass^3)(CSP[d9,q1]CLC[][ST[-I],kgR,
	Polarization[kgR,-I,Transversality->True]]+CSP[ST[-I],
	q1]CLC[][d9,kgR,Polarization[kgR,-I,Transversality->True]]+
	1/3CSP[d9,ST[-I]]CLC[][-2q1,kgR,Polarization[kgR,-I,
	Transversality->True]])
);


coOperatorsJ1=auxCO//Contract[#,EpsContract->False]&//switchMomenta//
	ReplaceAll[#,Dispatch[{CartesianMomentum[q1]->
	SoftScale q1vabs CartesianMomentum[q1vhat],
	CartesianMomentum[q2]->
		SoftScale q2vabs CartesianMomentum[q2vhat]}]]&//
		DotSimplify[#,Expanding->False]&//PowerExpand//
		Series[#,{SoftScale,0,2}]&//Normal//Cancel//
		Collect2[#,{SoftScale,q2vabs}]&;


ampLCDA$J1[0]=(
CSP[c0,ST[-I]]+(1/QMass)CSP[c1,q]SS[-I]+
(1/QMass^2)CSP[c2,ST[-I]]CSP[q,q]+
(1/QMass^2)(CSP[c3,q]CSP[q,ST[-I]]-1/3CSP[c3,ST[-I]]CSP[q,q])+
(1/QMass^3)CSP[c4,q]CSP[q,q]SS[-I]+
(1/QMass^4)CSP[c5,ST[-I]]CSP[q,q]^2+
(1/QMass^4)(CSP[c6,q]CSP[q,ST[-I]]-1/3CSP[c6,ST[-I]]CSP[q,q])CSP[q,q]
);


ampLCDA$J1[1]=Series[FCI[ampLCDA$J1[0]],{SoftScale,0,4}]//Normal


(* ::Subsection:: *)
(*Putting everything together*)


(* ::Text:: *)
(*Perturbative LCDA amplitude for the matching*)


ampLCDA$J1[0]=(csOperatorsJ1+coOperatorsJ1+  allInsertionsJ1);


(* ::Section:: *)
(*Matching to LCDA for J=1*)


(* ::Text:: *)
(*The matching is done order by order in qabs. Yet the determination of the tensor short distance coefficients is cumbersome to automatize.*)


(* ::Text:: *)
(*Usually, it is easier to look at the matching equation at the given order in qabs and *)
(*guess the correct short distance coefficient by first figuring out the tensor structure and*)
(*then fixing the scalar coefficients.*)


(* ::Subsection:: *)
(*0th order in SoftScale*)


nrqcdAmpJ1S0=Coefficient[ampLCDA$J1[0],SoftScale,0];
qcdAmpJ1S0=Coefficient[ampQCD$J1[1],SoftScale,0]/.SUNTF[__]->1;


(* ::Text:: *)
(*Check*)


qcdAmpJ1S0+ I*(Uncontract[nrqcdAmpJ1S0,c0,c1,CartesianPair->All]/.sdCoeff[c0]/.sdCoeff[c1]//Contract)//Simplify


(* ::Subsection:: *)
(*1st order in SoftScale*)


nrqcdAmpJ1S1=Coefficient[ampLCDA$J1[0],SoftScale,1];
qcdAmpJ1S1=Coefficient[ampQCD$J1[1],SoftScale,1]/.SUNTF[__]->1;


sdCoeff[d0]=CartesianPair[CartesianIndex[i_], CartesianMomentum[d0]] -> 
 (CartesianPair[CartesianIndex[i], CartesianMomentum[Polarization[kp, -I,
 Transversality -> True]]]*DF[-1/2 + x])/(2*SMP["m_Q"]);


sdCoeff[d1]=CartesianPair[CartesianIndex[i_], CartesianMomentum[d1]] -> 
 (DF[-1/2 + x]*Eps[CartesianIndex[i], CartesianMomentum[kphat], 
    CartesianMomentum[Polarization[kp, -I, 
    Transversality -> True]]])/(2*SMP["m_Q"]);


(* ::Text:: *)
(*Check*)


SelectNotFree2[qcdAmpJ1S1,SS]+I*(Uncontract[SelectNotFree2[nrqcdAmpJ1S1,SS],c0,
c1,d0,d1,CartesianPair->All]/.sdCoeff[c0]/.sdCoeff[c1]/.sdCoeff[d0]/.
sdCoeff[d1]//Contract)//Simplify


SelectNotFree2[qcdAmpJ1S1,ST]+  I*(Uncontract[SelectNotFree2[nrqcdAmpJ1S1,ST],
c0,c1,c2,c3,d0,d1,CartesianPair->All]/.sdCoeff[c0]/.sdCoeff[c1]/.
sdCoeff[c2]/.sdCoeff[c3]/.sdCoeff[d0]/.sdCoeff[d1]//Contract)//Simplify


(* ::Subsection:: *)
(*2nd order in SoftScale*)


nrqcdAmpJ1S2=Coefficient[ampLCDA$J1[0],SoftScale,2];
qcdAmpJ1S2=Coefficient[ampQCD$J1[1],SoftScale,2]/.SUNTF[__]->1;


sdCoeff[d4]=CartesianPair[CartesianIndex[i_], CartesianMomentum[d4]] -> 
 (CartesianPair[CartesianIndex[i], CartesianMomentum[Polarization[kp, -I, 
 Transversality -> True]]]*(-12*DF[-1/2 + x] - 
 Derivative[2][DF][-1/2 + x]))/(32*SMP["m_Q"]);


sdCoeff[d5]=CartesianPair[CartesianIndex[i_], CartesianMomentum[d5]] -> 
 (3*Eps[CartesianIndex[i], CartesianMomentum[kphat], CartesianMomentum[
     Polarization[kp, -I, Transversality -> True]]]*(5*DF[-1/2 + x] + Derivative[2][DF][-1/2 + x]))/
  (80*SMP["m_Q"]);


sdCoeff[c2]=FCI[CV[c2, i_]] -> (CV[Polarization[kp, -I, Transversality -> True], i]*
   (-20*DF[-1/2 + x] + Derivative[2][DF][-1/2 + x]))/(48*SMP["m_Q"])


sdCoeff[c3]=FCI[CV[c3, i_]] -> (CV[Polarization[kp, -I, Transversality -> True], i]*
   (20*DF[-1/2 + x] - Derivative[2][DF][-1/2 + x]))/(80*SMP["m_Q"])


(* ::Text:: *)
(*Check*)


diffJ1S2=SelectNotFree2[qcdAmpJ1S2,SS]+  
I*(Uncontract[SelectNotFree2[nrqcdAmpJ1S2,SS],c0,c1,c2,c3,
c4,d0,d1,d4,d5,CartesianPair->All]/.sdCoeff[c0]/.sdCoeff[c1]/.
	sdCoeff[c2]/.sdCoeff[c3]/.sdCoeff[c4]/.sdCoeff[d0]/.
	sdCoeff[d1]/.sdCoeff[d4]/.sdCoeff[d5]//Contract)//Simplify


(* ::Text:: *)
(*The remaining difference vanishes by Schouten's identity*)


(*vanishes by Schouten*)
FMCartesianSchoutenBruteForce[diffJ1S2,{kphat,kphat,q1vhat,q1vhat,
q2vhat,q2vhat,Polarization[kp,-I,Transversality->True],
Polarization[kgR,-I,Transversality->True]}]//
	FMCartesianSchoutenBruteForce[#,{kphat,kphat,q1vhat,q1vhat,
	q2vhat,q2vhat,Polarization[kp,-I,Transversality->True],
Polarization[kgR,-I,Transversality->True]}]&//Simplify


sdCoeff[d2]=CartesianPair[CartesianIndex[i_], CartesianMomentum[d2]] -> 
 -(CartesianPair[CartesianIndex[i], CartesianMomentum[Polarization[kp, -I, 
 Transversality -> True]]]*(16*DF[-1/2 + x] + 
 Derivative[2][DF][-1/2 + x]))/(128*SMP["m_Q"]);


sdCoeff[d3]=CartesianPair[CartesianIndex[i_], CartesianMomentum[d3]] -> 
 (-3*DF[-1/2 + x]*Eps[CartesianIndex[i], CartesianMomentum[kphat], 
    CartesianMomentum[Polarization[kp, -I,
    Transversality -> True]]])/(32*SMP["m_Q"]);


sdCoeff[d6]=CartesianPair[CartesianIndex[i_], CartesianMomentum[d6]] -> 
 -(CartesianPair[CartesianIndex[i], CartesianMomentum[Polarization[kp, -I, 
 Transversality -> True]]]*
    (56*DF[-1/2 + x] - Derivative[2][DF][-1/2 + x]))/(128*SMP["m_Q"]);


sdCoeff[d7]=CartesianPair[CartesianIndex[i_], CartesianMomentum[d7]] -> 
 (Eps[CartesianIndex[i], CartesianMomentum[kphat], CartesianMomentum[
     Polarization[kp, -I, Transversality -> True]]]*(-12*DF[-1/2 + x] + 
    Derivative[2][DF][-1/2 + x]))/(64*SMP["m_Q"]);


sdCoeff[d8]=CartesianPair[CartesianIndex[i_], CartesianMomentum[d8]] -> 
 -(CartesianPair[CartesianIndex[i], CartesianMomentum[Polarization[kp, -I, 
 Transversality -> True]]]*
    (-80*DF[-1/2 + x] + Derivative[2][DF][-1/2 + x]))/(640*SMP["m_Q"]);


sdCoeff[d9]=CartesianPair[CartesianIndex[i_], CartesianMomentum[d9]] -> 
 (Eps[CartesianIndex[i], CartesianMomentum[kphat], CartesianMomentum[
     Polarization[kp, -I, Transversality -> True]]]*(-15*DF[-1/2 + x] - 
    2*Derivative[2][DF][-1/2 + x]))/(160*SMP["m_Q"]);


SelectNotFree2[qcdAmpJ1S2,ST]+  
	I*(Uncontract[SelectNotFree2[nrqcdAmpJ1S2,ST],c0,c1,c2,c3,d2,d3,
	d6,d7,d8,d9,CartesianPair->All]/.sdCoeff[c0]/.sdCoeff[c1]/.
	sdCoeff[c2]/.sdCoeff[c3]/.sdCoeff[d2]/.sdCoeff[d3]/.
	sdCoeff[d6]/.sdCoeff[d7]/.sdCoeff[d8]/.sdCoeff[d9]//Contract)//Simplify


(* ::Section:: *)
(*Consistency check for the short distance coefficients*)


(* ::Text:: *)
(*Set of the final short distance coefficients*)


finalSdCoeffs={sdCoeff[d0],sdCoeff[d1],sdCoeff[d2],sdCoeff[d3],
sdCoeff[d4],sdCoeff[d5],sdCoeff[d6],sdCoeff[d7],sdCoeff[d8],sdCoeff[d9]};


diff=Contract[Uncontract[I ampLCDA$J1[0],c0,c1,c2,c3,c4,d0,d1,d2,d3,d4,d5,
d6,d7,d8,d9,CartesianPair->All]/.sdCoeff[c0]/.sdCoeff[c1]/.sdCoeff[c2]/.
	sdCoeff[c3]/.sdCoeff[c4]/.finalSdCoeffs]+(ampQCD$J1[1]/.SUNTF[__]->1)//Simplify;


check=(FMCartesianSchoutenBruteForce[diff,{kphat,kphat,q1vhat,
q1vhat,q2vhat,q2vhat,Polarization[kp,-I,Transversality->True],
Polarization[kgR,-I,Transversality->True]}])//Simplify


FCCompareResults[{check},{0},
Text->{"\tExpanded QCD and LCD amplitudes match exactly:",
"CORRECT.","WRONG!"}, Interrupt->{Hold[Quit[1]],Automatic}];


(* ::Text:: *)
(*The d - coefficients are related to the one' s in the paper (Eqs. 22 in 1907.06473) in the following way :*)


(* ::Text:: *)
(*d0 ~ tilde {c} _B up to the polarization vector*)
(*d6 is tilde {c} _ {DE_ 0} up to the polarization vector*)
(*d2 is tilde {c} _ {DE_ 1} up to the polarization vector*)
(*d4 is tilde {c} _ {DE_ 1'} up to the polarization vector*)
(*d8 is tilde {c} _ {DE_ 2'} up to the polarization vector*)


(* ::Section:: *)
(*Check the final results*)


knownResult ={CartesianPair[CartesianIndex[i_], CartesianMomentum[d0]] -> 
  (CartesianPair[CartesianIndex[i], CartesianMomentum[Polarization[kp, -I, 
       Transversality -> True]]]*DF[-1/2 + x])/(2*SMP["m_Q"]), 
 CartesianPair[CartesianIndex[i_], CartesianMomentum[d1]] -> 
  (DF[-1/2 + x]*Eps[CartesianIndex[i], CartesianMomentum[kphat], 
     CartesianMomentum[Polarization[kp, -I, Transversality -> True]]])/
   (2*SMP["m_Q"]), CartesianPair[CartesianIndex[i_], CartesianMomentum[d2]] -> 
  -(CartesianPair[CartesianIndex[i], CartesianMomentum[Polarization[kp, -I, 
        Transversality -> True]]]*(16*DF[-1/2 + x] + Derivative[2][DF][
       -1/2 + x]))/(128*SMP["m_Q"]), 
 CartesianPair[CartesianIndex[i_], CartesianMomentum[d3]] -> 
  (-3*DF[-1/2 + x]*Eps[CartesianIndex[i], CartesianMomentum[kphat], 
     CartesianMomentum[Polarization[kp, -I, Transversality -> True]]])/
   (32*SMP["m_Q"]), CartesianPair[CartesianIndex[i_], CartesianMomentum[d4]] -> 
  (CartesianPair[CartesianIndex[i], CartesianMomentum[Polarization[kp, -I, 
       Transversality -> True]]]*(-12*DF[-1/2 + x] - 
     Derivative[2][DF][-1/2 + x]))/(32*SMP["m_Q"]), 
 CartesianPair[CartesianIndex[i_], CartesianMomentum[d5]] -> 
  (3*Eps[CartesianIndex[i], CartesianMomentum[kphat], 
     CartesianMomentum[Polarization[kp, -I, Transversality -> True]]]*
    (5*DF[-1/2 + x] + Derivative[2][DF][-1/2 + x]))/(80*SMP["m_Q"]), 
 CartesianPair[CartesianIndex[i_], CartesianMomentum[d6]] -> 
  -(CartesianPair[CartesianIndex[i], CartesianMomentum[Polarization[kp, -I, 
        Transversality -> True]]]*(56*DF[-1/2 + x] - Derivative[2][DF][
       -1/2 + x]))/(128*SMP["m_Q"]), 
 CartesianPair[CartesianIndex[i_], CartesianMomentum[d7]] -> 
  (Eps[CartesianIndex[i], CartesianMomentum[kphat], 
     CartesianMomentum[Polarization[kp, -I, Transversality -> True]]]*
    (-12*DF[-1/2 + x] + Derivative[2][DF][-1/2 + x]))/(64*SMP["m_Q"]), 
 CartesianPair[CartesianIndex[i_], CartesianMomentum[d8]] -> 
  -(CartesianPair[CartesianIndex[i], CartesianMomentum[Polarization[kp, -I, 
        Transversality -> True]]]*(-80*DF[-1/2 + x] + 
      Derivative[2][DF][-1/2 + x]))/(640*SMP["m_Q"]), 
 CartesianPair[CartesianIndex[i_], CartesianMomentum[d9]] -> 
  (Eps[CartesianIndex[i], CartesianMomentum[kphat], 
     CartesianMomentum[Polarization[kp, -I, Transversality -> True]]]*
    (-15*DF[-1/2 + x] - 2*Derivative[2][DF][-1/2 + x]))/(160*SMP["m_Q"])};
FCCompareResults[finalSdCoeffs,knownResult,
Text->{"\tCompare to Eqs. 22 in 1907.06473:",
"CORRECT.","WRONG!"}, Interrupt->{Hold[Quit[1]],Automatic}];
Print["\tCPU Time used: ", Round[N[TimeUsed[],4],0.001], " s."];



