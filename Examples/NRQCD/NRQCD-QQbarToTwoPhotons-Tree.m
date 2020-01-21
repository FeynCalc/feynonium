(* ::Package:: *)

(* :Title: NRQCD-QQbarToTwoPhotons-Tree.m                            *)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2017 Vladyslav Shtabovenko
*)

(* :Summary:   Computation of the tree-level matching between QCD and
			NRQCD for the exlusive electromagnetic decay of a heavy
			quarkonium into two photons using NRQCD factorization at
			the amplitude level. *)

(* ------------------------------------------------------------------------ *)


(* ::Section:: *)
(*Tree-level matching between QCD and NRQCD for *)
(*QQbar -> 2 gamma*)


(* ::Subsection:: *)
(*Load FeynCalc, FeynArts and FeynHelpers*)


If[ $FrontEnd === Null,
		$FeynCalcStartupMessages = False;
		Print["Computation of the tree-level matching between QCD and \
NRQCD for the exlusive electromagnetic decay of a heavy quarkonium \
into two photons using NRQCD factorization at the amplitude level."];
];
$LoadAddOns={"FeynArts","FeynOnium"};
<<FeynCalc`
$FAVerbose=0;


(* ::Subsection:: *)
(*Generate Feynman diagrams*)


diags=InsertFields[CreateTopologies[0,2->2],{F[3,{2,SUNFIndex[col1]}],
	-F[3,{2,SUNFIndex[col2]}]}->{V[1],V[1]},InsertionLevel->{Classes}];
Paint[diags,ColumnsXRows->{2,1},Numbering->None,SheetHeader->False,
ImageSize->{512,256}];


amps=((3/2)^2SMP["e_Q"]^2*FCFAConvert[CreateFeynAmp[diags,Truncated->False,
PreFactor->-1],IncomingMomenta->{p1,p2},OutgoingMomenta->{k1,k2},
UndoChiralSplittings->True,List->False,
TransversePolarizationVectors->{k1,k2},
ChangeDimension->4,List->True,SMP->True,
FinalSubstitutions->{SMP["m_c"]->SMP["m_Q"],
SUNFDelta[__]:>1}])//Contract


(* ::Subsection:: *)
(*On-shell kinematics*)


QMass=SMP["m_Q"];
QCharge=SMP["e_Q"];


FCClearScalarProducts[];
SP[k1, k1] = 0;
SP[k2, k2] = 0;
SP[p1, p1] = QMass^2;
SP[p2, p2] = QMass^2;


TemporalMomentum[Polarization[k1|k2,___]]=0;
TC[q]=0;
TC[p1]=Eq;
TC[p2]=Eq;
TC[k1]=kabs;
TC[k2]=kabs;
CSP[khat,Polarization[k1,-I,Transversality->True]]=0;
CSP[khat,Polarization[k2,-I,Transversality->True]]=0;
CSP[khat,khat]=1;
CSP[qhat,qhat]=1;
CSP[qhatp,qhatp]=1;
CartesianMomentum[k1]:=kabs CartesianMomentum[khat];
CartesianMomentum[k2]:=-kabs CartesianMomentum[khat];
CartesianMomentum[p1]:=qabs CartesianMomentum[qhat];
CartesianMomentum[p2]:=-qabs CartesianMomentum[qhat];
CartesianMomentum[q]:=qabs CartesianMomentum[qhat];
CartesianMomentum[qp]:=qabs CartesianMomentum[qhatp];
CartesianMomentum[aux]=0;
Eq=Series[Sqrt[qabs^2+QMass^2],{qabs,0,4}]//Normal//PowerExpand;
kabs=Eq;


(* ::Subsection:: *)
(*Evaluation of the QCD amplitude, nonrelativistic normalization*)


(* ::Text:: *)
(**)


(*Simplify the Dirac algebra, rewrite Dirac chains in terms of Pauli 
chains and decompose all 4 - vectors into temporal components and 
3-vectors*)


AbsoluteTiming[amps2=amps//DiracSimplify//FMSpinorChainExplicit2[#,
	FMSpinorNormalization->"nonrelativistic"]&//Contract//
	FeynAmpDenominatorExplicit//LorentzToCartesian;]//First


(* ::Text:: *)
(*Expand in qabs up to 4th order*)


AbsoluteTiming[amps3=amps2//EpsEvaluate//ExpandScalarProduct//
	DotSimplify//Series[#,{qabs,0,4}]&//Normal;]//First


(* ::Text:: *)
(*Prepare the amplitude for angular projections*)


AbsoluteTiming[amps4=amps3//ReplaceAll[#,
PauliEta[-I].PauliSigma[x_].PauliXi[I]:>
	CartesianPair[CartesianMomentum[ST],x]]&//Collect2[#,
	{ST,PauliXi,PauliEta,qhat}]&;]//First


(* ::Text:: *)
(*Project out J=0,1,2 contributions*)


ampQCDJ0=FMCartesianTensorDecomposition[amps4,{qhat,ST},0]//
Collect2[#,qhat,ST,qabs]&;
ampQCDJ1=FMCartesianTensorDecomposition[amps4,{qhat,ST},1]//
Collect2[#,qhat,ST,qabs]&;
ampQCDJ2tmp=FMCartesianTensorDecomposition[amps4,{qhat,ST},2]//
Collect2[#,qhat,ST,qabs]&;


(* ::Text:: *)
(*As expected, there is no J = 1 contribution*)


ampQCDJ1===0


(* ::Text:: *)
(*The J = 2 contribution can be further simplified using Schouten identity in 3 dimensions*)


ampQCDJ2=FixedPoint[FMCartesianSchoutenBruteForce[#,{khat,khat,
qhat,qhat,Polarization[k1,-I,Transversality->True], 
Polarization[k2,-I,Transversality->True]},FCVerbose->-1]&,ampQCDJ2tmp];


(* ::Text:: *)
(*Final QCD amplitudes for matching*)


ampQCDJ0
ampQCDJ1
ampQCDJ2


(* ::Subsection:: *)
(*Evaluation of the NRQCD amplitude, nonrelativistic normalization*)


(* ::Text:: *)
(**)


(*Tell FeynCalc that the J=2 short distance coefficients should be 
treated as tensors.This is important to make Uncontract work with 
these objects.*)


DataType[c1J2,FCTensor]=True;
DataType[c2J2,FCTensor]=True;
DataType[c3J2,FCTensor]=True;
DataType[c4J2,FCTensor]=True;
DataType[c5J2,FCTensor]=True;


(* ::Text:: *)
(*Convenient shortcuts for entering parts of the J=2 NRQCD amplitude*)


symmTraceless1[i_,j_]:=FCI[CV[q,i]CV[ST,j]/2+CV[q,j]CV[ST,i]/2-
1/3 KD[i,j]CSP[q,ST]];
symmTraceless2[i_,j_]:=FCI[CV[q,i]CV[q,j]-1/3 KD[i,j]CSP[q,q]];


(* ::Text:: *)
(*Final NRQCD amplitudes for matching*)


ampNRQCDJ0=((c0J0/QMass) PauliEta[-I].PauliXi[I]+
(c1J0/QMass^2)CSP[q,ST]+
(c2J0/QMass^3)CSP[q,q]PauliEta[-I].PauliXi[I]+
(c3J0/QMass^4)CSP[q,ST]CSP[q,q]+
(c4J0/QMass^5)CSP[q,q]^2 PauliEta[-I].PauliXi[I])//FCI;


ampNRQCDJ2=((1/QMass^2)c1J2[CartesianIndex[i],CartesianIndex[j]]*
symmTraceless1[i,j]+
(1/QMass^3)c2J2[CartesianIndex[i],CartesianIndex[j]]symmTraceless2[i,j]*
PauliEta[-I].PauliXi[I]+
(1/QMass^4)c3J2[CartesianIndex[i],CartesianIndex[j]]symmTraceless1[i,j]*
CSP[q,q]+
(1/QMass^5)c4J2[CartesianIndex[i],CartesianIndex[j]]symmTraceless2[i,j]*
CSP[q,q]PauliEta[-I].PauliXi[I]+
(1/QMass^4)c5J2[CartesianIndex[i],CartesianIndex[j]](symmTraceless2[i,j]*
CSP[q,ST]-
2/5 symmTraceless1[i,j]CSP[q,q]))//Contract;


(* ::Subsection:: *)
(*Matching QCD to NRQCD*)


(* ::Subsubsection:: *)
(*J=0*)


(* ::Text:: *)
(*The determination of the scalar short distance coefficients is easy*)


tmp=(Coefficient[ampQCDJ0,qabs,0]==Coefficient[ampNRQCDJ0,qabs,0])
sdCoeff[c0J0]=Solve[tmp,c0J0]//Flatten


tmp=(Coefficient[ampQCDJ0,qabs,1]==Coefficient[ampNRQCDJ0,qabs,1])
sdCoeff[c1J0]=Solve[tmp,c1J0]//Flatten


tmp=(Coefficient[ampQCDJ0,qabs,2]==Coefficient[ampNRQCDJ0,qabs,2])
sdCoeff[c2J0]=Solve[tmp,c2J0]//Flatten


tmp=(Coefficient[ampQCDJ0,qabs,3]==Coefficient[ampNRQCDJ0,qabs,3])
sdCoeff[c3J0]=Solve[tmp,c3J0]//Flatten


tmp=(Coefficient[ampQCDJ0,qabs,4]==Coefficient[ampNRQCDJ0,qabs,4])
sdCoeff[c4J0]=Solve[tmp,c4J0]//Flatten


(* ::Subsubsection:: *)
(*J=2*)


(* ::Text:: *)
(*The determination of the tensor short distance coefficients is cumbersome to automatize.*)


(*Usually, it is easier to look at the equality A_QCD =  A_NRQCD at the 
given order in qabs and guess the correct short distance coefficient.*)


sdCoeff[c1J2]={c1J2[CartesianIndex[i_],CartesianIndex[j_]]->
FCI[- I(CV[Polarization[k2,-I,Transversality->True],j]*
CV[Polarization[k1,-I,Transversality->True],i]+CV[Polarization[k2,-I,
Transversality->True],i] CV[Polarization[k1,-I,Transversality->True],j]+
CV[khat,i] CSP[Polarization[k2,-I,Transversality->True],
	Polarization[k1,-I,Transversality->True]] CV[khat,j])*
	SMP["e"]^2 QCharge^2]}


sdCoeff[c2J2]={c2J2[CartesianIndex[i_],CartesianIndex[j_]]->
-CV[khat,i] CV[khat,j] SMP["e"]^2 QCharge^2 CLC[][khat,
Polarization[k1,-I,Transversality->True],Polarization[k2,-I,
Transversality->True]]}


sdCoeff[c3J2]={c3J2[CartesianIndex[i_],CartesianIndex[j_]]->
1/5 I (3 CSP[Polarization[k1,-I,Transversality->True],
Polarization[k2,-I,Transversality->True]] CV[khat,i] CV[khat,j]+
5 CV[Polarization[k1,-I,Transversality->True],j] *
CV[Polarization[k2,-I,Transversality->True],i]+
5 CV[Polarization[k1,-I,Transversality->True],i] CV[Polarization[k2,-I,
	Transversality->True],j]) SMP["e"]^2 QCharge^2}


sdCoeff[c4J2]={c4J2[CartesianIndex[i_],CartesianIndex[j_]]->
FCI[8/7 CV[khat,i] CV[khat,j] SMP["e"]^2 QCharge^2 *
CLC[][khat,Polarization[k1,-I,Transversality->True],
Polarization[k2,-I,Transversality->True]]]}


sdCoeff[c5J2]={c5J2[CartesianIndex[i_],CartesianIndex[j_]]->
	FCI[1/42 I (-17 CSP[Polarization[k1,-I,Transversality->True],
Polarization[k2,-I,Transversality->True]] CV[khat,i] CV[khat,j]+
25 CV[Polarization[k1,-I,Transversality->True],j] CV[Polarization[k2,-I,
Transversality->True],i]+25 CV[Polarization[k1,-I,
Transversality->True],i] CV[Polarization[k2,-I,
	Transversality->True],j]) SMP["e"]^2 QCharge^2]};


(* ::Subsection:: *)
(*Consistency check for the short distance coefficients*)


(* ::Text:: *)
(*Let us check that our short distance coefficients are correct,  i.e. that we have A_QCD - A_NRQCD = 0 order by order in qabs*)


AmpQCDMinusAmpNRQCDJ0=Simplify[(ampNRQCDJ0/.sdCoeff[c0J0]/.sdCoeff[c1J0]
/.sdCoeff[c2J0]/.sdCoeff[c3J0]/.sdCoeff[c4J0])-ampQCDJ0]


AmpQCDMinusAmpNRQCDJ2=Simplify[Contract[Uncontract[ampNRQCDJ2,All]/.
sdCoeff[c1J2]/.sdCoeff[c2J2]/.sdCoeff[c3J2]/.sdCoeff[c4J2]/.
sdCoeff[c5J2]]-ampQCDJ2]


(* ::Subsection:: *)
(*List of the obtained short-distance coefficients*)


sdCoeff[c0J0]
sdCoeff[c1J0]
sdCoeff[c2J0]
sdCoeff[c3J0]
sdCoeff[c4J0]


sdCoeff[c1J2]
sdCoeff[c2J2]
sdCoeff[c3J2]
sdCoeff[c4J2]
sdCoeff[c5J2]


(* ::Subsection:: *)
(*Final matching coefficients*)


(* ::Text:: *)
(**)


(*Decay rates according to Eqs. 2.39-2.42 from arXiv:hep-ph/0604190, 
omitting matrix elements that contain chromoelectric or chromomagnetic 
fields*)


decayRateEtaC= 2im[{"f_em","1S0"}]/QMass^2 PauliEta[-I].PauliXi[I] *
PauliXi[-I].PauliEta[I]+
2im[{"g_em","1S0"}]/QMass^2 qabs^2 PauliEta[-I].PauliXi[I] *
PauliXi[-I].PauliEta[I]+
2im[{"h'_em","1S0"}]/QMass^4 qabs^4 PauliEta[-I].PauliXi[I] *
PauliXi[-I].PauliEta[I]+
2im[{"h''_em","1S0"}]/QMass^4 qabs^4 PauliEta[-I].PauliXi[I] *
PauliXi[-I].PauliEta[I];


decayRateChiC0= (2im[{"f_em","3P0"}]/QMass^4 qabs^2 CSP[qhat,ST]*
CSP[qhatp,STcc]/3+2im[{"g_em","3P0"}]/QMass^6 qabs^4 CSP[qhat,ST]*
CSP[qhatp,STcc]/3)//FCI;


decayRateChiC2= (2im[{"f_em","3P2"}]/QMass^4 symmTraceless1[i,j]*
(symmTraceless1[i,j]/.{qhat->qhatp,ST->STcc}) +
2im[{"g_em","3P2"}]/QMass^6 qabs^2 symmTraceless1[i,j]*
(symmTraceless1[i,j]/.{qhat->qhatp,ST->STcc}))//Contract;


(* ::Text:: *)
(*These LDMEs do not appear in the decay formulas for eta_c or chi_c, but the corresponding *)
(*contributions do appear on the QCD side of the matching, since they are allowed by symmetries.*)
(*Therefore, when matching QCD and NRQCD amplitudes/decay rates to each other, we must also*)
(*include these LDMEs*)


extraLDMEs=(2im[{"g_em","3P2,3F2"}]/QMass^6 *
Contract[(1/2symmTraceless2[i,j]CSP[q,ST]-
1/5 symmTraceless1[i,j]CSP[q,q])(symmTraceless1[i,j]/.
{qhat->qhatp,ST->STcc})+
(( 1/2symmTraceless2[i,j]CSP[qp,ST]- 1/5 symmTraceless1[i,j]CSP[q,q])/.
{qhat->qhatp,ST->STcc})(symmTraceless1[i,j])])+
2im[{"h_em","1D2"}]/QMass^6 Contract[symmTraceless2[i,j]*
(symmTraceless2[i,j]/.{qhat->qhatp,ST->STcc})];


repRuleJ0=Join[sdCoeff[c0J0],sdCoeff[c1J0],sdCoeff[c2J0],sdCoeff[c3J0],
sdCoeff[c4J0]];
repRuleJ0cc=ComplexConjugate[repRuleJ0];
repRuleJ2=Join[sdCoeff[c1J2],sdCoeff[c2J2],sdCoeff[c3J2],sdCoeff[c4J2],
sdCoeff[c5J2]];
repRuleJ2cc=(rd[#[[1]],ComplexConjugate[#[[2]]]]&/@repRuleJ2)/.
rd->Rule;


decayRateNRQCDJ0pert=Series[ampNRQCDJ0 ComplexConjugate[ampNRQCDJ0//.
{qhat->qhatp,ST->STcc}/.{h:c0J0|c1J0|c2J0|c3J0|c4J0:>Conjugate[h]}],
{qabs,0,4}]//Normal;
decayRateNRQCDJ2pert=(Series[ampNRQCDJ2 ComplexConjugate[ampNRQCDJ2//.
{qhat->qhatp,ST->STcc}/.
{(h:c1J2|c2J2|c3J2|c4J2|c5J2)[x__]:>h["cc",x]}],{qabs,0,4}]//Normal//
Uncontract[#,All]&)//FMCartesianTensorDecomposition[#,
{qhat,qhatp,ST,STcc},0]&//Uncontract[#,All]&;


getMatchingCoeffJ0[n_]:=(1/(16Pi))(Coefficient[decayRateNRQCDJ0pert,qabs,n]/.
{Conjugate[x_]:>(x/.ComplexConjugate[repRuleJ0])}/.repRuleJ0/.
{SMP["e"]->2Sqrt[Pi SMP["alpha_fs"]]})//DoPolarizationSums[#,k1,aux]&//
DoPolarizationSums[#,k2,aux]&//LorentzToCartesian//Simplify


getMatchingCoeffJ2[n_]:=(1/(16Pi))(Coefficient[decayRateNRQCDJ2pert,qabs,n]/.
{(h:c1J2|c2J2|c3J2|c4J2|c5J2)["cc",x__]:>(h[x]/.repRuleJ2cc)}/.repRuleJ2/.
{SMP["e"]->2Sqrt[Pi SMP["alpha_fs"]]})//DoPolarizationSums[#,k1,aux]&//
DoPolarizationSums[#,k2,aux]&//LorentzToCartesian//Simplify


(* ::Text:: *)
(*This precisely reproduces Eqs. 3.4-3.12 from arXiv:hep-ph/0604190*)


Solve[SelectFree2[getMatchingCoeffJ0[0],ST]==
	Coefficient[decayRateEtaC,qabs,0],{im[{"f_em","1S0"}]}]
Solve[SelectFree2[getMatchingCoeffJ0[2],ST]==
	Coefficient[decayRateEtaC,qabs,2],{im[{"g_em","1S0"}]}]
Solve[SelectNotFree2[getMatchingCoeffJ0[2],ST]==
	Coefficient[decayRateChiC0,qabs,2],{im[{"f_em","3P0"}]}]
Solve[SelectNotFree2[getMatchingCoeffJ2[2],ST]==
	(Coefficient[decayRateChiC2,qabs,2]),{im[{"f_em","3P2"}]}]
Solve[SelectFree2[getMatchingCoeffJ2[4],ST]==
	Coefficient[SelectFree[extraLDMEs,ST],qabs,4],{im[{"h_em","1D2"}]}]
Solve[SelectFree2[getMatchingCoeffJ0[4],ST]==
	Coefficient[decayRateEtaC,qabs,4],{im[{"h'_em","1S0"}]}]
Solve[SelectNotFree2[getMatchingCoeffJ0[4],ST]==
	Coefficient[decayRateChiC0,qabs,4],{im[{"g_em","3P0"}]}]
Solve[SelectNotFree2[getMatchingCoeffJ2[4],ST]==
	((Coefficient[decayRateChiC2+SelectNotFree2[extraLDMEs,ST],qabs,4])/.
		{im[{"g_em","3P2,3F2"}]->-20/21 SMP["alpha_fs"]^2 SMP["e_Q"]^4 Pi
}),{im[{"g_em","3P2"}]}]


(* ::Subsection:: *)
(*Check with the known results*)


Print["Check with the known results: ",
			If[{AmpQCDMinusAmpNRQCDJ0,AmpQCDMinusAmpNRQCDJ2}==={0,0}, 
			"CORRECT.", "!!! WRONG !!!"]];
