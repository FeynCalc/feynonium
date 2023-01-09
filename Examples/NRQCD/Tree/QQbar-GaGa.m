(* ::Package:: *)

(* :Title: QQbar-GaGa															*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2014-2023 Vladyslav Shtabovenko
*)

(* :Summary:  Q Qbar -> Ga Ga, NRQCD, matching, tree					*)

(* ------------------------------------------------------------------------ *)


(* ::Title:: *)
(*Exclusive electromagnetic decays of heavy quarkonia into 2 photons in NRQCD*)


(* ::Section:: *)
(*Load FeynCalc and the necessary add-ons or other packages*)


description="Q Qbar -> Ga Ga, NRQCD, matching, tree";
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
(*Generate Feynman diagrams*)


(* ::Text:: *)
(*Nicer typesetting*)


MakeBoxes[p1,TraditionalForm]:="\!\(\*SubscriptBox[\(p\), \(1\)]\)";
MakeBoxes[p2,TraditionalForm]:="\!\(\*SubscriptBox[\(p\), \(2\)]\)";
MakeBoxes[k1,TraditionalForm]:="\!\(\*SubscriptBox[\(k\), \(1\)]\)";
MakeBoxes[k2,TraditionalForm]:="\!\(\*SubscriptBox[\(k\), \(2\)]\)";


diags=InsertFields[CreateTopologies[0,2->2],{F[3,{2,SUNFIndex[col1]}],
	-F[3,{2,SUNFIndex[col2]}]}->{V[1],V[1]},InsertionLevel->{Classes}];

Paint[diags,ColumnsXRows->{2,1},Numbering->None,SheetHeader->False,
ImageSize->{512,256}];


(* ::Section:: *)
(*Obtain the amplitude*)


amp[0] = FCFAConvert[CreateFeynAmp[diags,
	Truncated->False,PreFactor->-1],IncomingMomenta->{p1,p2},
	OutgoingMomenta->{k1,k2},UndoChiralSplittings->True,
	TransversePolarizationVectors->{k1,k2,k3},ChangeDimension->4,
	List->True,SMP->True,DropSumOver->True,
	FinalSubstitutions->{SMP["m_c"]->SMP["m_Q"],SUNFDelta[__]:>1}];


(* ::Text:: *)
(*Introduce heavy quark charge and perform index contractions*)


amp[1] = Contract[(3/2)^2 SMP["e_Q"]^2 amp[0]];


(* ::Section:: *)
(*Fix the kinematics*)


mQ=SMP["m_Q"];
eQ=SMP["e_Q"];


(* ::Text:: *)
(*All particles are on-shell*)


FCClearScalarProducts[];
SP[k1, k1] = 0;
SP[k2, k2] = 0;
SP[p1, p1] = mQ^2;
SP[p2, p2] = mQ^2;


(* ::Text:: *)
(*Eq is the the zero component of the heavy quark momenta. Here it is sufficient to expand it to*)
(*4th order in the relative momentum |q|*)


Eq=Series[Sqrt[qabs^2+mQ^2],{qabs,0,4}]//Normal//PowerExpand;


(* ::Text:: *)
(*Temporal components of 4-momenta*)


TemporalMomentum[Polarization[k1|k2,___]]=0;
TC[q]=0;
TC[n]=1;
TC[p1]=Eq;
TC[p2]=Eq;
TC[k1]=kabs;
TC[k2]=kabs;


(* ::Text:: *)
(*Cartesian scalar products*)


CSP[khat,Polarization[k1,-I,Transversality->True]]=0;
CSP[khat,Polarization[k2,-I,Transversality->True]]=0;
CSP[khat,Polarization[k1,I,Transversality->True]]=0;
CSP[khat,Polarization[k2,I,Transversality->True]]=0;
CSP[khat,khat]=1;
CSP[qhat,qhat]=1;
CSP[qhatp,qhatp]=1;


(* ::Text:: *)
(*Extract absolute values of Cartesian 3-momenta*)


CartesianMomentum[k1]:=kabs CartesianMomentum[khat];
CartesianMomentum[k2]:=-kabs CartesianMomentum[khat];
CartesianMomentum[p1]:=qabs CartesianMomentum[qhat];
CartesianMomentum[p2]:=-qabs CartesianMomentum[qhat];
CartesianMomentum[q]:=qabs CartesianMomentum[qhat];
CartesianMomentum[qp]:=qabs CartesianMomentum[qhatp]
CartesianMomentum[n]=0;


(* ::Text:: *)
(*The absolute values of the photon 3-momenta |k1| and |k2| equal Eq*)


kabs=Eq;


(* ::Section:: *)
(*Expand the amplitude*)


(* ::Text:: *)
(*After having simplified the Dirac algebra we can rewrite the spinor chains in terms of nonrelativistic quantities*)


amp[2]=amp[1]//DiracSimplify//
FMSpinorChainExplicit2[#,FMNormalization->"nonrelativistic"]&;


(* ::Text:: *)
(*Decompose all 4-vectors into temporal components and 3-vectors*)


amp[3]=amp[2]//FeynAmpDenominatorExplicit//LorentzToCartesian;


(* ::Text:: *)
(*Expand in qabs up to 4th order*)


amp[4]=amp[3]//ExpandScalarProduct//DotSimplify//
Series[#,{qabs,0,4}]&//Normal;


(* ::Text:: *)
(*Pauli algebra simplifications*)


amp[5]=amp[4]//PauliSimplify[#,PauliReduce->True]&;


(* ::Text:: *)
(*Substitute Pauli chains containing a single Pauli matrix with a 3-vector ST*)


amp[6]=Collect2[Total[amp[5]],PauliSigma]//
	ReplaceAll[#,{PauliEta[-I].PauliSigma[x_].PauliXi[I]:>
	CartesianPair[CartesianMomentum[ST[I]],x]}]&;


(* ::Text:: *)
(*Project out J = 0, 1, 2 contributions*)


ampQCD$J0[0]=FMCartesianTensorDecomposition[amp[6],{qhat,ST[I]},0]//
Collect2[#,qhat,ST,qabs]&;


ampQCD$J1[0]=FMCartesianTensorDecomposition[amp[6],{qhat,ST[I]},1]//
Collect2[#,qhat,ST,qabs]&;


ampQCD$J2[0]=FMCartesianTensorDecomposition[amp[6],{qhat,ST[I]},2]//
Collect2[#,qhat,ST,qabs]&;


FCCompareResults[{ampQCD$J1[0]},{0},
Text->{"\tThe J=1 contribution is forbidden by the Landau-Yang theorem:",
"CORRECT.","WRONG!"}, Interrupt->{Hold[Quit[1]],Automatic}];


(* ::Text:: *)
(*The J = 2 contribution can be further simplified using Schouten identity in 3 dimensions*)


ampQCD$J2[1]=FixedPoint[FMCartesianSchoutenBruteForce[#,{khat,khat,
qhat,qhat,Polarization[k1,-I,Transversality->True], 
Polarization[k2,-I,Transversality->True]}]&,ampQCD$J2[0]];


ampQCD$J0[1]=ampQCD$J0[0];


(* ::Section:: *)
(*Enter NRQCD amplitudes*)


(* ::Text:: *)
(*Tell FeynCalc that the J=2 short distance coefficients should be  treated as tensors.*)
(*This is important to make Uncontract work with these symbols.*)


DataType[c1J2,FCTensor]=True;
DataType[c2J2,FCTensor]=True;
DataType[c3J2,FCTensor]=True;
DataType[c4J2,FCTensor]=True;
DataType[c5J2,FCTensor]=True;


(* ::Text:: *)
(*Convenient shortcuts for entering parts of the J=2 NRQCD amplitude*)


symmTraceless1[i_,j_]:=
	FCI[CV[q,i]CV[ST[I],j]/2+CV[q,j]CV[ST[I],i]/2-1/3 KD[i,j]CSP[q,ST[I]]];
symmTraceless2[i_,j_]:=
	FCI[CV[q,i]CV[q,j]-1/3 KD[i,j]CSP[q,q]];


(* ::Text:: *)
(*Perturbative NRQCD amplitudes for matching*)


ampNRQCD$J0[0]=((c0J0[I]/mQ) PauliEta[-I].PauliXi[I]+
(c1J0[I]/mQ^2)CSP[q,ST[I]]+
(c2J0[I]/mQ^3)CSP[q,q]PauliEta[-I].PauliXi[I]+
(c3J0[I]/mQ^4)CSP[q,ST[I]]CSP[q,q]+
(c4J0[I]/mQ^5)CSP[q,q]^2 PauliEta[-I].PauliXi[I])//FCI;


ampNRQCD$J2[0]=((1/mQ^2)c1J2[I,CartesianIndex[i],CartesianIndex[j]]*
symmTraceless1[i,j]+
(1/mQ^3)c2J2[I,CartesianIndex[i],CartesianIndex[j]]symmTraceless2[i,j]*
PauliEta[-I].PauliXi[I]+
(1/mQ^4)c3J2[I,CartesianIndex[i],CartesianIndex[j]]symmTraceless1[i,j]*
CSP[q,q]+
(1/mQ^5)c4J2[I,CartesianIndex[i],CartesianIndex[j]]symmTraceless2[i,j]*
CSP[q,q]PauliEta[-I].PauliXi[I]+
(1/mQ^4)c5J2[I,CartesianIndex[i],CartesianIndex[j]](symmTraceless2[i,j]*
CSP[q,ST[I]]-
2/5 symmTraceless1[i,j]CSP[q,q]))//Contract;


(* ::Section:: *)
(*Matching between QCD and NRQCD amplitudes*)


(* ::Subsection:: *)
(*J=0*)


(* ::Text:: *)
(*The matching is done order by order in qabs*)


tmp=(Coefficient[ampQCD$J0[1],qabs,0]==Coefficient[ampNRQCD$J0[0],qabs,0])
sdCoeff[c0J0]=Solve[tmp,c0J0[I]]//Flatten


tmp=(Coefficient[ampQCD$J0[1],qabs,1]==Coefficient[ampNRQCD$J0[0],qabs,1])
sdCoeff[c1J0]=Solve[tmp,c1J0[I]]//Flatten


tmp=(Coefficient[ampQCD$J0[1],qabs,2]==Coefficient[ampNRQCD$J0[0],qabs,2])
sdCoeff[c2J0]=Solve[tmp,c2J0[I]]//Flatten


tmp=(Coefficient[ampQCD$J0[1],qabs,3]==Coefficient[ampNRQCD$J0[0],qabs,3])
sdCoeff[c3J0]=Solve[tmp,c3J0[I]]//Flatten


tmp=(Coefficient[ampQCD$J0[1],qabs,4]==Coefficient[ampNRQCD$J0[0],qabs,4])
sdCoeff[c4J0]=Solve[tmp,c4J0[I]]//Flatten


(* ::Subsection:: *)
(*J=2*)


(* ::Text:: *)
(*The determination of the tensor short distance coefficients is cumbersome to automatize.*)
(**)
(*Usually, it is easier to look at the matching equation at the given order in qabs and *)
(*guess the correct short distance coefficient by first figuring out the tensor structure and*)
(*then fixing the scalar coefficients.*)
(**)


sdCoeff[c1J2]={c1J2[I,CartesianIndex[i_],CartesianIndex[j_]]->
FCI[- I(CV[Polarization[k2,-I,Transversality->True],j]*
CV[Polarization[k1,-I,Transversality->True],i]+CV[Polarization[k2,-I,
Transversality->True],i] CV[Polarization[k1,-I,Transversality->True],j]+
CV[khat,i] CSP[Polarization[k2,-I,Transversality->True],
	Polarization[k1,-I,Transversality->True]] CV[khat,j])*
	SMP["e"]^2 eQ^2]}


sdCoeff[c2J2]={c2J2[I,CartesianIndex[i_],CartesianIndex[j_]]->
-CV[khat,i] CV[khat,j] SMP["e"]^2 eQ^2 CLC[][khat,
Polarization[k1,-I,Transversality->True],Polarization[k2,-I,
Transversality->True]]}


sdCoeff[c3J2]={c3J2[I,CartesianIndex[i_],CartesianIndex[j_]]->
1/5 I (3 CSP[Polarization[k1,-I,Transversality->True],
Polarization[k2,-I,Transversality->True]] CV[khat,i] CV[khat,j]+
5 CV[Polarization[k1,-I,Transversality->True],j] *
CV[Polarization[k2,-I,Transversality->True],i]+
5 CV[Polarization[k1,-I,Transversality->True],i] CV[Polarization[k2,-I,
	Transversality->True],j]) SMP["e"]^2 eQ^2}


sdCoeff[c4J2]={c4J2[I,CartesianIndex[i_],CartesianIndex[j_]]->
FCI[8/7 CV[khat,i] CV[khat,j] SMP["e"]^2 eQ^2 *
CLC[][khat,Polarization[k1,-I,Transversality->True],
Polarization[k2,-I,Transversality->True]]]}


sdCoeff[c5J2]={c5J2[I,CartesianIndex[i_],CartesianIndex[j_]]->
	FCI[1/42 I (-17 CSP[Polarization[k1,-I,Transversality->True],
Polarization[k2,-I,Transversality->True]] CV[khat,i] CV[khat,j]+
25 CV[Polarization[k1,-I,Transversality->True],j] CV[Polarization[k2,-I,
Transversality->True],i]+25 CV[Polarization[k1,-I,
Transversality->True],i] CV[Polarization[k2,-I,
	Transversality->True],j]) SMP["e"]^2 eQ^2]}


(* ::Section:: *)
(*Consistency check for the short distance coefficients*)


check1=Simplify[(ampNRQCD$J0[0]/.sdCoeff[c0J0]/.sdCoeff[c1J0]
/.sdCoeff[c2J0]/.sdCoeff[c3J0]/.sdCoeff[c4J0])-ampQCD$J0[1]]


check2=Simplify[Contract[Uncontract[ampNRQCD$J2[0],All]/.
sdCoeff[c1J2]/.sdCoeff[c2J2]/.sdCoeff[c3J2]/.sdCoeff[c4J2]/.
sdCoeff[c5J2]]-ampQCD$J2[1]]


FCCompareResults[{check1,check2},{0,0},
Text->{"\tExpanded QCD and NRQCD amplitudes match exactly:",
"CORRECT.","WRONG!"}, Interrupt->{Hold[Quit[1]],Automatic}];


(* ::Section:: *)
(*Final matching coefficients*)


(* ::Text:: *)
(*NRQCD decay rates for eta_c, chi_c0 and chi_c2 according to Eqs. 2.39-2.42 from hep-ph/0604190,  omitting matrix elements that contain chromoelectric or chromomagnetic fields*)


decayRateEtaC= 2im[{"f_em","1S0"}]/mQ^2 PauliEta[-I].PauliXi[I] *
PauliXi[-I].PauliEta[I]+
2im[{"g_em","1S0"}]/mQ^2 qabs^2 PauliEta[-I].PauliXi[I] *
PauliXi[-I].PauliEta[I]+
2im[{"h'_em","1S0"}]/mQ^4 qabs^4 PauliEta[-I].PauliXi[I] *
PauliXi[-I].PauliEta[I]+
2im[{"h''_em","1S0"}]/mQ^4 qabs^4 PauliEta[-I].PauliXi[I] *
PauliXi[-I].PauliEta[I]


decayRateChiC0= (2im[{"f_em","3P0"}]/mQ^4 qabs^2 CSP[qhat,ST[I]]*
CSP[qhatp,ST[-I]]/3+2im[{"g_em","3P0"}]/mQ^6 qabs^4 CSP[qhat,ST[I]]*
CSP[qhatp,ST[-I]]/3)//FCI


decayRateChiC2= (2im[{"f_em","3P2"}]/mQ^4 symmTraceless1[i,j]*
(symmTraceless1[i,j]/.{qhat->qhatp,ST[I]->ST[-I]}) +
2im[{"g_em","3P2"}]/mQ^6 qabs^2 symmTraceless1[i,j]*
(symmTraceless1[i,j]/.{qhat->qhatp,ST[I]->ST[-I]}))//Contract


(* ::Text:: *)
(*These LDMEs do not appear in the decay formulas for eta_c or chi_c, but the corresponding *)
(*contributions do appear on the QCD side of the matching, since they are allowed by symmetries.*)
(*Therefore, when matching QCD and NRQCD amplitudes/decay rates to each other, we must also*)
(*include these LDMEs*)


extraLDMEs=(2im[{"g_em","3P2,3F2"}]/mQ^6 *
Contract[(1/2symmTraceless2[i,j]CSP[q,ST[I]]-
1/5 symmTraceless1[i,j]CSP[q,q])(symmTraceless1[i,j]/.
{qhat->qhatp,ST[I]->ST[-I]})+
(( 1/2symmTraceless2[i,j]CSP[qp,ST[I]]- 1/5 symmTraceless1[i,j]CSP[q,q])/.
{qhat->qhatp,ST[I]->ST[-I]})(symmTraceless1[i,j])])+
2im[{"h_em","1D2"}]/mQ^6 Contract[symmTraceless2[i,j]*
(symmTraceless2[i,j]/.{qhat->qhatp,ST[I]->ST[-I]})]*PauliEta[-I].PauliXi[I] *
PauliXi[-I].PauliEta[I]


(* ::Text:: *)
(*Combine all J=0 and J=2 SDCs obtained so far into single replacement rules*)


repRuleJ0=Join[sdCoeff[c0J0],sdCoeff[c1J0],sdCoeff[c2J0],sdCoeff[c3J0],
sdCoeff[c4J0]];
repRuleJ2=Join[sdCoeff[c1J2],sdCoeff[c2J2],sdCoeff[c3J2],sdCoeff[c4J2],
sdCoeff[c5J2]];


(* ::Text:: *)
(*We also need replacement rules for c.c. versions of the SDCs*)


{repRuleJ0cc,repRuleJ2cc}=
	{repRuleJ0,repRuleJ2}/.Rule[a_,b_]:>Rule[ComplexConjugate[a],ComplexConjugate[b]];


(* ::Text:: *)
(*Calculate perturbative decay rates for J=0 and J=2 by squaring the corresponding NRQCD amplitudes*)


prefac=(1/(16Pi));


decayRateNRQCD$J0[0]=prefac Series[ampNRQCD$J0[0] ComplexConjugate[ampNRQCD$J0[0]/.
	{qhat->qhatp}],{qabs,0,4}]//Normal;


decayRateNRQCD$J2[0]=prefac Series[ampNRQCD$J2[0] ComplexConjugate[ampNRQCD$J2[0]/.
{qhat->qhatp}],{qabs,0,4}]//Normal//Uncontract[#,All]&//
FMCartesianTensorDecomposition[#,{qhat,qhatp,ST[I],ST[-I]},0]&//FCCanonicalizeDummyIndices;


decayRateNRQCD$J0[1]=decayRateNRQCD$J0[0]//ReplaceAll[#,repRuleJ0]&//ReplaceAll[#,repRuleJ0cc]&//
	DoPolarizationSums[#,k1,n]&//DoPolarizationSums[#,k2,n]&//LorentzToCartesian//Together//
	Collect2[#,qabs]&//ReplaceAll[#,SMP["e"]->2Sqrt[Pi SMP["alpha_fs"]]]&


decayRateNRQCD$J2[1]=decayRateNRQCD$J2[0]//ReplaceAll[#,repRuleJ2]&//ReplaceAll[#,repRuleJ2cc]&//
	DoPolarizationSums[#,k1,n]&//DoPolarizationSums[#,k2,n]&//LorentzToCartesian//
	Together//Collect2[#,qabs]&//ReplaceAll[#,SMP["e"]->2Sqrt[Pi SMP["alpha_fs"]]]&


(* ::Text:: *)
(*Matching coefficients for etc_c*)


mcRes1=Solve[SelectFree2[Coefficient[decayRateNRQCD$J0[1],qabs,0],ST]==
	Coefficient[decayRateEtaC,qabs,0],im[{"f_em", "1S0"}]]//First
mcRes2=Solve[SelectFree2[Coefficient[decayRateNRQCD$J0[1],qabs,2],ST]==
	Coefficient[decayRateEtaC,qabs,2],im[{"g_em", "1S0"}]]//First
mcRes3=Solve[SelectFree2[Coefficient[decayRateNRQCD$J0[1],qabs,4],ST]==
	Coefficient[decayRateEtaC,qabs,4],im[{"h'_em", "1S0"}]]//First


(* ::Text:: *)
(*Matching coefficients for chi_c0*)


mcRes4=Solve[SelectNotFree2[Coefficient[decayRateNRQCD$J0[1],qabs,2],ST]==
	Coefficient[decayRateChiC0,qabs,2],im[{"f_em", "3P0"}]]//First
mcRes5=Solve[SelectNotFree2[Coefficient[decayRateNRQCD$J0[1],qabs,4],ST]==
	Coefficient[decayRateChiC0,qabs,4],im[{"g_em", "3P0"}]]//First


(* ::Text:: *)
(*Lowest order matching coefficient for chi_c0*)


mcRes6=Solve[SelectNotFree2[Coefficient[decayRateNRQCD$J2[1],qabs,2],ST]==
	Coefficient[decayRateChiC2,qabs,2],im[{"f_em", "3P2"}]]//First


(* ::Text:: *)
(*One of the additional matching coefficients*)


mcRes7=Solve[SelectFree2[Coefficient[decayRateNRQCD$J2[1],qabs,4],ST]==
	SelectFree2[Coefficient[extraLDMEs,qabs,4],ST],im[{"h_em","1D2"}]]//First


(* ::Text:: *)
(*To resolve the last matching coefficients we need to combine contributions from the extra matching coefficients*)
(*and chi_c2*)


tmp=Collect2[Coefficient[decayRateChiC2+SelectNotFree2[extraLDMEs,ST],qabs,4]-
SelectNotFree2[Coefficient[decayRateNRQCD$J2[1],qabs,4],ST],qhat,ST];
tmp2=(SelectFree[#,qhat,ST]&/@(List@@tmp)//Union);
mcRes8=Solve[Map[Equal[#,0]&,tmp2],{im[{"g_em","3P2,3F2"}],im[{"g_em","3P2"}]}]//First


finalMCs=Join[mcRes1,mcRes2,mcRes3,mcRes4,mcRes5,mcRes6,mcRes7,mcRes8]//Sort;


finalMCs//TableForm


(* ::Section:: *)
(*Check the final results*)


knownResult = {im[{"f_em", "1S0"}] -> Pi*SMP["alpha_fs"]^2*SMP["e_Q"]^4, 
	im[{"f_em", "3P0"}] -> 3*Pi*SMP["alpha_fs"]^2*SMP["e_Q"]^4, 
 im[{"f_em", "3P2"}] -> (4*Pi*SMP["alpha_fs"]^2*SMP["e_Q"]^4)/5, 
 im[{"g_em", "1S0"}] -> (-4*Pi*SMP["alpha_fs"]^2*SMP["e_Q"]^4)/(3*SMP["m_Q"]^2), 
 im[{"g_em", "3P0"}] -> -7*Pi*SMP["alpha_fs"]^2*SMP["e_Q"]^4, 
 im[{"g_em", "3P2"}] -> (-8*Pi*SMP["alpha_fs"]^2*SMP["e_Q"]^4)/5, 
 im[{"g_em", "3P2,3F2"}] -> (-20*Pi*SMP["alpha_fs"]^2*SMP["e_Q"]^4)/21, 
 im[{"h'_em", "1S0"}] -> (68*Pi*SMP["alpha_fs"]^2*SMP["e_Q"]^4 - 
 45*im[{"h''_em", "1S0"}]*SMP["m_Q"]^2)/
   (45*SMP["m_Q"]^2), im[{"h_em", "1D2"}] -> (2*Pi*SMP["alpha_fs"]^2*SMP["e_Q"]^4)/15};
FCCompareResults[finalMCs,knownResult,
Text->{"\tCompare to Eqs. 3.4-3.12 in hep-ph/0604190:",
"CORRECT.","WRONG!"}, Interrupt->{Hold[Quit[1]],Automatic}];
Print["\tCPU Time used: ", Round[N[TimeUsed[],4],0.001], " s."];



