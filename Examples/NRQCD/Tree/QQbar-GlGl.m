(* ::Package:: *)

(* :Title: QQbar-GlGl															*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2014-2023 Vladyslav Shtabovenko
*)

(* :Summary:  Q Qbar -> Gl Gl, NRQCD, matching ST CS, tree			*)

(* ------------------------------------------------------------------------ *)


(* ::Title:: *)
(*Born contribution to the quarkonium decay into two gluons in NRQCD (spin triplet, color singlet)*)


(* ::Section:: *)
(*Load FeynCalc and the necessary add-ons or other packages*)


description="Q Qbar -> Gl Gl, NRQCD, matching ST CS, tree";
If[ $FrontEnd === Null,
	$FeynCalcStartupMessages =False;
	Print[description];
];
If[ $Notebooks === False,
	$FeynCalcStartupMessages = False
];
$LoadAddOns={"FeynArts", "FeynOnium","FeynHelpers"};
<<FeynCalc`
$FAVerbose = 0;

FCCheckVersion[9,3,1];


(* ::Section:: *)
(*Configure some options*)


FCSetDiracGammaScheme["BMHV"];


(* ::Section:: *)
(*Generate Feynman diagrams*)


(* ::Text:: *)
(*Nicer typesetting*)


MapThread[FCAttachTypesettingRule[#1,{SubscriptBox,"p",#2}]&,
{{p1,p2},Range[2]}];


MapThread[FCAttachTypesettingRule[#1,{SubscriptBox,"k",#2}]&,
{{k1,k2},Range[2]}];


diags=InsertFields[CreateTopologies[0,2->2],
	{F[3,{2,cq}],-F[3,{2,cqbar}]}->{V[5],V[5]},
	InsertionLevel->{Classes},Model->"SMQCD",
	ExcludeParticles->{S[_],V[2|3|4]}];

Paint[diags, ColumnsXRows->{2,2}, Numbering->Simple,
	SheetHeader->False,ImageSize->{512,512}];


(* ::Section:: *)
(*Obtain the amplitudes*)


amp[0] = FCFAConvert[CreateFeynAmp[diags,PreFactor->1], IncomingMomenta->{p1,p2},
	OutgoingMomenta->{k1,k2},UndoChiralSplittings->True,ChangeDimension->D,
	List->False, SMP->True, Contract->True,DropSumOver->True,
	TransversePolarizationVectors->{k1,k2},
		FinalSubstitutions->{SMP["m_c"]->SMP["m_Q"]}]//
	ReplaceAll[#,{SMP["g_s"]^2->(4Pi SMP["alpha_s"])}]&//
	SUNSimplify


(* ::Section:: *)
(*Fix the kinematics*)


FCClearScalarProducts[]


QMass=SMP["m_Q"];


(* ::Text:: *)
(*All particles are on-shell*)


FCClearScalarProducts[];
SPD[p1]=QMass^2;
SPD[p2]=QMass^2;
SPD[k1]=0;
SPD[k2]=0;


(* ::Text:: *)
(*At 0th order in the relative momentum q the kinematics is particularly simple*)


SPD[P,q]=0;
SPD[P]=4QMass^2;
SPD[P,k1]=2QMass^2;
SPD[P,k2]=2QMass^2;
SPD[q,k2]=-FCI@SPD[k1,q];
SPD[k1,k2]=2 QMass^2;


TC[P]=2QMass;
TC[p1]=QMass;
TC[p2]=QMass;


(* ::Text:: *)
(*This speeds up some expansions*)


Unprotect[Power];
\!\(\*
TagBox[
StyleBox[
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Power", "[", 
RowBox[{"QMass", ",", "2"}], "]"}], ",", 
RowBox[{"Rational", "[", 
RowBox[{"n_", ",", "2"}], "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\):=QMass^n;
Protect[Power];


(* ::Section:: *)
(*Extract the spin triplet color singlet contribution*)


(* ::Text:: *)
(*Here we apply the spin-triplet color singlet covariant projector*)


amp[1]=FMInsertCovariantProjector[amp[0],{p1,QMass},{p2,QMass},
	mu,{cq,cqbar},Dimension->D];


(* ::Text:: *)
(*The next step is to carry out the Dirac traces and simplify the color algebra*)


amp[2]=amp[1]//SUNSimplify[#,SUNNToCACF->False]&//
	DiracSimplify[#]&;


(* ::Text:: *)
(*Switch to the kinematic variables P and q*)


amp[3]=((ExpandScalarProduct[amp[2]//MomentumExpand]//.
{h_[p1,dim___]:>h[P,dim]/2+h[q,dim],
h_[p2,dim___]:>h[P,dim]/2-h[q,dim],EN->FCI[Sqrt[QMass^2-SPD[q]]]}
)//ExpandScalarProduct)/.EN->FCI[Sqrt[QMass^2-SPD[q]]]//Simplify;


(* ::Text:: *)
(*To extract the P-wave contribution at LO, we need to differentiate w.r.t to q and put q to zero*)
(*afterwards*)


amp[4]=FourDivergence[amp[3],FVD[q,nu]]//ReplaceAll[#,{q->0,P->k1+k2}]&//
	FeynAmpDenominatorExplicit//ExpandScalarProduct//
	ReplaceAll[#,{EN->QMass}]&//Simplify


(* ::Section:: *)
(*Square the amplitude*)


(* ::Text:: *)
(*Now we square the amplitude and use the suitable polarization tensor for the P-wave quarkonium*)


PiTensor[ind1_,ind2_]:=FCI[(-MTD[ind1,ind2]+
	FVD[P,ind1]FVD[P,ind2]/(4QMass^2))];
N0=1;
N1=(D-1)(D-2)/2;
N2=(D+1)(D-2)/2;
polSumJ0[mu1_,nu1_,mu2_,nu2_]:=1/(2N0) 1/(D-1)PiTensor[mu1,nu1]PiTensor[mu2,nu2]/.P->k1+k2;
polSumJ1[mu1_,nu1_,mu2_,nu2_]:=1/(2N1) (1/2(PiTensor[mu1,mu2]PiTensor[nu1,nu2]-PiTensor[mu1,nu2]PiTensor[mu2,nu1]))/.P->k1+k2
polSumJ2[mu1_,nu1_,mu2_,nu2_]:=1/(2N2) (1/2(PiTensor[mu1,mu2]PiTensor[nu1,nu2]+PiTensor[mu1,nu2]PiTensor[mu2,nu1])-
	1/(D-1)PiTensor[mu1,nu1]PiTensor[mu2,nu2])/.P->k1+k2


(* ::Text:: *)
(*This is a special function that handles the contractions with the polarization vectors of the quarkonium*)
(*and sums over the polarizations of the gluons.*)


ClearAll[calRVJ];
calRVJ[amp_,fun_]:=SUNSimplify[(amp ComplexConjugate[amp/.{mu->mu1,
	nu->nu1}])fun[mu,nu,mu1,nu1],
	SUNTrace->True,Explicit->True]//Contract//
	Collect2[#,Polarization,IsolateNames->KK]&//
	DoPolarizationSums[#,k1,k2]&//DoPolarizationSums[#,k2,k1]&


ampSquaredJ0[0]=calRVJ[amp[4],polSumJ0]//FRH//FCReplaceD[#,D->4-2Epsilon]&//Simplify
ampSquaredJ1[0]=calRVJ[amp[4],polSumJ1]//FRH
ampSquaredJ2[0]=calRVJ[amp[4],polSumJ2]//FRH//FCReplaceD[#,D->4-2Epsilon]&//Simplify


(* ::Section:: *)
(*Check the final results*)


(* ::Text:: *)
(*When comparing the results in hep-ph/9707223 we omit the phase-space prefactor Phi_(2) mu^(4 eps) and the LDME*)


knownResults = {
	144 CF SMP["alpha_s"]^2 Pi^2/QMass^4 (1-Epsilon)/(3-2Epsilon),
	0,
	32 CF SMP["alpha_s"]^2 Pi^2/QMass^4 (6-13 Epsilon+4Epsilon^2)/
		((3-2Epsilon)(5-2Epsilon))
};
FCCompareResults[({ampSquaredJ0[0],ampSquaredJ1[0],
ampSquaredJ2[0]}),
knownResults,
Text->{"\tCompare to Eqs. 242-244 in arXiv:hep-ph/9707223:",
"CORRECT.","WRONG!"}, Interrupt->{Hold[Quit[1]],Automatic}]
Print["\tCPU Time used: ", Round[N[TimeUsed[],3],0.001], " s."];



