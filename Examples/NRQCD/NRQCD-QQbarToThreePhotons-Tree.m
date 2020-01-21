(* ::Package:: *)

(* :Title: NRQCD-QQbarToThreePhotons-Tree.m                            *)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2017 Vladyslav Shtabovenko
*)

(* :Summary:   Computation of the tree-level matching between QCD and
			NRQCD for the exlusive electromagnetic decay of a J/Psi
			into three photons using NRQCD factorization at
			the level of total decay rates. *)

(* ------------------------------------------------------------------------ *)


(* ::Section:: *)
(*Tree-level matching between QCD and NRQCD for QQbar -> 3 gamma*)


(* ::Subsection:: *)
(*Load FeynCalc, FeynArts and FeynOnium*)


If[ $FrontEnd === Null,
		$FeynCalcStartupMessages = False;
		Print["Computation of the tree-level matching between QCD \
and NRQCD for the exlusive electromagnetic decay of a J/Psi into three
photons using NRQCD factorization at the level of total decay rates."];
];
$LoadAddOns={"FeynArts","FeynOnium"};
<<FeynCalc`
$FAVerbose=0;


(* ::Subsection:: *)
(*Generate Feynman diagrams*)


diags=InsertFields[CreateTopologies[0,2->3],{F[3,{2}],
-F[3,{2}]}->{V[1],V[1],V[1]},InsertionLevel->{Classes},Model->"SMQCD"];
Paint[diags,ColumnsXRows->{3,2},Numbering->None,
SheetHeader->False,ImageSize->{756,512}];


ampsRaw=((3/2)^3 SMP["e_Q"]^3*FCFAConvert[CreateFeynAmp[diags,
Truncated->False,PreFactor->-1],IncomingMomenta->{p1,p2},
OutgoingMomenta->{k1,k2,k3},UndoChiralSplittings->True,List->False,
TransversePolarizationVectors->{k1,k2,k3},ChangeDimension->4,
List->True,SMP->True,DropSumOver->True,
FinalSubstitutions->{SMP["m_c"]->SMP["m_Q"],SUNFDelta[__]:>1}])//Contract


(* ::Text:: *)
(*Eliminate k3 using momentum conservation*)


amps=(MomentumExpand[ampsRaw]/.Momentum[k3]->Momentum[p1+p2-k1-k2])//
MomentumExpand


(* ::Subsection:: *)
(*On-shell kinematics*)


QMass=SMP["m_Q"];
QCharge=SMP["e_Q"];


FCClearScalarProducts[];
SP[k1, k1] = 0;
SP[k2, k2] = 0;
SP[k3, k3] = 0;
SP[p1, p1] = QMass^2;
SP[p2, p2] = QMass^2;


TemporalMomentum[Polarization[k1|k2|k3,___]]=0;
TC[q]=0;
TC[p1]=Eq;
TC[p2]=Eq;
TC[k1]=k1abs;
TC[k2]=k2abs;
TC[k3]=k3abs;
TC[aux]=1;
CSP[k1hat,Polarization[k1,-I]]=0;
CSP[k2hat,Polarization[k2,-I]]=0;
CSP[k3hat,Polarization[k3,-I]]=0;
CSP[k1hat,k1hat]=1;
CSP[k2hat,k2hat]=1;
CSP[k3hat,k3hat]=1;
CSP[k1hat,k2hat]=1/(k1abs k2abs) (2 Eq^2-2  Eq (k1abs+k2abs)+ k1abs*k2abs);
CartesianMomentum[k1]:=k1abs CartesianMomentum[k1hat];
CartesianMomentum[k2]:=k2abs CartesianMomentum[k2hat];
CartesianMomentum[k3]:=k3abs CartesianMomentum[k3hat];
CartesianMomentum[p1]:=qabs CartesianMomentum[qhat];
CartesianMomentum[p2]:=-qabs CartesianMomentum[qhat];
CartesianMomentum[q]:=qabs CartesianMomentum[qhat];
CartesianMomentum[aux]=0;

Eq=Series[Sqrt[qabs^2+QMass^2],{qabs,0,0}]//Normal//PowerExpand;
k1abs=Eq x1;
k2abs=Eq x2;


(* ::Subsection:: *)
(*Calculation of the total decay rate in QCD*)


(* ::Text:: *)
(*Simplify the Dirac algebra, rewrite Dirac chains in terms of Pauli chains and decompose all 4 - vectors into temporal components and 3 - vectors*)


AbsoluteTiming[amps2=amps//DiracSimplify//
FMSpinorChainExplicit2[#,FMSpinorNormalization->"nonrelativistic"]&//
Contract//FeynAmpDenominatorExplicit//LorentzToCartesian;]//First


(* ::Text:: *)
(*Expand in qabs up to 0th order*)


AbsoluteTiming[amps3=amps2//EpsEvaluate//ExpandScalarProduct//DotSimplify//
Series[#,{qabs,0,0}]&//Normal;]//First


(* ::Text:: *)
(*Extract the spin triplet contribution*)


AbsoluteTiming[ampST=Collect2[SelectNotFree2[amps3,PauliSigma],
PauliSigma,Polarization,FCFactorOut->QCharge^3]//
ReplaceAll[#,{PauliEta[-I].PauliSigma[x_].PauliXi[I]:>
CartesianPair[CartesianMomentum[ST],x],
PauliXi[-I].PauliSigma[x_].PauliEta[I]:>
CartesianPair[CartesianMomentum[STcc],x]}]&;]//First


(* ::Text:: *)
(*Compute amplitude squared*)


AbsoluteTiming[ampSTSquared1=(ComplexConjugate[ampST/.ST->STcc] ampST);]//
First


(* ::Text:: *)
(*Sum over polarizations of the photons*)


AbsoluteTiming[ampSTSquared2=ampSTSquared1//DoPolarizationSums[#,k1,aux]&//
DoPolarizationSums[#,k2,aux]&//
DoPolarizationSums[#,k3,aux]&//LorentzToCartesian//Collect2[#,{ST,STcc}]&;]//First


(* ::Text:: *)
(*Eliminate k3hat*)


AbsoluteTiming[ampSTSquared3=ampSTSquared2//
Uncontract[#,k3hat,CartesianPair->All]&//
ReplaceRepeated[#,{CartesianMomentum[k3hat]:>
-k1abs/k3abs CartesianMomentum[k1hat]-
k2abs/k3abs CartesianMomentum[k2hat],k3abs->2Eq-k1abs-k2abs}]&//
ExpandScalarProduct//Contract//Collect2[#,k1hat,k2hat]&;]//First


(* ::Text:: *)
(*Average over k1hat and k2hat (corresponds to the angular integration)*)


AbsoluteTiming[ampSTSquared4=FMCartesianTensorDecomposition[ampSTSquared3,
{k1hat,k2hat},0]//Simplify;]//First


(* ::Text:: *)
(*Obtain the total decay rate*)


QCDDecayRate=ReplaceRepeated[QMass^2/(192 Pi^3)ampSTSquared4,{SMP["e"]->
2 Sqrt[Pi SMP["alpha_fs"]],
(x1^4+2 x1^3 (-2+x2)+(-1+x2)^2 (2-2 x2+x2^2)+x1^2 (7-9 x2+3 x2^2)+
x1 (-6+13 x2-9 x2^2+2 x2^3))/(x1^2 x2^2 (-2+x1+x2)^2)->1/2(Pi^2-9)}]


(* ::Text:: *)
(*FYI: This is how the integral over x1 and x2 is calculated*)


(*tmp=Integrate[(x1^4+2 x1^3 (-2+x2)+(-1+x2)^2 (2-2 x2+x2^2)+x1^2 (7-
9 x2+3 x2^2)+x1 (-6+13 x2-9 x2^2+2 x2^3))/(x1^2 x2^2 (-2+x1+x2)^2),
{x2,1-x1,1}]
Integrate[Normal[tmp],{x1,0,1}]*)


(* ::Subsection:: *)
(*Matching between QCD and NRQCD*)


(* ::Text:: *)
(*The total decay rate in NRQCD at leading order in velocity is simply*)


NRQCDDecayRate= 2ImFem3S1/QMass^2FCI[ CSP[ST,STcc]]


(* ::Text:: *)
(*Equating the two decay rates we can read off the value of the matching coefficient*)


matchingCoeff[ImFem3S1]=Solve[QCDDecayRate==NRQCDDecayRate,{ImFem3S1}]//
Flatten


(* ::Text:: *)
(*So that our final NRQCD factorized decay rate is given by*)


NRQCDDecayRateFinal=NRQCDDecayRate/.matchingCoeff[ImFem3S1]


(* ::Subsection:: *)
(*Check with the literature*)


resLit=(8 (-9+\[Pi]^2) CSP[ST,STcc] SMP["alpha_fs"]^3 SMP["e_Q"]^6)/
(9 SMP["m_Q"]^2);
Print["Check with Eq.1 in arXiv:1210.6337: ",
			If[FCI[resLit]-NRQCDDecayRateFinal===0,
			"CORRECT.", "!!! WRONG !!!"]];
