(* ::Package:: *)

(* :Title: QQbar-GaGaGa															*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2014-2021 Vladyslav Shtabovenko
*)

(* :Summary:  Q Qbar -> Ga Ga Ga, NRQCD, matching, tree					*)

(* ------------------------------------------------------------------------ *)


(* ::Title:: *)
(*Exclusive electromagnetic decay of J/Psi into 3 photons in NRQCD*)


(* ::Section:: *)
(*Load FeynCalc and the necessary add-ons or other packages*)


description="Q Qbar -> Ga Ga Ga, NRQCD, matching, tree";
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
MakeBoxes[k3,TraditionalForm]:="\!\(\*SubscriptBox[\(k\), \(3\)]\)";


diags = InsertFields[CreateTopologies[0,2->3],{F[3,{2}],
-F[3,{2}]}->{V[1],V[1],V[1]},InsertionLevel->{Classes}];

Paint[diags, ColumnsXRows->{3,2},Numbering -> Simple,
SheetHeader->False,ImageSize->{640,512}];


(* ::Section:: *)
(*Obtain the amplitude*)


amp[0] = FCFAConvert[CreateFeynAmp[diags,
	Truncated->False,PreFactor->-1],IncomingMomenta->{p1,p2},
	OutgoingMomenta->{k1,k2,k3},UndoChiralSplittings->True,
	TransversePolarizationVectors->{k1,k2,k3},ChangeDimension->4,
	List->True,SMP->True,DropSumOver->True,
	FinalSubstitutions->{SMP["m_c"]->SMP["m_Q"],SUNFDelta[__]:>1}];


(* ::Text:: *)
(*Introduce heavy quark charge and perform index contractions*)


amp[1] = Contract[(3/2)^3 SMP["e_Q"]^3 amp[0]];


(* ::Text:: *)
(*Use momentum conservation to obtain more compact expressions*)


amp[2] = FCRerouteMomenta[amp[1],{p1,p2},{k1,k2,k3}]


(* ::Section:: *)
(*Fix the kinematics*)


mQ=SMP["m_Q"];
eQ=SMP["e_Q"];


(* ::Text:: *)
(*All particles are on-shell*)


FCClearScalarProducts[];
SP[k1, k1] = 0;
SP[k2, k2] = 0;
SP[k3, k3] = 0;
SP[p1, p1] = mQ^2;
SP[p2, p2] = mQ^2;


(* ::Text:: *)
(*Eq is the the zero component of the heavy quark momenta. Here it is sufficient to expand it to*)
(*0th order in the relative momentum |q|*)


Eq=Series[Sqrt[qabs^2+mQ^2],{qabs,0,0}]//Normal//PowerExpand;


(* ::Text:: *)
(*Temporal components of 4-momenta*)


TemporalMomentum[Polarization[k1|k2|k3,___]]=0;
TC[q]=0;
TC[p1]=Eq;
TC[p2]=Eq;
TC[k1]=k1abs;
TC[k2]=k2abs;
TC[k3]=2Eq-k1abs-k2abs;
TC[n]=1;


(* ::Text:: *)
(*Cartesian scalar products*)


CSP[k1hat,Polarization[k1,-I,Transversality->True]]=0;
CSP[k2hat,Polarization[k2,-I,Transversality->True]]=0;
CSP[k3hat,Polarization[k3,-I,Transversality->True]]=0;
CSP[k1hat,k1hat]=1;
CSP[k2hat,k2hat]=1;
CSP[k3hat,k3hat]=1;
CSP[k1hat,k2hat]=1/(k1abs k2abs) (2 Eq^2-2  Eq (k1abs+k2abs)+ k1abs*k2abs);


(* ::Text:: *)
(*Extract absolute values of Cartesian 3-momenta*)


CartesianMomentum[k1]:=k1abs CartesianMomentum[k1hat];
CartesianMomentum[k2]:=k2abs CartesianMomentum[k2hat];
CartesianMomentum[k3]:=-CartesianMomentum[k1]-CartesianMomentum[k2];
CartesianMomentum[p1]:=qabs CartesianMomentum[qhat];
CartesianMomentum[p2]:=-qabs CartesianMomentum[qhat];
CartesianMomentum[q]:=qabs CartesianMomentum[qhat];
CartesianMomentum[n]=0;


(* ::Text:: *)
(*The absolute values of the photon 3-momenta |k1| and |k2| also depend on Eq*)


k1abs=Eq x1;
k2abs=Eq x2;


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
(*Expand in qabs up to 0th order*)


amp[4]=amp[3]//ExpandScalarProduct//DotSimplify//
Series[#,{qabs,0,0}]&//Normal;


(* ::Text:: *)
(*Pauli algebra simplifications*)


amp[5]=amp[4]//PauliSimplify[#,PauliReduce->True]&;


(* ::Text:: *)
(*Keep only the spin triplet contribution.*)
(*Substitute Pauli chains containing a single Pauli matrix with a 3-vector ST*)


amp[6]=Collect2[Total[amp[5]],PauliSigma]//
SelectNotFree[#,PauliSigma]&//
ReplaceAll[#,{PauliEta[-I].PauliSigma[x_].PauliXi[I]:>
	CartesianPair[CartesianMomentum[ST[I]],x]}]&;


FreeQ[amp[6],PauliSigma]


(* ::Section:: *)
(*Square the amplitude*)


(* ::Text:: *)
(*Compute amplitude squared and sum over the polarizations of the *)
(*photons using auxiliary vector n=(1,0,0,0)^T*)


ampSquared[0] = amp[6] ComplexConjugate[amp[6]]//
	DoPolarizationSums[#,k1,n]&//
	DoPolarizationSums[#,k2,n]&//
	DoPolarizationSums[#,k3,n]&//ExpandScalarProduct//
	LorentzToCartesian//Collect2[#,ST]&;


(* ::Text:: *)
(*Average over k1hat and k2hat (corresponds to the angular integration in the phase space integral)*)


ampSquared[1]=FMCartesianTensorDecomposition[ampSquared[0],{k1hat,k2hat},0]


(* ::Section:: *)
(*Total decay rate*)


prefac=mQ^2/(192 Pi^3);


{aux1,aux2}=FCProductSplit[ampSquared[1],{x1,x2}]


(* ::Text:: *)
(*Here we replace the integral over x1 and x2 by the known result, the itself integral is calculated below*)


If[Together[aux2-((2 - 6*x1 + 7*x1^2 - 4*x1^3 + x1^4 - 6*x2 + 13*x1*x2 - 9*x1^2*x2 + 
	2*x1^3*x2 + 7*x2^2 - 9*x1*x2^2 + 3*x1^2*x2^2 - 
  4*x2^3 + 2*x1*x2^3 + x2^4)/(x1^2*x2^2*(-2 + x1 + x2)^2))]==0,
  decayRateTotalQCD=prefac*aux1*1/2(Pi^2-9)/.SMP["e"]->2 Sqrt[Pi SMP["alpha_fs"]]
]


(* ::Text:: *)
(*FYI: This is how the integral over x1 and x2 is calculated*)


(*tmp=Integrate[(x1^4+2 x1^3 (-2+x2)+(-1+x2)^2 (2-2 x2+x2^2)+x1^2 (7-
9 x2+3 x2^2)+x1 (-6+13 x2-9 x2^2+2 x2^3))/(x1^2 x2^2 (-2+x1+x2)^2),
{x2,1-x1,1}]
Integrate[Normal[tmp],{x1,0,1}]*)


(* ::Section:: *)
(*Matching from QCD to NRQCD*)


(* ::Text:: *)
(*The total decay rate in NRQCD at leading order in velocity is given by*)


decayRateTotalNRQCD[0]=2ImFem3S1/mQ^2FCI[ CSP[ST[I],ST[-I]]]//FCI


(* ::Text:: *)
(*Extract the imaginary part of the matching coefficient F_em(^3 S_1)*)


matchingCoeff[ImFem3S1]=Solve[decayRateTotalQCD==decayRateTotalNRQCD[0],{ImFem3S1}]//
Flatten


(* ::Text:: *)
(*Final expression for the total decay rate in NRQCD*)


decayRateTotalNRQCD[1]=decayRateTotalNRQCD[0]/.matchingCoeff[ImFem3S1]


(* ::Section:: *)
(*Check the final results*)


knownResult = (8 (-9+\[Pi]^2) CSP[ST[I],ST[-I]]*
	SMP["alpha_fs"]^3 SMP["e_Q"]^6)/(9 SMP["m_Q"]^2);
FCCompareResults[decayRateTotalNRQCD[1],knownResult,
Text->{"\tCompare to Eq.1 in arXiv:1210.6337:",
"CORRECT.","WRONG!"}, Interrupt->{Hold[Quit[1]],Automatic}];
Print["\tCPU Time used: ", Round[N[TimeUsed[],4],0.001], " s."];



