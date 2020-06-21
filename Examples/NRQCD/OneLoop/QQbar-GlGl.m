(* ::Package:: *)

(* :Title: QQbar-GlGl															*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2014-2020 Vladyslav Shtabovenko
*)

(* :Summary:  Q Qbar -> Gl Gl, NRQCD, matching ST CS, 1-loop			*)

(* ------------------------------------------------------------------------ *)


(* ::Title:: *)
(*Virtual contribution to the quarkonium decay into two gluons in NRQCD (spin triplet, color singlet)*)


(* ::Section:: *)
(*Load FeynCalc and the necessary add-ons or other packages*)


description="Q Qbar -> Gl Gl, NRQCD, matching ST CS, 1-loop";
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


(* ::Text:: *)
(*Define a filter rule to exclude pair annihilation diagrams that do not contribute*)


$ExcludeTopologies[pairAnnihilation] =
FreeQ[(ToTree[#]/.{Topology[_][___,Propagator[External][Vertex[1][1], 
Vertex[a_][b_]],___,Propagator[External][Vertex[1][2], Vertex[a_][b_]],___]->mark,
	Topology[_][___,Propagator[External][Vertex[1][3], Vertex[a_][b_]],___,
	Propagator[External][Vertex[1][4], Vertex[a_][b_]],___]->mark}), mark]&;


diags=InsertFields[CreateTopologies[1,2->2,
ExcludeTopologies->{Tadpoles,pairAnnihilation}],
{F[3,{2,cq}],-F[3,{2,cqbar}]}->{V[5],V[5]},
InsertionLevel->{Particles},Model -> "SMQCD",
ExcludeParticles->{S[_],V[1|2|3|4],F[1|2|4],F[3,{1|3,_}]}];


diagsCT=InsertFields[CreateCTTopologies[1,2->2,
ExcludeTopologies->{Tadpoles,pairAnnihilation}],
{F[3,{2,cq}],-F[3,{2,cqbar}]}->{V[5],V[5]},
InsertionLevel->{Particles},Model -> "SMQCD"];


(* ::Section:: *)
(*Organize the diagrams as in the literature*)


(* ::Text:: *)
(*For simplicity, here we follow the calculation from hep-ph/9707223*)


(* ::Text:: *)
(*Diagrams from Fig. 3 a) in arXiv:hep-ph/9707223. No counter-terms are needed since these*)
(* diagrams are UV-finite.*)


diagsA=DiagramExtract[diags,{10,12}];
Paint[diagsA,
ColumnsXRows->{2,1}, Numbering->False,SheetHeader->False,
ImageSize->{512,256}];


(* ::Text:: *)
(*Diagrams (plus counter-terms for the OS mass renormalization) from Fig. 3 b) in arXiv:hep-ph/9707223*)


diagsB=DiagramExtract[diags,{20,25}];
Paint[diagsB,
ColumnsXRows->{2,1}, Numbering->False,SheetHeader->False,
ImageSize->{512,256}];


ctDiagsB=DiagramExtract[diagsCT,{5,7}];
Paint[ctDiagsB,
ColumnsXRows->{2,1}, Numbering->False,SheetHeader->False,
ImageSize->{512,256}];


diagsD=DiagramExtract[diags,{2,4,6,8}];
Paint[diagsD,
ColumnsXRows->{2,1}, Numbering->False,SheetHeader->False,
ImageSize->{512,256}];


(* ::Text:: *)
(*Diagrams from Fig. 3 e) in arXiv:hep-ph/9707223*)


diagsE=DiagramExtract[diags,{3,5,7,9}];
Paint[diagsE,ColumnsXRows->{2,1}, Numbering->False,SheetHeader->False,
ImageSize->{512,256}];


(* ::Text:: *)
(*Diagrams from Fig. 3 f) in arXiv:hep-ph/9707223.*)


diagsF=DiagramExtract[diags,{14,15}];
Paint[diagsF,
ColumnsXRows->{2,1}, Numbering->False,SheetHeader->False,
ImageSize->{512,256}];


(* ::Text:: *)
(*Diagrams from Fig. 3 g) in arXiv:hep-ph/9707223.*)


diagsG=DiagramExtract[diags,{11,13}];
Paint[diagsG,
ColumnsXRows->{2,1}, Numbering->False,SheetHeader->False,
ImageSize->{512,256}];


(* ::Text:: *)
(*Diagram from Fig. 3 h) in arXiv:hep-ph/9707223.*)


diagsH=DiagramExtract[diags,{1}];
Paint[diagsH,
ColumnsXRows->{2,1}, Numbering->False,SheetHeader->False,
ImageSize->{512,256}];


(* ::Section:: *)
(*Obtain the amplitudes*)


(* ::Text:: *)
(*Boilerplate code for generating the amplitudes*)


ampCreate[ex_]:=FCFAConvert[CreateFeynAmp[ex, PreFactor->1],
	IncomingMomenta->{p1,p2}, OutgoingMomenta->{k1,k2},LoopMomenta->{l},
	UndoChiralSplittings->True,ChangeDimension->D,	
	List->False, SMP->True, Contract->True,DropSumOver->True,
	FinalSubstitutions->{SMP["m_c"]->SMP["m_Q"]}]//
	ReplaceAll[#,{SMP["g_s"]^2->(4Pi SMP["alpha_s"])}]&//
	SUNSimplify//FeynAmpDenominatorSplit[#,Momentum->{l}]&;


(* ::Text:: *)
(*Apply the above code to the diagrams*)


{ampA[0],ampB[0],ampD[0],ampE[0],
	ampF[0],ampG[0],ampH[0]}=
	ampCreate/@{diagsA,diagsB,diagsD,diagsE,
	diagsF,diagsG,diagsH};


ctAmpB[0]=ampCreate[ctDiagsB]//ReplaceAll[#,{Conjugate[(dZfR1|dZfL1)[3,2,2]]->dZpsi,(dZfR1|dZfL1)[3,2,2]->dZpsi,
dMf1[3,2]->dZm SMP["m_Q"]}]&//DiracSubstitute67//DotSimplify//DiracSimplify;


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


{ampA[1],ampB[1],ampD[1],ampE[1],ampF[1],ampG[1],ampH[1],ctAmpB[1]}=
FMInsertCovariantProjector[#,{p1,QMass},{p2,QMass},
	mu,{cq,cqbar},Dimension->D]&/@{ampA[0],ampB[0],ampD[0],
	ampE[0],ampF[0],ampG[0],ampH[0],ctAmpB[0]};


(* ::Text:: *)
(*The next step is to carry out the Dirac traces and simplify the color algebra*)


AbsoluteTiming[{ampA[2],ampB[2],ampD[2],ampE[2],ampF[2],ampG[2],ampH[2],ctAmpB[2]}=
DiracSimplify[SUNSimplify[#]]&/@{ampA[1],ampB[1],
	ampD[1],ampE[1],ampF[1],ampG[1],ampH[1],ctAmpB[1]};]


(* ::Text:: *)
(*Switch to the kinematic variables P and q*)


AbsoluteTiming[
{ampA[3],ampB[3],ampD[3],ampE[3],ampF[3],ampG[3],ampH[3],ctAmpB[3]}=
	(((ExpandScalarProduct[#//MomentumExpand]//.
{h_[p1,dim___]:>h[P,dim]/2+h[q,dim],
h_[p2,dim___]:>h[P,dim]/2-h[q,dim],EN->FCI[Sqrt[QMass^2-SPD[q]]]}
)//ExpandScalarProduct)/.EN->FCI[Sqrt[QMass^2-SPD[q]]])&/@{ampA[2],ampB[2],
ampD[2],ampE[2],ampF[2],ampG[2],ampH[2],ctAmpB[2]};
]


(* ::Text:: *)
(*To extract the P-wave contribution at LO, we need to differentiate w.r.t to q and put q to zero*)
(*afterwards*)


pWaveExtract[ex_]:=FourDivergence[Collect2[ex,q,IsolateNames->KK],FVD[q,nu],
	ApartFF->False]//ReplaceAll[#,{q->0}]&;


AbsoluteTiming[{ampA[4],ampB[4],ampD[4],ampE[4],ampF[4],ampG[4],ampH[4],ctAmpB[4]}=
pWaveExtract/@{ampA[3],ampB[3],ampD[3],ampE[3],ampF[3],ampG[3],ampH[3],ctAmpB[3]};]


AbsoluteTiming[{ampA[5],ampB[5],ampD[5],ampE[5],ampF[5],ampG[5],ampH[5]}=
Collect2[ExpandScalarProduct[FRH[#]/.P->k1+k2],l,
	FeynAmpDenominator,IsolateNames->KK,IsolateFast->True,Factoring->False]&/@
{ampA[4],ampB[4],ampD[4],ampE[4],ampF[4],ampG[4],ampH[4]};]


(* ::Section:: *)
(*Process the loop integrals*)


(* ::Text:: *)
(*The most challenging part is the handling of loop integrals. Doing it in a naive way would be too slow,*)
(*hence we split this part of the calculation into multiple steps. At first we perform a partial tensor reduction*)
(*so that no loop momenta with open indices appear.*)


AbsoluteTiming[{ampA[6],ampB[6],ampD[6],ampE[6],ampF[6],ampG[6],ampH[6]}=
	(WriteString["stdout","."];FCMultiLoopTID[#,{l},FDS->False,ApartFF->False])&/@
{ampA[5],ampB[5],ampD[5],ampE[5],ampF[5],ampG[5],ampH[5]};]


AbsoluteTiming[{ampA[7],ampB[7],ampD[7],ampE[7],ampF[7],ampG[7],ampH[7]}=
	(WriteString["stdout","."];Contract[#])&/@
{ampA[6],ampB[6],ampD[6],ampE[6],ampF[6],ampG[6],ampH[6]};]


(* ::Text:: *)
(*Then we perform partial fractioning and loop momentum shifts several times to prepare*)
(*the integrals for the IBP reduction*)


AbsoluteTiming[ampA[8]=ApartFF[ampA[7],{l}];]


AbsoluteTiming[ampB[8]=ApartFF[ampB[7],{l}];]


AbsoluteTiming[ampD[8]=ApartFF[ampD[7],{l}];]


AbsoluteTiming[ampE[8]=ApartFF[ampE[7],{l}];]


AbsoluteTiming[ampF[8]=ApartFF[ampF[7],{l}];]


AbsoluteTiming[ampG[8]=ApartFF[ampG[7],{l}];]


AbsoluteTiming[ampH[8]=ApartFF[ampH[7],{l}];]


(* ::Text:: *)
(*Now we run again*)


AbsoluteTiming[ampA[9]=ApartFF[ampA[8],{l},FDS->False];]


AbsoluteTiming[ampB[9]=ApartFF[ampB[8],{l},FDS->False];]


AbsoluteTiming[ampD[9]=ApartFF[ampD[8],{l},FDS->False];]


AbsoluteTiming[ampE[9]=ApartFF[ampE[8],{l},FDS->False];]


AbsoluteTiming[ampF[9]=ApartFF[ampF[8],{l},FDS->False];]


AbsoluteTiming[ampG[9]=ApartFF[ampG[8],{l},FDS->False];]


AbsoluteTiming[ampH[9]=ApartFF[ampH[8],{l},FDS->False];]


AbsoluteTiming[{ampA[10],ampB[10],ampD[10],ampE[10],ampF[10],ampG[10],ampH[10]}=
	FCLoopExtract[#,{l},loop,FCLoopIBPReducableQ->True]&/@{ampA[9],ampB[9],ampD[9],ampE[9],ampF[9],ampG[9],ampH[9]};]


listIBP=Union[Flatten[Last/@{ampA[10],ampB[10],ampD[10],ampE[10],ampF[10],ampG[10],ampH[10]}]];
listIBP//Length


(* ::Text:: *)
(*There are 125 integrals that can be further simplified using IBP reduction, although some of them are scaleless*)
(*and can be removed right away. The IBP reduction is carried out using FIRE*)


listIBPEval=listIBP/.loop[x_FeynAmpDenominator]:>loop[FDS[x,l]];


i=0;
AbsoluteTiming[listIBPEval=(i++; WriteString["stdout", ToString[i]<>" "];FIREBurn[#,{l},{k1,k2}])&/@(listIBPEval/.loop->Identity);]


ruleIBP=Dispatch[Thread[Rule[listIBP,listIBPEval]]];


(* ::Text:: *)
(*Substitute the reduction rules*)


{ampA[11],ampB[11],ampD[11],ampE[11],ampF[11],ampG[11],ampH[11]}=
	{Total[ampA[10][[1;;2]]]/.ruleIBP,
	Total[ampB[10][[1;;2]]]/.ruleIBP,
	Total[ampD[10][[1;;2]]]/.ruleIBP,
	Total[ampE[10][[1;;2]]]/.ruleIBP,
	Total[ampF[10][[1;;2]]]/.ruleIBP,
	Total[ampG[10][[1;;2]]]/.ruleIBP,
	Total[ampH[10][[1;;2]]]/.ruleIBP};


(* ::Text:: *)
(*Now that we handled all IBP reducible integrals, the remaining integrals are much simpler.*)
(*We can handle them using TID and then analytically evaluate the resulting PaVe functions*)


AbsoluteTiming[{ampA[12],ampB[12],ampD[12],ampE[12],ampF[12],ampG[12],ampH[12]}=
Collect2[FRH[#],l,FeynAmpDenominator,IsolateNames->KK,IsolateFast->True,Factoring->False]&/@
{ampA[11],ampB[11],ampD[11],ampE[11],ampF[11],ampG[11],ampH[11]};]


AbsoluteTiming[{ampA[13],ampB[13],ampD[13],ampE[13],ampF[13],ampG[13],ampH[13]}=
TID[#,l]&/@{ampA[12],ampB[12],ampD[12],ampE[12],ampF[12],ampG[12],ampH[12]};]


AbsoluteTiming[ampA[14]=Collect2[FRH@FeynAmpDenominatorExplicit[ToPaVe[ampA[13],l]],PaVe,D,A0,B0,C0,D0,IsolateNames->KK,IsolateFast->True,Factoring->False];]


AbsoluteTiming[ampB[14]=Collect2[FRH@FeynAmpDenominatorExplicit[ToPaVe[ampB[13],l]],PaVe,D,A0,B0,C0,D0,IsolateNames->KK,IsolateFast->True,Factoring->False];]


AbsoluteTiming[ampD[14]=Collect2[FRH@FeynAmpDenominatorExplicit[ToPaVe[ampD[13],l]],PaVe,D,A0,B0,C0,D0,IsolateNames->KK,IsolateFast->True,Factoring->False];]


AbsoluteTiming[ampE[14]=Collect2[FRH@FeynAmpDenominatorExplicit[ToPaVe[ampE[13],l]],PaVe,D,A0,B0,C0,D0,IsolateNames->KK,IsolateFast->True,Factoring->False];]


AbsoluteTiming[ampF[14]=Collect2[FRH@FeynAmpDenominatorExplicit[ToPaVe[ampF[13],l]],PaVe,D,A0,B0,C0,D0,IsolateNames->KK,IsolateFast->True,Factoring->False];]


AbsoluteTiming[ampG[14]=Collect2[FRH@FeynAmpDenominatorExplicit[ToPaVe[ampG[13],l]],PaVe,D,A0,B0,C0,D0,IsolateNames->KK,IsolateFast->True,Factoring->False];]


AbsoluteTiming[ampH[14]=Collect2[FRH@FeynAmpDenominatorExplicit[ToPaVe[ampH[13],l]],PaVe,D,A0,B0,C0,D0,IsolateNames->KK,IsolateFast->True,Factoring->False];]


(* ::Text:: *)
(*Evaluate the PaVe functions analytically*)


AbsoluteTiming[ampA[15]=PaXEvaluate[ampA[14],l,PaXImplicitPrefactor->1/(2Pi)^D,ToPaVe->False]/.a_Log:>PowerExpand[a];]


AbsoluteTiming[ampB[15]=PaXEvaluate[ampB[14],l,PaXImplicitPrefactor->1/(2Pi)^D,ToPaVe->True]/.a_Log:>PowerExpand[a];]


AbsoluteTiming[ampD[15]=PaXEvaluate[ampD[14],l,PaXImplicitPrefactor->1/(2Pi)^D,ToPaVe->False]/.a_Log:>PowerExpand[a];]


AbsoluteTiming[ampE[15]=PaXEvaluate[ampE[14],l,PaXImplicitPrefactor->1/(2Pi)^D,ToPaVe->False]/.a_Log:>PowerExpand[a];]


AbsoluteTiming[ampF[15]=PaXEvaluate[ampF[14],l,PaXImplicitPrefactor->1/(2Pi)^D,ToPaVe->False]/.a_Log:>PowerExpand[a];]


AbsoluteTiming[ampG[15]=PaXEvaluate[ampG[14],l,PaXImplicitPrefactor->1/(2Pi)^D,ToPaVe->False]/.a_Log:>PowerExpand[a];]


AbsoluteTiming[ampH[15]=PaXEvaluate[ampH[14],l,PaXImplicitPrefactor->1/(2Pi)^D,ToPaVe->False]/.a_Log:>PowerExpand[a];]


(* ::Text:: *)
(*Finally we obtain our intermediate result. Even though all loop integrals have already been calculated, the expressions are still*)
(*quite complicated. The next step is to calculate the interference of these virtual diagrams with the Born-level diagrams.*)


AbsoluteTiming[{ampA[16],ampB[16],ampD[16],ampE[16],ampF[16],ampG[16],ampH[16]}=
	Collect2[FRH[#],LorentzIndex,Polarization,SUNIndex,Complex,IsolateNames->KK]&/@{ampA[15],ampB[15],ampD[15],ampE[15],ampF[15],ampG[15],ampH[15]};]


(* ::Section:: *)
(*Calculate real-virtual interference terms*)


(* ::Text:: *)
(*Tree-level amplitude for Q Qbar->Gl Gl that will be required for calculating*)
(*RV interference terms*)


ampTree=1/(Sqrt[SUNN] SMP["m_Q"]^4) I Sqrt[2] \[Pi] SMP["alpha_s"] (-Pair[LorentzIndex[mu,D],Momentum[Polarization[k2,-I],
D]] Pair[LorentzIndex[nu,D],Momentum[k1,D]] Pair[Momentum[k2,D],Momentum[Polarization[k1,-I],
D]]-Pair[LorentzIndex[mu,D],Momentum[k1,D]] Pair[LorentzIndex[nu,D],
Momentum[Polarization[k2,-I],D]] Pair[Momentum[k2,D],
Momentum[Polarization[k1,-I],D]]-Pair[LorentzIndex[mu,D],
Momentum[k1,D]] Pair[LorentzIndex[nu,D],Momentum[k1,
D]] Pair[Momentum[Polarization[k1,-I],D],Momentum[Polarization[k2,
-I],D]]+Pair[LorentzIndex[mu,D],Momentum[k2,D]] (-Pair[LorentzIndex[nu,
D],Momentum[Polarization[k1,-I],D]] Pair[Momentum[k1,D],
Momentum[Polarization[k2,-I],D]]+Pair[LorentzIndex[nu,D],
Momentum[k1,D]] Pair[Momentum[Polarization[k1,-I],D],
Momentum[Polarization[k2,-I],D]])+2 Pair[LorentzIndex[mu,
D],Momentum[Polarization[k2,-I],D]] Pair[LorentzIndex[nu,D],
Momentum[Polarization[k1,-I],D]] SMP["m_Q"]^2+Pair[LorentzIndex[mu,
D],Momentum[Polarization[k1,-I],D]] (Pair[LorentzIndex[nu,D],
Momentum[k1,D]] Pair[Momentum[k1,D],Momentum[Polarization[k2,-I],
D]]+2 Pair[LorentzIndex[nu,D],Momentum[Polarization[k2,
-I],D]] SMP["m_Q"]^2)) SUNDelta[SUNIndex[Glu3],SUNIndex[Glu4]];


(* ::Text:: *)
(*Introduce quarkonium polarization tensors for the spin triplet P-states*)


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
calRVJ[amp_,fun_]:=SUNSimplify[(ampTree ComplexConjugate[amp/.{mu->mu1,nu->nu1}]+
	(amp/.{mu->mu1,nu->nu1}) ComplexConjugate[ampTree])fun[mu,nu,mu1,nu1],
	SUNTrace->True,Explicit->True]//Contract//
	Collect2[#,Polarization,IsolateNames->KK]&//
	DoPolarizationSums[#,k1,0]&//DoPolarizationSums[#,k2,0]&


(* ::Text:: *)
(*The RV calculation still takes some time, but the output is quite simple*)


AbsoluteTiming[{rvAJ0[0],rvDJ0[0],rvEJ0[0],rvFJ0[0],rvGJ0[0],rvHJ0[0]}=
	calRVJ[#,polSumJ0]&/@{ampA[16],ampD[16],ampE[16],ampF[16],ampG[16],ampH[16]};]


AbsoluteTiming[{rvAJ1[0],rvDJ1[0],rvEJ1[0],rvFJ1[0],rvGJ1[0],rvHJ1[0]}=
	calRVJ[#,polSumJ1]&/@{ampA[16],ampD[16],ampE[16],ampF[16],ampG[16],ampH[16]};]


AbsoluteTiming[{rvAJ2[0],rvDJ2[0],rvEJ2[0],rvFJ2[0],rvGJ2[0],rvHJ2[0]}=
	calRVJ[#,polSumJ2]&/@{ampA[16],ampD[16],ampE[16],ampF[16],ampG[16],ampH[16]};]


(* ::Text:: *)
(*As expected the J=1 contribution vanishes.*)


{rvAJ1[0],rvDJ1[0],rvEJ1[0],rvFJ1[0],rvGJ1[0],rvHJ1[0]}


(* ::Text:: *)
(*The b) diagrams require mass renormalization in the on-shell scheme. Since we generated the*)
(*corresponding mass counterterm at the very beginning, we can evaluate it now using dZm for the*)
(*on-shell scheme.*)


ctAmpB[5]=ctAmpB[4]//FRH//ReplaceAll[#,P->k1+k2]&//FeynAmpDenominatorExplicit//ExpandScalarProduct//ReplaceRepeated[#,{
dZpsi->0,dZm->-3*CF*SMP["alpha_s"]*(4/3 + SMP["Delta"]+Log[ScaleMu^2/QMass^2])/(4*Pi)}]&//Series[#,{SMP["alpha_s"],0,2}]&//
	Normal//Simplify//FCShowEpsilon;


AbsoluteTiming[rvBJ0[0]=calRVJ[ampB[16]+ctAmpB[5],polSumJ0];]
AbsoluteTiming[rvBJ1[0]=calRVJ[ampB[16]+ctAmpB[5],polSumJ1];]
AbsoluteTiming[rvBJ2[0]=calRVJ[ampB[16]+ctAmpB[5],polSumJ2];]


(* ::Text:: *)
(*The c) diagrams are obtained by multiplying tree-level diagrams with Zpsi in the on-shell scheme*)


ampC[16]=(ampTree(Zpsi-1)/.{Zpsi->1-CF SMP["alpha_s"]/(4Pi)(3 SMP["Delta"]+3Log[ScaleMu^2/QMass^2]+4)})//
	FCShowEpsilon//Series[#,{SMP["alpha_s"],0,2}]&//Normal;


AbsoluteTiming[rvCJ0[0]=calRVJ[ampC[16],polSumJ0];]
AbsoluteTiming[rvCJ1[0]=calRVJ[ampC[16],polSumJ1];]
AbsoluteTiming[rvCJ2[0]=calRVJ[ampC[16],polSumJ2];]


(* ::Text:: *)
(*Introduce the known LO and NLO results from the literature (hep-ph/9707223)*)


prefacJ0=(SMP["alpha_s"]/Pi)decayRateJ0;
fEps=( 4 Pi ScaleMu^2/(4QMass^2))^Epsilon Gamma[1+  Epsilon];
phi2=1/(8Pi) (4Pi/( 4QMass^2))^(Epsilon)Gamma[1-Epsilon]/Gamma[2-2Epsilon];
decayRateJ0=144 Pi^2(1-Epsilon)/(3-2Epsilon) CF SMP["alpha_s"]^2/SMP["m_Q"]^4;
decayRateJ2=32 CF SMP["alpha_s"]^2 Pi^2/QMass^4 (6-13 Epsilon+4Epsilon^2)/
		((3-2Epsilon)(5-2Epsilon));
GBornJ0=(decayRateJ0 ScaleMu^(4Epsilon) phi2);
GBornJ2=(decayRateJ2 ScaleMu^(4Epsilon) phi2);


fLitJ0={
(*a*)(1/(Epsilon)- 4/9+  32/9Log[2] + Pi^2/12+0 Pi^2/(2v))CF,
(*b*)(-1/(2Epsilon)- 13/9+5/9Log[2])CF,
(*c*)(-1/(2Epsilon)-1/Epsilon-2-3Log[2])CF,
(*d*)(1/(Epsilon)+14/9 - 10/9 Log[2]+ Pi^2/6)(CF-1/2CA),
(*e*)(-3/(Epsilon)+2/(3 Epsilon^2) + 20/(9 Epsilon) - 11/3 + 2/3 Log[2]- Pi^2/9)(-1/2CA),
(*f*)(4/(3Epsilon^2)-2/(9Epsilon)+ 1-20/3Log[2]- 5/9 Pi^2)(CA/2),
(*g*)(-4/(3Epsilon^2)+2/(9Epsilon)-14/27+14/27Log[2]+13/18 Pi^2)CA,
(*h*)(-19/27+70/27 Log[2])CA
};
{resLitAJ0,resLitBJ0,resLitCJ0,resLitDJ0,
	resLitEJ0,resLitFJ0,resLitGJ0,resLitHJ0}=
	(Normal[Series[GBornJ0(SMP["alpha_s"]/Pi)fEps #,{Epsilon,0,0}]]//PowerExpand)&/@fLitJ0;


fLitJ2={
(*a*)(1/(Epsilon)- 5/3+  7/3Log[2] + Pi^2/8+0 Pi^2/(2v))CF,
(*b*)(-1/(2Epsilon)- 1/6 + 11/6 Log[2])CF,
(*c*)(-1/(2Epsilon)-1/Epsilon-2-3Log[2])CF,
(*d*)(1/(Epsilon)-1/6 - 7/6 Log[2]- Pi^2/8)(CF-1/2CA),
(*e*)(-3/(Epsilon)+3/(8 Epsilon^2) + 17/(16 Epsilon) - 59/96 - Pi^2/16)(-1/2CA),
(*f*)(13/(8Epsilon^2)+15/(16Epsilon)+ 107/96-11/2Log[2]- 67/48 Pi^2)(CA/2),
(*g*)(-13/(8Epsilon^2)-15/(16Epsilon)- 17/288+89/18 Log[2]+ 37/48 Pi^2)CA,
(*h*)(-5/9-10/9Log[2])CA
};
{resLitAJ2,resLitBJ2,resLitCJ2,resLitDJ2,
	resLitEJ2,resLitFJ2,resLitGJ2,resLitHJ2}=
	(Normal[Series[GBornJ2(SMP["alpha_s"]/Pi)fEps #,{Epsilon,0,0}]]//PowerExpand)&/@fLitJ2;


{resAJ0,resBJ0,resCJ0,resDJ0,resEJ0,resFJ0,resGJ0,resHJ0}= (Normal[Series[FCReplaceD[(FRH[#]/.{SMP["g_s"]^4->
(4Pi SMP["alpha_s"])^2}) (ScaleMu)^(4 Epsilon)phi2,D->4-2Epsilon],{Epsilon,0,0}]]//PowerExpand//Expand//Simplify//Expand)&/@{
	rvAJ0[0],rvBJ0[0],rvCJ0[0],rvDJ0[0],rvEJ0[0],rvFJ0[0],rvGJ0[0],rvHJ0[0]};


{resAJ2,resBJ2,resCJ2,resDJ2,resEJ2,resFJ2,resGJ2,resHJ2}= (Normal[Series[FCReplaceD[(FRH[#]/.{SMP["g_s"]^4->
(4Pi SMP["alpha_s"])^2}) (ScaleMu)^(4 Epsilon)phi2,D->4-2Epsilon],{Epsilon,0,0}]]//PowerExpand//Expand//Simplify//Expand)&/@{
	rvAJ2[0],rvBJ2[0],rvCJ2[0],rvDJ2[0],rvEJ2[0],rvFJ2[0],rvGJ2[0],rvHJ2[0]};


(* ::Text:: *)
(*Comparing results of the separate diagrams to the literature we find full agreement.*)
(*Notice that we have no Coulomb singularities, since the integrals were calculated after *)
(*applying the projectors. Furthermore, here we do not distinguish between UV and IR poles,*)
(*as we carry out the calculation using IBP techniques*)


{resLitAJ0-resAJ0,resLitBJ0-resBJ0,
resLitCJ0-resCJ0,resLitDJ0-resDJ0,
resLitEJ0-resEJ0,resLitFJ0-resFJ0,
resLitGJ0-resGJ0,resLitHJ0-resHJ0}//PowerExpand//SUNSimplify//Simplify


{resLitAJ2-resAJ2,resLitBJ2-resBJ2,
resLitCJ2-resCJ2,resLitDJ2-resDJ2,
resLitEJ2-resEJ2,resLitFJ2-resFJ2,
resLitGJ2-resGJ2,resLitHJ2-resHJ2}//PowerExpand//SUNSimplify//Simplify


(* ::Section:: *)
(*Final results*)


(* ::Text:: *)
(*Our final results written as in Eq. 124 of hep-ph/9707223*)


GammaHVJ0=Series[(resAJ0+resBJ0+resCJ0+resDJ0+resEJ0+resFJ0+resGJ0+resHJ0)/(GBornJ0(SMP["alpha_s"]/Pi)fEps),{Epsilon,0,0}]//
	Normal//PowerExpand//Together//SUNSimplify


GammaHVJ2=Series[(resAJ2+resBJ2+resCJ2+resDJ2+resEJ2+resFJ2+resGJ2+resHJ2)/(GBornJ2(SMP["alpha_s"]/Pi)fEps),{Epsilon,0,0}]//
	Normal//PowerExpand//Together//SUNSimplify


(* ::Section:: *)
(*Check the final results*)


knownResult = {
SUNSimplify[(11/6 CA-2/3 1/2 Nf)1/Epsilon-CA(1/Epsilon^2+11/(6Epsilon))+2/(3Epsilon)1/2 Nf+CF(-7/3+Pi^2/4)+CA(1/3+5/12 Pi^2)],
SUNSimplify[(11/6 CA-2/3 1/2 Nf)1/Epsilon-CA(1/Epsilon^2+11/(6Epsilon))+2/(3Epsilon)1/2 Nf-4CF+CA(1/3+5/3Log[2]+Pi^2/6)]
};
FCCompareResults[{GammaHVJ0,GammaHVJ2},knownResult,
Text->{"\tCompare to Eqs. 124-127 in arXiv:hep-ph/9707223:",
"CORRECT.","WRONG!"}, Interrupt->{Hold[Quit[1]],Automatic}];
Print["\tCPU Time used: ", Round[N[TimeUsed[],4],0.001], " s."];



