(* ::Package:: *)

(* :Title: N-N															*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2014-2023 Vladyslav Shtabovenko
*)

(* :Summary:  N -> N, BChPT, master integrals, 1-loop					*)

(* ------------------------------------------------------------------------ *)



(* ::Title:: *)
(*One loop correction to the nucleon mass*)


(* ::Section:: *)
(*Load FeynCalc and the necessary add-ons or other packages*)


description="N -> N, BChPT, master integrals, 1-loop";
If[ $FrontEnd === Null,
	$FeynCalcStartupMessages = False;
	Print[description];
];
If[ $Notebooks === False,
	$FeynCalcStartupMessages = False
];
<<FeynCalc`

FCCheckVersion[9,3,1];


(* ::Section:: *)
(*Enter the amplitude*)


(* ::Text:: *)
(*The 1/(2Pi)^D prefactor is implicit. We enter Eq. 5.182 from hep-ph/0210398*)


amp[0] = (-(-1/2 GA[5].(GAD[\[Mu]].GSD[v]-FVD[v,\[Mu]]).CSI[i]FVD[k,\[Mu]])).
(-1/2 GA[5].(GAD[\[Nu]].GSD[v]-FVD[v,\[Nu]]).CSI[i])FVD[k,\[Nu]]*
SFAD[{{0,v.(r-k)}},{k,M^2}]


(* ::Section:: *)
(*Calculate the amplitude*)


(* ::Text:: *)
(*Simplify the Pauli algebra and carry out tensor reduction*)


amp[1] = amp[0]//PauliSimplify//FCMultiLoopTID[#,{k}]&


(* ::Section:: *)
(*Check the final results*)


knownResult = 3/4 SFAD[{{k,0},{M^2,1},1}]*
SPD[r,v]-3/4 SFAD[{{k,0},{M^2,1},1},{{0,(-k+r).v},{0,1},1}]*
 (SPD[r,v]^2-M^2 SPD[v,v]);
FCCompareResults[amp[1],knownResult,
Text->{"\tCompare to hep-ph/0210398, Eq 5.183:",
"CORRECT.","WRONG!"}, Interrupt->{Hold[Quit[1]],Automatic}];
Print["\tCPU Time used: ", Round[N[TimeUsed[],4],0.001], " s."];



