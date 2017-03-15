(* ::Package:: *)

(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: FeynOnium														*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2016 Vladyslav Shtabovenko
*)

(* :Summary: 	Tools for calculations in non-relativistic EFTs			 	*)

(* ------------------------------------------------------------------------ *)

$FeynOniumVersion::usage=
"$FeynOniumVersion is the string that represents the version of FeynOnium";

$FeynOniumDirectory::usage=
"$FeynOniumDirectory is the string that represents the full path to the FeynOnium \
directory";

Begin["`Package`"]
End[]

Begin["`FeynOnium`Private`"];

$FeynOniumVersion="0.0.1";

$FeynOniumDirectory =
ToFileName[{$FeynCalcDirectory, "AddOns", "FeynOnium"}];

(* Load the .m files *)
BeginPackage["FeynCalc`"];
FCDeclareHeader/@FileNames[{"*.m"},ToFileName[{$FeynOniumDirectory,"Shared"}]];
FCDeclareHeader/@FileNames[{"*.m"},ToFileName[{$FeynOniumDirectory,"NRQCD"}]];
Get/@FileNames[{"*.m"},ToFileName[{$FeynOniumDirectory,"Shared"}]];
Get/@FileNames[{"*.m"},ToFileName[{$FeynOniumDirectory,"NRQCD"}]];
EndPackage[]




(* Print startup message *)
If[ Global`$FeynCalcStartupMessages =!= False,
	Print[Style["FeynOnium ", "Text", Bold], Style[$FeynOniumVersion <> " loaded.", "Text"]];
	Print[ Style["Have a look at the supplied ","Text"],

	Style[DisplayForm@ButtonBox["examples.", BaseStyle -> "Hyperlink",	ButtonFunction :>
							SystemOpen[FileNameJoin[{$FeynOniumDirectory, "Examples"}]],
							Evaluator -> Automatic, Method -> "Preemptive"], "Text"],
	Style[" If you use FeynOnium in your research, please cite","Text"]];
	Print [Style[" \[Bullet] N. Brambilla, V. Shtabovenko and A.Vairo \"FeynOnium: Using FeynCalc for automatic calculations in non-relativistic EFTs\", TUM-EFT 92/17, in preparation","Text"]];
];

End[]


