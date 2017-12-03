(* :Title: General.mt														*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2015-2018 Vladyslav Shtabovenko
*)

(* :Summary:  Unit tests for FeynOnium									*)

(* ------------------------------------------------------------------------ *)


If [!StringQ[FeynCalc`$FeynOniumDirectory],
	BeginPackage["FeynCalc`"];
	FCDeclareHeader@ToFileName[{$FeynCalcDirectory, "AddOns",
	"FeynOnium"}, "FeynOnium.m"];
	Get@ToFileName[{$FeynCalcDirectory, "AddOns",
	"FeynOnium"}, "FeynOnium.m"];
	EndPackage[]
]

ClearAll[tests];
tests = FileNames["*.test",FileNameJoin[{$FeynOniumDirectory, "Tests", "Shared"}]]
Get/@tests;

Map[Test[ToExpression[(#[[2]])],ToExpression[(#[[3]])],TestID->#[[1]]]&,
	Join@@(ToExpression/@Names["Tests`Shared`*"])];
