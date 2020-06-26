(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: install															*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2014-2020 Vladyslav Shtabovenko
*)

(* :Summary:  Installs FeynOnium *)

(* ------------------------------------------------------------------------ *)

If[	!FreeQ[$ContextPath,"WolframLanguageForJupyter`"],
			Print["It seems that your are trying to install FeynOnium from a ",
				"Wolfram Language kernel for Jupyter notebooks.",
				"Unfortunately, graphical installation using a Jupyter frontend is currently not possible.",
				"If you only have access to the Free Wolfram Engine, please start the kernel with a text-based interface",
				"and run the installer again.", "\n\nInstallation aborted!"];
			Abort[]
];

$FeynCalcStartupMessages = False;

BeginPackage["FeynOniumInstaller`",{"FeynCalc`"}];

InstallFeynOnium::usage =
"Installs FeynOnium.";

InstallFeynOnium::nofc =
"Looks like you don't have FeynCalc installed. FeynOnium cannot work without FeynCalc, so please \
install it first.";

InstallFeynOnium::notcomp =
"Your Mathematica version is too old. FeynOnium requires at least Mathematica 8. Installation aborted!";

InstallFeynOnium::failed =
"Download of `1` failed. Installation aborted!";

AutoOverwriteFeynOniumDirectory::usage="AutoOverwriteFeynOniumDirectory is an option of InstallFeynOnium. If \
set to True, the existing FeynOnium directory will be deleted without any further notice. The default
value None means that the user will be asked by a dialog. False means that the directory will be overwritten.";

FeynOniumDevelopmentVersionLink::usage="FeynOniumDevelopmentVersionLink is an option of InstallFeynOnium. It specifies the url \
to the main repository of FeynOnium. This repository is used to install the development version of FeynOnium.";

FeynOniumStableVersionLink::usage="FeynOniumStableVersionLink is an option of InstallFeynOnium. It specifies the url \
to the latest stable release of FeynOnium.";

InstallFeynOniumDevelopmentVersion::usage="InstallFeynOniumDevelopmentVersion is an option of InstallFeynOnium. If \
set to True, the installer will download the latest development version of FeynOnium from the git repository. \
Otherwise it will install the latest stable version.";

InstallFeynOniumTo::usage="InstallFeynOniumTo is an option of InstallFeynOnium. It specifies, the full path \
to the directory where FeynOnium will be installed.";

Begin["`Private`"]

testConnection::usage="";
packageDir::usage="";
packageName::usage="";
strOverwriteFC::usage="";

If[	$VersionNumber < 8,
	Message[InstallFeynCalc::notcomp];
	Abort[]
];

If [Needs["FeynCalc`"]===$Failed,
	Message[InstallFeynOnium::nofc];
	Abort[]
];

If[	8.0 <=$VersionNumber < 9.0,
	(*To use FetchURL in MMA8 we need to load URLTools first *)
	Needs["Utilities`URLTools`"];
];

Which[
	(*Mma 8*)
	8.0 <=$VersionNumber < 9.0,
		(*To use FetchURL we need to load URLTools first *)
		FCGetUrl[x_, opts:OptionsPattern[]]:= Utilities`URLTools`FetchURL[x,opts],
	(*Mma 9 or 10 *)
	9.0 <=$VersionNumber < 11.0,
		FCGetUrl[x_, opts:OptionsPattern[]]:= URLSave[x,CreateTemporary[],opts],
	(*Mma 11 and above *)
	$VersionNumber >= 11.0,
		FCGetUrl[x_, opts:OptionsPattern[]]:= URLSave[x,CreateTemporary[],opts]
		(*FCGetUrl[x_, opts:OptionsPattern[]]:= First[URLDownload[x,CreateTemporary[],opts]]*)
];

(*Test that we can access the FeynCalc repository*)
	Quiet[testConnection = FCGetUrl["https://github.com/FeynCalc/feyncalc"];];
	If[	testConnection===$Failed || !FileExistsQ[testConnection],
		WriteString["stdout",
			"It seems that your Mathematica version is unable to ",
			"connect to the FeynCalc repository on GitHub.\n",
			"This might be a network connectivity problem or an issue with Mathematica.\n",
			"Especially some older versions of Mathematica (8, 9 or 10) and known to cause such problems\n",
			"on recent versions of Linux, MacOS and Windows when accessing SSL-encrypted urls.\n\n",
			"Please check the wiki <https://github.com/FeynCalc/feyncalc/wiki/Installation> for ",
			"possible workarounds.\n",
			"Notice that it is also possible to download all the necessary files by hand and install FeynCalc\n",
			"without an existing internet connection. The required steps are described in the wiki.", "\n\nInstallation aborted!"
		];
			Abort[]
	];

fancyText[Column[li_List]] :=
	Column[(TextCell[#, "Text"] & /@ li)] /; $Notebooks

fancyText[x_] :=
	x /; !$Notebooks;

choiceDialog2[x__] :=
	ChoiceDialog[x]/; $Notebooks;

choiceDialog2[text_,rest__] :=
	(
	WriteString["stdout","\n\n"];
	MessageDialog[text];
	ChoiceDialog["",rest]
	)/; !$Notebooks;

strOverwriteFC :=
	Column[{
		"Looks like you already have a version of "<> packageName <> " installed in " <> packageDir,
		"",
		"The installer can overwrite the content of this directory with the downloaded version of " <> packageName<>".",
		"",
		"However, in this case all custom configuration files or add-ons located there will be lost.",
		"",
		"How should we proceed?"
		}
	];



(*Greeter*)
Print["Welcome to the automatic FeynOnium installer!"];
Print[" \[Bullet] To install the current stable version of FeynOnium (recommended for productive use), please evaluate"];
Print["\t", If[$Notebooks,TextCell["InstallFeynOnium[]", "Code"],"InstallFeynOnium[]"]];
Print[" \[Bullet] To install the development version of FeynOnium (only for experts or beta testers), please evaluate "];
Print["\t", If[$Notebooks,TextCell["InstallFeynOnium[InstallFeynOniumDevelopmentVersion->True]", "Code"],
	"InstallFeynOnium[InstallFeynOniumDevelopmentVersion->True]" ]];
Print[" \[Bullet] If you are already using the development version of FeynCalc you must also install the development verson of FeynOnium!"];


Options[InstallFeynOnium] = {
	AutoOverwriteFeynOniumDirectory		->	None,
	FeynOniumDevelopmentVersionLink		->	"https://github.com/FeynCalc/feynonium/archive/master.zip",
	FeynOniumStableVersionLink			->	"https://github.com/FeynCalc/feynonium/archive/stable.zip",
	InstallFeynOniumDevelopmentVersion	->	False,
	InstallFeynOniumTo					->	FileNameJoin[{$FeynCalcDirectory, "AddOns","FeynOnium"}]
};


InstallFeynOnium[OptionsPattern[]]:=
	Module[	{unzipDir, tmpzip, zip, fullPath,
			xInstalled, fireInstalled, zipDir},

		If[OptionValue[InstallFeynOniumDevelopmentVersion],
			zip = OptionValue[FeynOniumDevelopmentVersionLink];
			zipDir = "feynonium-master",
			zip = OptionValue[FeynOniumStableVersionLink];
			zipDir = "feynonium-stable"
		];

		xInstalled 	  = False;
		fireInstalled = False;
		packageName   = "FeynOnium";
		packageDir    = OptionValue[InstallFeynOniumTo];




		(* If the package directory already exists, ask the user about overwriting *)
		If[ DirectoryQ[packageDir],

			If[ OptionValue[AutoOverwriteFeynOniumDirectory],

				Quiet@DeleteDirectory[packageDir, DeleteContents -> True],

				Null,
				If[ choiceDialog2[fancyText[strOverwriteFC],{"Yes, overwrite the " <> packageName <> " directory"->True,
					"No, I need to do a backup first. Abort installation."->False}, WindowFloating->True, WindowTitle->"Existing "<>packageName<>" installation detected"],
					Quiet@DeleteDirectory[packageDir, DeleteContents -> True],
					Abort[]
				]
			]
		];

		(* Download FeynOnium tarball	*)
		WriteString["stdout", "Downloading " <> packageName <>" from ", zip," ..."];
		tmpzip   = FCGetUrl[zip];
		unzipDir = tmpzip<>".dir";
		fullPath = FileNameJoin[{unzipDir,zipDir}];

		WriteString["stdout", "done! \n"];

		(* Extract to the content	*)
		WriteString["stdout", packageName <> " zip file was saved to ", tmpzip,".\n"];
		WriteString["stdout", "Extracting " <> packageName <> " zip file to ", unzipDir, " ..."];

		If[	ExtractArchive[tmpzip, unzipDir]===$Failed,
			WriteString["stdout", "\nFailed to extract the "<>packageName<>" zip. The file might be corrupted.\nInstallation aborted!"];
			Abort[],
			WriteString["stdout", "done! \n"];
			(* Delete the downloaded file	*)
			Quiet@DeleteFile[tmpzip]
		];

		(* Move the files to the final destination	*)
		WriteString["stdout", "Copying "<> packageName <>" to ", packageDir, " ..."];

		If[	CopyDirectory[fullPath, packageDir]===$Failed,
			WriteString["stdout", "\nFailed to copy "  <> fullPath <> " to ", packageDir <>". \nInstallation aborted!"];
			Abort[],
			WriteString["stdout", "done! \n"];
			(* Delete the extracted archive *)
			Quiet@DeleteDirectory[unzipDir, DeleteContents -> True];
		];

		(* Delete the downloaded file	*)
		Quiet@DeleteFile[tmpzip];

		(* Delete the extracted archive *)
		Quiet@DeleteDirectory[unzipDir, DeleteContents -> True];

		WriteString["stdout","\nInstallation complete!"];
		WriteString["stdout","\nTo load FeynOnium, restart Mathematica and evaluate"];
		WriteString["stdout","\n\n $LoadAddOns={\"FeynOnium\"}; \n\n before you load FeynCalc; \n"];

	];


End[];

EndPackage[];
