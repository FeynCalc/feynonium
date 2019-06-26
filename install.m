(* ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ *)

(* :Title: install															*)

(*
	This software is covered by the GNU General Public License 3.
	Copyright (C) 2014-2017 Vladyslav Shtabovenko
*)

(* :Summary:  Installs FeynOnium *)

(* ------------------------------------------------------------------------ *)

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

If[  $VersionNumber == 8,
(*To use FetchURL in MMA8 we need to load URLTools first *)
Needs["Utilities`URLTools`"];
];

If [Needs["FeynCalc`"]===$Failed,
	Message[InstallFeynOnium::nofc];
	Abort[]
];

Options[InstallFeynOnium]={
	AutoOverwriteFeynOniumDirectory->None,
	FeynOniumDevelopmentVersionLink->"https://github.com/FeynCalc/feynonium/archive/master.zip",
	(* For now there is no stable version *)
	FeynOniumStableVersionLink->"https://github.com/FeynCalc/feynonium/archive/master.zip",
	InstallFeynOniumDevelopmentVersion->False,
	InstallFeynOniumTo->FileNameJoin[{$FeynCalcDirectory, "AddOns","FeynOnium"}]
};


InstallFeynOnium[OptionsPattern[]]:=
	Module[{	unzipDir, tmpzip, gitzip, packageName, packageDir,
				FCGetUrl, strOverwriteFCdit, zipDir},

	If[OptionValue[InstallFeynOniumDevelopmentVersion],
		gitzip = OptionValue[FeynOniumDevelopmentVersionLink];
		zipDir = "feynonium-master",
		(* For now there is no stable version *)
		gitzip = OptionValue[FeynOniumStableVersionLink];
		zipDir = "feynonium-master"
	];

	packageName = "FeynOnium";
	packageDir = OptionValue[InstallFeynOniumTo];

strOverwriteFCdit="Looks like FeynOnium is already installed. Do you want to replace the content \
of " <> packageDir <> " with the downloaded version of FeynOnium? If you are using any custom configuration \
files or add-ons that are located in that directory, please backup them in advance.";

	If[$VersionNumber < 8,
		Message[InstallFeynOnium::notcomp];
		Abort[]
	];

	If[$VersionNumber == 8,
		(*To use FetchURL in MMA8 we need to load URLTools first *)
		FCGetUrl[x_]:= Utilities`URLTools`FetchURL[x],
		FCGetUrl[x_]:= URLSave[x,CreateTemporary[]]
	];


	(* If the package directory already exists, ask the user about overwriting *)
	If[ DirectoryQ[packageDir],

		If[ OptionValue[AutoOverwriteFeynOniumDirectory],

			Quiet@DeleteDirectory[packageDir, DeleteContents -> True],

			Null,
			If[ ChoiceDialog[strOverwriteFCdit,{"Yes, overwrite the " <> packageName <>" directory"->True,
				"No! I need to do a backup first."->False}],
				Quiet@DeleteDirectory[packageDir, DeleteContents -> True],
				Abort[]
			]
		]
	];

	(* Download FeynOnium tarball	*)
	WriteString["stdout", "Downloading FeynOnium from ", gitzip," ..."];
	tmpzip=FCGetUrl[gitzip];
	unzipDir= tmpzip<>".dir";
	WriteString["stdout", "done! \n"];

	(* Extract to the content	*)
	WriteString["stdout", "FeynOnium zip file was saved to ", tmpzip,".\n"];
	WriteString["stdout", "Extracting FeynOnium zip file to ", unzipDir, " ..."];
	ExtractArchive[tmpzip, unzipDir];
	WriteString["stdout", "done! \n"];

	(* Delete the downloaded file	*)
	Quiet@DeleteFile[tmpzip];

	(* Move the files to the final destination	*)
	WriteString["stdout", "Copying "<>packageName<>" to ", packageDir, " ..."];
	Print[FileNameJoin[{unzipDir,zipDir}]];
	CopyDirectory[FileNameJoin[{unzipDir,zipDir}],packageDir];
	WriteString["stdout", "done! \n"];
	(* Delete the extracted archive *)
	Quiet@DeleteDirectory[unzipDir, DeleteContents -> True];

	WriteString["stdout", "done! \n"];

	WriteString["stdout","\nInstallation complete! To load FeynOnium, restart Mathematica \
and evaluate \n\n $LoadAddOns={\"FeynOnium\"}; \n\n before you load FeynCalc; \n"];

];
