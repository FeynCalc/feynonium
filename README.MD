# Description

FeynOnium is a FeynCalc add-on that facilitates calculations in Nonrelativistic Effective Field Theories (NREFTs)
in particular Nonrelativistic QCD (NRQCD) and potential Nonrelativistic QCD (pNRQCD)

# Requirements

FeynOnium is designed as an add-on for FeynCalc. To use it you need at least FeynCalc 9.3 and Mathematica 8. Many of the supplied examples also require the FeynHelpers(https://github.com/FeynCalc/feynhelpers) add-on.


# Installation

## Automatic installation

* Install the latest stable version of FeynCalc according to the [instructions](https://github.com/FeynCalc/feyncalc/wiki/Installation#st_automatic_installation) in the wiki

* Run the following instruction in a Kernel or Notebook session of Mathematica

	```
	Import["https://raw.githubusercontent.com/FeynCalc/feynonium/master/install.m"]
	InstallFeynOnium[]
	```

## Manual installation


* Create a directory with the name _FeynOnium_ inside

```
	FileNameJoin[{$UserBaseDirectory, "Applications", "FeynCalc", "AddOns"}]
```

and put the source code there.

# Usage

For usage information see the accompanying publication.

# Acknowledgments

If you use FeynOnium in you work, please cite

* N. Brambilla, H. S. Chung, V. Shtabovenko and A.Vairo, TUM-EFT 92/17, in preparation

# License

* The code of FeynOnium is licensed under GNU GPLv3.
