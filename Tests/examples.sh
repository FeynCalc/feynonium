#!/bin/bash

# This software is covered by the GNU General Public License 3.
# Copyright (C) 2015-2023 Vladyslav Shtabovenko

# Description:

# Checks FeynOnium using real-life calculations.

# Stop if any of the examples fails
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd $DIR



MATH=$1

#QED Examples
#-------------------------------------------------------------------------------
for exFile in 'ElAel-ElAel-CoulombPotential.m ElEl-ElEl-CoulombPotential.m'

do
  echo
  echo -e "* \c"
  $MATH -nopromt -script ../Examples/QED/Tree/$exFile
done

for exFile in 'GaGa-GaGa.m'

do
  echo
  echo -e "* \c"
  $MATH -nopromt -script ../Examples/QED/OneLoop/$exFile
done

#NRQCD Examples
#-------------------------------------------------------------------------------
for exFile in 'QQbar-GlGl.m H-QQbarGaGl-LCDA.m \
H-QQbarGa-LCDA.m QQbar-GaGa.m QQbar-GaGaGa.m'

do
  echo
  echo -e "* \c"
  $MATH -nopromt -script ../Examples/NRQCD/Tree/$exFile
done

for exFile in 'QiQjbar-QiQjbar.m'

do
  echo
  echo -e "* \c"
  $MATH -nopromt -script ../Examples/NRQCD/Tree/$exFile
done

#pNRQCD Examples
#-------------------------------------------------------------------------------
for exFile in 'S-OG.m'

do
  echo
  echo -e "* \c"
  $MATH -nopromt -script ../Examples/pNRQCD/OneLoop/$exFile
done

#BChPT Examples
#-------------------------------------------------------------------------------
for exFile in 'N-N.m'

do
  echo
  echo -e "* \c"
  $MATH -nopromt -script ../Examples/BChPT/OneLoop/$exFile
done

#-------------------------------------------------------------------------------


notify-send --urgency=low -i "$([ $? = 0 ] && echo sunny || echo error)" "Finished running examples for FeynCalc."
