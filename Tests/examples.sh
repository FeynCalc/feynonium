#!/bin/bash

# This small bash script provides a nice way to check that
# FeynOnium is working properly using real-life examples.

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd $DIR

if [ -z ${MATH+x} ]; then MATH=math; else echo $MATH; fi

#NRQCD Examples
$MATH -nopromt -script ../Examples/NRQCD/NRQCD-QQbarToTwoPhotons-Tree.m
$MATH -nopromt -script ../Examples/NRQCD/NRQCD-QQbarToThreePhotons-Tree.m
$MATH -nopromt -script ../Examples/NRQCD/NRQCD-QQbarPrimeToQQbarPrime-OneLoop.m

notify-send "Finished running examples for FeynOnium."
