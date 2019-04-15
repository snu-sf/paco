#!/bin/sh

if [ $# -lt 1 ]
then
  echo "Usage: $0 relsize"
  exit 1
fi

PACOSRCDIR=../src

relsize=$1

python paco.py ${relsize} > $PACOSRCDIR/paco${relsize}.v;
python gpaco.py ${relsize} > $PACOSRCDIR/gpaco${relsize}.v;
echo "Require Export paco${relsize}." >> $PACOSRCDIR/pacoall.v;
echo "Require Export gpaco${relsize}." >> $PACOSRCDIR/gpacoall.v;
