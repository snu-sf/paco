#!/bin/sh

if [ $# -lt 1 ]
then
  echo "Usage: $0 relsize"
  exit 1
fi

PACOSRCDIR=../src

relsize=$1

python paco.py ${relsize} > $PACOSRCDIR/paco${relsize}.v;
python upto.py ${relsize} > $PACOSRCDIR/paco${relsize}_upto.v;
echo "Require Export paco${relsize}." >> $PACOSRCDIR/paco.v;
echo "Require Export paco${relsize}_upto." >> $PACOSRCDIR/paco.v;
