#!/bin/sh

if [ $# -lt 1 ]
then
  echo "Usage: $0 relsize"
  exit 1
fi

PACOSRCDIR=../src

relsize=$1

python paco.py ${relsize} > $PACOSRCDIR/paco${relsize}.v;
python cpn.py ${relsize} > $PACOSRCDIR/cpn${relsize}.v;
python gcpn.py ${relsize} > $PACOSRCDIR/gcpn${relsize}.v;
echo "Require Export paco${relsize}." >> $PACOSRCDIR/pacoall.v;
echo "Require Export cpn${relsize}." >> $PACOSRCDIR/cpnall.v;
echo "Require Export gcpn${relsize}." >> $PACOSRCDIR/gcpnall.v;
