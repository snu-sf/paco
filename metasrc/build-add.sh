#!/bin/sh

if [ $# -lt 2 ]
then
  echo "Usage: $0 relsize mutsize"
  exit 1
fi

PACOSRCDIR=../src

relsize=$1
mutsize=$2

python paco.py ${relsize} ${mutsize} > $PACOSRCDIR/paco${relsize}.v; 
echo "Require Export paco${relsize}." >> $PACOSRCDIR/paco.v; 
