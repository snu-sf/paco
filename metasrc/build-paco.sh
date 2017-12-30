#!/bin/sh

PACOSRCDIR=../src

relsize=15
mutsize=3

python paconotation.py $relsize > $PACOSRCDIR/paconotation.v
python pacotac.py $relsize > $PACOSRCDIR/pacotac.v
python pacodef.py $relsize $mutsize > $PACOSRCDIR/pacodef.v
python pacotacuser.py $relsize $mutsize > $PACOSRCDIR/pacotacuser.v
for i in `seq 0 $relsize`; do python paco.py $i $mutsize > $PACOSRCDIR/paco${i}.v; done
echo "" > $PACOSRCDIR/paco.v
for i in `seq 0 $relsize`; do echo "Require Export paco${i}." >> $PACOSRCDIR/paco.v; done
