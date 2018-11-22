#!/bin/sh

PACOSRCDIR=../src

maxsize=15
relsize=15
mutsize=3

python paconotation.py $maxsize > $PACOSRCDIR/paconotation.v
python paconotation_internal.py $maxsize > $PACOSRCDIR/paconotation_internal.v
python pacotac.py $maxsize > $PACOSRCDIR/pacotac.v
python pacotacuser.py > $PACOSRCDIR/pacotacuser.v
python pacon.py ${mutsize} > $PACOSRCDIR/pacon.v

echo "" > $PACOSRCDIR/paco.v
for i in `seq 0 $relsize`; do
  ./build-add.sh $i $mutsize
done
