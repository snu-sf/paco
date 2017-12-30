#!/bin/sh

PACOSRCDIR=../src

maxsize=15
relsize=15
mutsize=3

python paconotation.py $maxsize > $PACOSRCDIR/paconotation.v
python pacotac.py $maxsize > $PACOSRCDIR/pacotac.v
python pacotacuser.py > $PACOSRCDIR/pacotacuser.v

echo "" > $PACOSRCDIR/paco.v
for i in `seq 0 $relsize`; do
  ./build-add.sh $i $mutsize
done
