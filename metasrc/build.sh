#!/bin/sh

PACOSRCDIR=../src

maxsize=18

rm $PACOSRCDIR/paco*.v
python paconotation.py $(expr $maxsize + 1) > $PACOSRCDIR/paconotation.v
python paconotation_internal.py $maxsize > $PACOSRCDIR/paconotation_internal.v
python pacotac.py $maxsize > $PACOSRCDIR/pacotac.v
cp pacotacuser.v $PACOSRCDIR/pacotacuser.v
cp pacon.v $PACOSRCDIR/pacon.v

echo "" > $PACOSRCDIR/paco.v
for i in `seq 0 $maxsize`; do
  ./build-add.sh $i
done

