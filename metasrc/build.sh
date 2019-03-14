#!/bin/sh

PACOSRCDIR=../src

maxsize=18

rm $PACOSRCDIR/paco*.v
python paconotation.py $(expr $maxsize + 1) > $PACOSRCDIR/paconotation.v
python paconotation_internal.py $maxsize > $PACOSRCDIR/paconotation_internal.v
python pacotac.py $maxsize > $PACOSRCDIR/pacotac.v
python pacotacuser_param.py $maxsize > $PACOSRCDIR/pacotacuser_param.v
cp pacotacuser.v $PACOSRCDIR/pacotacuser.v
cp pacon.v $PACOSRCDIR/pacon.v

echo "" > $PACOSRCDIR/pacoall.v
for i in `seq 0 $maxsize`; do
  ./build-add.sh $i
done

echo "Require Export pacoall." > $PACOSRCDIR/paco.v
echo "Require Export pacotacuser_param." >> $PACOSRCDIR/paco.v

