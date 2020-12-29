#!/bin/sh

PACOSRCDIR=../src

maxsize=4

rm -f $PACOSRCDIR/paco*.v
rm -f $PACOSRCDIR/gpaco*.v
python paconotation.py $(expr $maxsize + 1) > $PACOSRCDIR/paconotation.v
python paconotation_internal.py $maxsize > $PACOSRCDIR/paconotation_internal.v
cp paco_internal.v $PACOSRCDIR/paco_internal.v
python pacotac_internal.py $maxsize > $PACOSRCDIR/pacotac_internal.v
python pacotac.py $maxsize > $PACOSRCDIR/pacotac.v
python gpacotac.py $maxsize > $PACOSRCDIR/gpacotac.v

echo "" > $PACOSRCDIR/pacoall.v
echo "" > $PACOSRCDIR/gpacoall.v
for i in `seq 0 $maxsize`; do
  ./build-add.sh $i
done

echo -n "" > $PACOSRCDIR/paco.v
echo "From Paco Require Export pacoall." >> $PACOSRCDIR/paco.v
echo "From Paco Require Export pacotac." >> $PACOSRCDIR/paco.v
echo "From Paco Require Export gpacoall." >> $PACOSRCDIR/paco.v
echo "From Paco Require Export gpacotac." >> $PACOSRCDIR/paco.v
