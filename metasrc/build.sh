#!/bin/sh

PACOSRCDIR=../src

maxsize=15

rm -f $PACOSRCDIR/paco*.v
rm -f $PACOSRCDIR/cpn*.v
rm -f $PACOSRCDIR/wcpn*.v
python paconotation.py $(expr $maxsize + 1) > $PACOSRCDIR/paconotation.v
python paconotation_internal.py $maxsize > $PACOSRCDIR/paconotation_internal.v
cp paco_internal.v $PACOSRCDIR/paco_internal.v
python pacotac_internal.py $maxsize > $PACOSRCDIR/pacotac_internal.v
python pacotac.py $maxsize > $PACOSRCDIR/pacotac.v
python cpntac.py $maxsize > $PACOSRCDIR/cpntac.v
python wcpntac.py $maxsize > $PACOSRCDIR/wcpntac.v

echo "" > $PACOSRCDIR/pacoall.v
echo "" > $PACOSRCDIR/cpnall.v
echo "" > $PACOSRCDIR/wcpnall.v
for i in `seq 0 $maxsize`; do
  ./build-add.sh $i
done

echo "" > $PACOSRCDIR/paco.v
echo "Require Export pacoall." >> $PACOSRCDIR/paco.v
echo "Require Export pacotac." >> $PACOSRCDIR/paco.v
echo "Require Export cpnall." >> $PACOSRCDIR/paco.v
echo "Require Export cpntac." >> $PACOSRCDIR/paco.v
echo "Require Export wcpnall." >> $PACOSRCDIR/paco.v
echo "Require Export wcpntac." >> $PACOSRCDIR/paco.v
