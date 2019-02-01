#!/bin/sh

PACOSRCDIR=../src

maxsize=18
mutsize=3

rm $PACOSRCDIR/paco*.v
python paconotation.py $(expr $maxsize + 1) > $PACOSRCDIR/paconotation.v
python paconotation_internal.py $maxsize > $PACOSRCDIR/paconotation_internal.v
python pacotac.py $maxsize > $PACOSRCDIR/pacotac.v
python pacotacuser.py > $PACOSRCDIR/pacotacuser.v
python pacon.py ${mutsize} > $PACOSRCDIR/pacon.v

echo "" > $PACOSRCDIR/paco.v

for i in `seq 0 $maxsize`; do
  ./build-add.sh $i $mutsize
done

echo "" >> $PACOSRCDIR/paco.v
echo "Ltac pclearbot :=" >> $PACOSRCDIR/paco.v
echo "  let X := fresh \"_X\" in" >> $PACOSRCDIR/paco.v
echo "  repeat match goal with" >> $PACOSRCDIR/paco.v
echo "         | [H: context[pacoid] |- _] =>" >> $PACOSRCDIR/paco.v
echo "           first" >> $PACOSRCDIR/paco.v
echo "             [red in H; destruct H as [H|X]; [|contradiction X]|(" >> $PACOSRCDIR/paco.v
for i in `seq 0 $maxsize`; do
    echo "                setoid_rewrite upaco${i}_clear in H ||" >> $PACOSRCDIR/paco.v
done
echo "                fail)] end." >> $PACOSRCDIR/paco.v
