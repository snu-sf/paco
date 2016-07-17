#!/bin/sh

relsize=15
mutsize=3

python paconotation.py $relsize > paconotation.v
python pacotac.py $relsize > pacotac.v
python pacodef.py $relsize $mutsize > pacodef.v
python pacotacuser.py $relsize $mutsize > pacotacuser.v
for i in `seq 0 $relsize`; do python paco.py $i $mutsize > paco${i}.v; done
echo "" > paco.v
for i in `seq 0 $relsize`; do echo "Require Export paco${i}." >> paco.v; done



