#!/bin/sh

if [ $# -lt 2 ]
then
  echo "Usage: $0 infile outfile"
  exit 1
fi

infile=$1
outfile=$2

cp $infile $outfile
sed "s/\\\\/\\\\\\\\/g" < $outfile > ${outfile}~; mv ${outfile}~ $outfile
sed "s/ x0 x1 x2/\"+itrstr(\" x\", n)+\"/g" < $outfile > ${outfile}~; mv ${outfile}~ $outfile
sed "s/ T0 T1 T2/\"+itrstr(\" T\", n)+\"/g" < $outfile > ${outfile}~; mv ${outfile}~ $outfile
sed "s/3/\"+str(n)+\"/g" < $outfile > ${outfile}~; mv ${outfile}~ $outfile
sed "s/4/\"+str(n+1)+\"/g" < $outfile > ${outfile}~; mv ${outfile}~ $outfile
sed "s/^/print (\"/g" < $outfile > ${outfile}~; mv ${outfile}~ $outfile
sed "s/$/\")/g" < $outfile > ${outfile}~; mv ${outfile}~ $outfile
sed "s/^print (\"Variable T0.*$/for i in range(n):\n    print (\"Variable T\"+str(i)+\" : \"+ifpstr(i,\"forall\"),end=\"\")/g" < $outfile > ${outfile}~; mv ${outfile}~ $outfile
sed "s/^print (\"Variable T1.*$/    for j in range(i):\n        print (\" (x\"+str(j)+\": @T\"+str(j)+itrstr(\" x\",j)+\")\",end=\"\")/g" < $outfile > ${outfile}~; mv ${outfile}~ $outfile
sed "s/^print (\"Variable T2.*$/    print (ifpstr(i,\", \")+\"Type.\")/g" < $outfile > ${outfile}~; mv ${outfile}~ $outfile

echo -n '' > ${outfile}~
echo 'from __future__ import print_function' >> ${outfile}~
echo 'import sys' >> ${outfile}~
echo 'from pacolib import *' >> ${outfile}~
echo 'if len(sys.argv) < 2:' >> ${outfile}~
echo '    sys.stderr.write("\\nUsage: "+sys.argv[0]+" relsize\\n\\n")' >> ${outfile}~
echo '    sys.exit(1)' >> ${outfile}~
echo 'n = int(sys.argv[1])' >> ${outfile}~
echo '' >> ${outfile}~
cat $outfile >> ${outfile}~
mv ${outfile}~ $outfile


