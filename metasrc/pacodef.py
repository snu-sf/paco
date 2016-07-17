from __future__ import print_function
import sys
from pacolib import *

if len(sys.argv) < 3: 
    sys.stderr.write('\nUsage: '+sys.argv[0]+' relsize mutsize\n\n') 
    sys.exit(1) 

relsize = int(sys.argv[1])
mutsize = int(sys.argv[2])

print ('Require Export paconotation.')
print ('Set Implicit Arguments.')
print ('')

print ('(** * Formalization of Parameterized Coinduction: the Internal Approach')
print ('')
print ('    We use the strict positivization trick (Section 6.1 of the paper) ')
print ('    in order to define G for arbitrary functions (here called paco{n}).')
print ('*)')
print ('')

for n in range(relsize+1):
    for m in range(1,mutsize+1):
        print ('Section Arg'+str(n)+lev(m)+'_def.')
        for i in range(n):
            print ('Variable T'+str(i)+' : '+ifpstr(i,'forall'),end='')
            for j in range(i):
                print (' (x'+str(j)+': @T'+str(j)+itrstr(" x",j)+')',end='')
            print (ifpstr(i,', ')+'Type.')
        print ('Variable'+itridx(" gf",m)+' : '+m*('rel'+str(n)+itrstr(" T",n)+' -> ')+'rel'+str(n)+itrstr(" T",n)+'.')
        for i in range(m):
            print ('Implicit Arguments gf'+idx(m,i)+' [].')
        print ('')
        print ('CoInductive ',end='')
        for i in range(m):
            print (ifpstr(i,"with ")+'paco'+str(n)+lev(m)+idx(m,i)+'('+itridx(' r',m)+': rel'+str(n)+itrstr(' T',n)+')'+itrstr(" x",n)+' : Prop :=')
            print ('| paco'+str(n)+lev(m)+idx(m,i)+'_pfold'+itridx(' pco',m))
            for j in range(m):
                print ('    (LE : pco'+idx(m,j)+' <'+str(n)+'= (paco'+str(n)+lev(m)+idx(m,j)+itridx(' r',m)+' \\'+str(n)+'/ r'+idx(m,j)+'))')
            print ('    (SIM: gf'+idx(m,i)+itridx(' pco',m)+itrstr(" x",n)+')')
        print ('.')
        for i in range(m):
            print ('Definition ',end='')
            print ('upaco'+str(n)+lev(m)+idx(m,i)+'('+itridx(' r',m)+': rel'+str(n)+itrstr(' T',n)+')'+' := '+'paco'+str(n)+lev(m)+idx(m,i)+itridx(' r',m)+' \\'+str(n)+'/ r'+idx(m,i),end='')
            print ('.')
        print ('End Arg'+str(n)+lev(m)+'_def.')
        for i in range(m):
            print ('Implicit Arguments paco'+str(n)+lev(m)+idx(m,i)+' ['+itrstr(" T",n)+' ].')
            print ('Implicit Arguments upaco'+str(n)+lev(m)+idx(m,i)+' ['+itrstr(" T",n)+' ].')
            print ('Hint Unfold upaco'+str(n)+lev(m)+idx(m,i)+'.')
        print ('')
