from __future__ import print_function
import sys
from pacolib import *

if len(sys.argv) < 2: 
    sys.stderr.write('\nUsage: '+sys.argv[0]+' relsize\n\n') 
    sys.exit(1) 

relsize = int(sys.argv[1])

print ("(** * Common notations and definitions *)")
print ()

print ("(** ** Types of dependent predicates *)")
print ()
for n in range (relsize+1):
    print ("Definition rel"+str(n)+itrstr(" T",n)+" :=")
    print ("  "+ifpstr(n,"forall"),end='')
    for i in range (n):
        print (" (x"+str(i)+": T"+str(i)+itrstr(" x",i)+")",end='')
    print (ifpstr(n,", ")+"Prop.")
    print ("Implicit Arguments rel"+str(n)+" [].")
    print ()

print ("(** ** Bottom *)")
print ()
print ("Definition pacoid {A : Type} (a: A) : A := a.")
print ()
for n in range (relsize+1):
    print ("Notation bot"+str(n)+" :=")
    print ("  (pacoid("+ifpstr(n,"fun")+n*" _"+ifpstr(n," => ")+"False)).")
    print ()

print ("(** ** Less than or equal *)")
print ()
for n in range (relsize+1):
    print ("Notation \"p <"+str(n)+"= q\" :=")
    print ("  (forall"+itrstr(" x",n)+" (PR: p"+itrstr(" x",n)+" : Prop), q"+itrstr(" x",n)+" : Prop)")
    print ("  (at level 50, no associativity"+ifzstr(n,", only parsing")+").")
    print ()

print ("(** ** Union *)")
print ()
for n in range (relsize+1):
    print ("Notation \"p \\"+str(n)+"/ q\" :=")
    print ("  ("+ifpstr(n,"fun")+itrstr(" x",n)+ifpstr(n," => ")+"p"+itrstr(" x",n)+" \\/ q"+itrstr(" x",n)+")")
    print ("  (at level 50, no associativity"+ifzstr(n,", only parsing")+").")
    print ()

