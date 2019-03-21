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
    print ("Arguments rel"+str(n)+" : clear implicits.")
    print ()

print ("(** ** Signatures *)")
print ()
for n in range (relsize+1):
    print ("Record sig"+str(n)+"T "+ifpstr(n,"{"+itrstr(" T",n)+"}")+" :=")
    print ("  exist"+str(n)+"T {")
    for i in range(n):
        print ("      proj"+str(n)+"T"+str(i)+": @T"+str(i)+itrstr(" proj"+str(n)+"T", i)+";")
    print ("    }.")
    print (ifpstr(n,"Arguments exist"+str(n)+"T "+ifpstr(n,"{"+itrstr(" T",n)+"}")+ifpstr(n-1," ["+itrstr(" proj"+str(n)+"T",n-1) +"]")+"."))
    print ("Definition uncurry"+str(n)+" "+ifpstr(n,"{"+itrstr(" T",n)+"}")+" (R: rel"+str(n)+itrstr(" T",n)+"): rel1 sig"+str(n)+"T :=")
    print ("  fun x => R"+itrstr(" (proj"+str(n)+"T", n, " x)")+".")
    print ("Definition curry"+str(n)+" "+ifpstr(n,"{"+itrstr(" T",n)+"}")+" (R: rel1 sig"+str(n)+"T): rel"+str(n)+itrstr(" T", n)+" :=")
    print ("  "+ifpstr(n, "fun"+itrstr(" x", n)+" => ")+"R (exist"+str(n)+"T"+ifpstr(n, " x"+str(n-1))+").")
    print()

print ("(** ** Bottom *)")
print ()
print ("Definition pacoid {A : Type} (a: A) : A := a.")
print ()
for n in range (relsize+1):
    print ("Notation bot"+str(n)+" :=")
    print ("  (pacoid(curry"+str(n)+"(fun _ => False))).")
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

print ("(** ** Intersection *)")
print ()
for n in range (relsize+1):
    print ("Notation \"p /"+str(n)+"\\ q\" :=")
    print ("  ("+ifpstr(n,"fun")+itrstr(" x",n)+ifpstr(n," => ")+"p"+itrstr(" x",n)+" /\\ q"+itrstr(" x",n)+")")
    print ("  (at level 50, no associativity"+ifzstr(n,", only parsing")+").")
    print ()

