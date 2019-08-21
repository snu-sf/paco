from __future__ import print_function
import sys
from pacolib import *

if len(sys.argv) < 2:
    sys.stderr.write('\nUsage: '+sys.argv[0]+' relsize\n\n')
    sys.exit(1)

relsize = int(sys.argv[1])

print ("From Paco Require Import paconotation.")
print ("")

print ("(** ** Less than or equal *)")
print ()
for n in range (relsize+1):
    print ("Definition le"+str(n)+itrstr(" T",n)+" (p q : rel"+str(n)+itrstr(" T",n)+") :=")
    print ("  (forall"+itrstr(" x",n)+" (PR: p"+itrstr(" x",n)+" : Prop), q"+itrstr(" x",n)+" : Prop).")
    print ("Arguments le"+str(n)+ifpstr(n, " ["+itrstr(" T",n)+"] p q.", " : clear implicits."))
    print ()

for n in range (relsize+1):
    print ("Notation \"p <"+str(n)+"== q\" :=")
    print ("  (le"+str(n)+" p q)")
    print ("  (at level 50, no associativity"+ifzstr(n,", only parsing")+").")
    print ()

print ("(** ** Tranisitivity and Reflexivity *)")
print ()
for n in range (relsize+1):
    print ("Lemma le"+str(n)+"_trans"+itrstr(" T",n)+"(r0 r1 r2 : rel"+str(n)+itrstr(" T",n)+")")
    print ("      (LE0 : r0 <"+str(n)+"== r1) (LE1 : r1 <"+str(n)+"== r2) :")
    print ("  r0 <"+str(n)+"== r2.")
    print ("Proof. do "+str(n)+" intro. intros H. eapply LE1, LE0, H. Qed.")
    print ()

for n in range (relsize+1):
    print ("Lemma le"+str(n)+"_refl"+itrstr(" T",n)+"(r : rel"+str(n)+itrstr(" T",n)+") :")
    print ("  r <"+str(n)+"== r.")
    print ("Proof. do "+str(n)+" intro. intros H. apply H. Qed.")
    print ()
