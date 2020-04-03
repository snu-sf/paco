from __future__ import print_function
import sys
from pacolib import *
if len(sys.argv) < 2:
    sys.stderr.write("\nUsage: "+sys.argv[0]+" relsize\n\n")
    sys.exit(1)
n = int(sys.argv[1])

print ("Require Export Program.Basics. Open Scope program_scope.")
print ("From Paco Require Import paconotation_internal paco_internal pacotac_internal paco_currying.")
print ("From Paco Require Export paconotation.")
print ("Set Implicit Arguments.")
print ("")
print ("Section PACO"+str(n)+".")
print ("")
for i in range(n):
    print ("Variable T"+str(i)+" : "+ifpstr(i,"forall"),end="")
    for j in range(i):
        print (" (x"+str(j)+": @T"+str(j)+itrstr(" x",j)+")",end="")
    print (ifpstr(i,", ")+"Type.")
print ("")
print ("(** ** Predicates of Arity "+str(n)+"")
print ("*)")
print ("")
print ("Notation t := (")
for i in range(n):
    print ("    arityS (@T"+str(i), end="")
    for j in range(i):
        print (" x"+str(j), end="")
    print (") (fun x"+str(i)+" =>")
print ("    arity0", end="")
for i in range(n):
    print(")", end="")
print (").")
print ("")
print ("Definition paco"+str(n)+"(gf : rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+")(r: rel"+str(n)+""+itrstr(" T", n)+") : rel"+str(n)+""+itrstr(" T", n)+" :=")
print ("  _paco (t := t) gf r.")
print ("")
print ("Definition upaco"+str(n)+"(gf : rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+")(r: rel"+str(n)+""+itrstr(" T", n)+") := paco"+str(n)+" gf r \\"+str(n)+"/ r.")
print ("Arguments paco"+str(n)+" : clear implicits.")
print ("Arguments upaco"+str(n)+" : clear implicits.")
print ("Hint Unfold upaco"+str(n)+" : core.")
print ("")
print ("Definition monotone"+str(n)+" (gf: rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+") :=")
print ("  forall r r' (LE: r <"+str(n)+"= r'), gf r <"+str(n)+"= gf r'.")
print ("")
print ("Lemma monotone"+str(n)+"_compose : forall (gf gf': rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+")")
print ("      (MON1: monotone"+str(n)+" gf)")
print ("      (MON2: monotone"+str(n)+" gf'),")
print ("  monotone"+str(n)+" (compose gf gf').")
print ("Proof.")
print ("  exact (_monotone_compose (t := t)).")
print ("Qed.")
print ("")
print ("Lemma monotone"+str(n)+"_union : forall (gf gf': rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+")")
print ("      (MON1: monotone"+str(n)+" gf)")
print ("      (MON2: monotone"+str(n)+" gf'),")
print ("  monotone"+str(n)+" (gf \\"+str(n+1)+"/ gf').")
print ("Proof.")
print ("  exact (_monotone_union (t := t)).")
print ("Qed.")
print ("")
print ("Lemma paco"+str(n)+"_mon_gen : forall (gf gf': rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+")")
print ("    (LEgf: gf <"+str(n+1)+"= gf')")
print ("    r r' (LEr: r <"+str(n)+"= r'),")
print ("  paco"+str(n)+" gf r <"+str(n)+"= paco"+str(n)+" gf' r'.")
print ("Proof.")
print ("  exact (_paco_mon_gen (t := t)).")
print ("Qed.")
print ("")
print ("Lemma paco"+str(n)+"_mon_bot : forall (gf gf': rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+") r'")
print ("    (LEgf: gf <"+str(n+1)+"= gf'),")
print ("  paco"+str(n)+" gf bot"+str(n)+" <"+str(n)+"= paco"+str(n)+" gf' r'.")
print ("Proof.")
print ("  exact (_paco_mon_bot (t := t)).")
print ("Qed.")
print ("")
print ("Lemma upaco"+str(n)+"_mon_gen : forall (gf gf': rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+")")
print ("    (LEgf: gf <"+str(n+1)+"= gf')")
print ("    r r' (LEr: r <"+str(n)+"= r'),")
print ("  upaco"+str(n)+" gf r <"+str(n)+"= upaco"+str(n)+" gf' r'.")
print ("Proof.")
print ("  exact (_upaco_mon_gen (t := t)).")
print ("Qed.")
print ("")
print ("Lemma upaco"+str(n)+"_mon_bot : forall (gf gf': rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+") r'")
print ("    (LEgf: gf <"+str(n+1)+"= gf'),")
print ("  upaco"+str(n)+" gf bot"+str(n)+" <"+str(n)+"= upaco"+str(n)+" gf' r'.")
print ("Proof.")
print ("  exact (_upaco_mon_bot (t := t)).")
print ("Qed.")
print ("")
print ("Section Arg"+str(n)+".")
print ("")
print ("Variable gf : rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+".")
print ("Arguments gf : clear implicits.")
print ("")
print ("Theorem paco"+str(n)+"_acc: forall")
print ("  l r (OBG: forall rr (INC: r <"+str(n)+"= rr) (CIH: l <"+str(n)+"= rr), l <"+str(n)+"= paco"+str(n)+" gf rr),")
print ("  l <"+str(n)+"= paco"+str(n)+" gf r.")
print ("Proof.")
print ("  exact (_paco_acc (t := t) gf).")
print ("Qed.")
print ("")
print ("Theorem paco"+str(n)+"_mon: monotone"+str(n)+" (paco"+str(n)+" gf).")
print ("Proof.")
print ("  exact (_paco_mon (t := t) gf).")
print ("Qed.")
print ("")
print ("Theorem upaco"+str(n)+"_mon: monotone"+str(n)+" (upaco"+str(n)+" gf).")
print ("Proof.")
print ("  exact (_upaco_mon (t := t) gf).")
print ("Qed.")
print ("")
print ("Theorem paco"+str(n)+"_mult_strong: forall r,")
print ("  paco"+str(n)+" gf (upaco"+str(n)+" gf r) <"+str(n)+"= paco"+str(n)+" gf r.")
print ("Proof.")
print ("  exact (_paco_mult_strong (t := t) gf).")
print ("Qed.")
print ("")
print ("Corollary paco"+str(n)+"_mult: forall r,")
print ("  paco"+str(n)+" gf (paco"+str(n)+" gf r) <"+str(n)+"= paco"+str(n)+" gf r.")
print ("Proof.")
print ("  exact (_paco_mult (t := t) gf).")
print ("Qed.")
print ("")
print ("Theorem paco"+str(n)+"_fold: forall (MON: monotone"+str(n)+" gf) r,")
print ("  gf (upaco"+str(n)+" gf r) <"+str(n)+"= paco"+str(n)+" gf r.")
print ("Proof.")
print ("  exact (_paco_fold (t := t) gf).")
print ("Qed.")
print ("")
print ("Theorem paco"+str(n)+"_unfold: forall (MON: monotone"+str(n)+" gf) r,")
print ("  paco"+str(n)+" gf r <"+str(n)+"= gf (upaco"+str(n)+" gf r).")
print ("Proof.")
print ("  exact (_paco_unfold (t := t) gf).")
print ("Qed.")
print ("")
print ("End Arg"+str(n)+".")
print ("")
print ("Arguments paco"+str(n)+"_acc : clear implicits.")
print ("Arguments paco"+str(n)+"_mon : clear implicits.")
print ("Arguments upaco"+str(n)+"_mon : clear implicits.")
print ("Arguments paco"+str(n)+"_mult_strong : clear implicits.")
print ("Arguments paco"+str(n)+"_mult : clear implicits.")
print ("Arguments paco"+str(n)+"_fold : clear implicits.")
print ("Arguments paco"+str(n)+"_unfold : clear implicits.")
print ("")
print ("Global Instance paco"+str(n)+"_inst  (gf : rel"+str(n)+""+itrstr(" T", n)+"->_) r"+itrstr(" x", n)+" : paco_class (paco"+str(n)+" gf r"+itrstr(" x", n)+") :=")
print ("{ pacoacc    := paco"+str(n)+"_acc gf;")
print ("  pacomult   := paco"+str(n)+"_mult gf;")
print ("  pacofold   := paco"+str(n)+"_fold gf;")
print ("  pacounfold := paco"+str(n)+"_unfold gf }.")
print ("")
print ("End PACO"+str(n)+".")
print ("")
print ("Global Opaque paco"+str(n)+".")
print ("")
print ("Hint Unfold upaco"+str(n)+" : core.")
print ("Hint Resolve paco"+str(n)+"_fold : core.")
print ("Hint Unfold monotone"+str(n)+" : core.")
print ("")
