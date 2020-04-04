from __future__ import print_function
import sys
from pacolib import *
if len(sys.argv) < 2:
    sys.stderr.write("\nUsage: "+sys.argv[0]+" relsize\n\n")
    sys.exit(1)
n = int(sys.argv[1])

print ("""
Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal paco_currying.
From Paco Require Export paconotation.
Set Implicit Arguments.

Generalizable Variables T.
""")
print ("Module Import paco"+str(n)+".")
print ("Section PACO.")
print ("")
if 1 == n:
    print ("Context {T0 : Type}.")
    print ("")
elif 1 < n:
    print ("Context `{T"+str(n-1)+" : forall", end="")
    for j in range(n-1):
        print (" (x"+str(j)+": @T"+str(j)+itrstr(" x",j)+")",end="")
    print (", Type}.")
    print ("")
print ("Local Open Scope paco_scope.")
print ("Local Notation rel := (rel"+str(n)+itrstr(" T", n)+").")
print ("Local Notation \"r <= r'\" := (r <"+str(n)+"= r') : paco_scope.")
print ("Local Notation \"r <1= r'\" := (r <"+str(n+1)+"= r') : paco_scope.")
print ("Local Notation \"r \\/ r'\" := (r \\"+str(n)+"/ r') : paco_scope.")
print ("Local Notation \"r \\1/ r'\" := (r \\"+str(n+1)+"/ r') : paco_scope.")
print ("")
print ("(** ** Predicates of Arity "+str(n)+" *)")
print ("")
print ("Let t : arityn "+str(n)+" := Eval compute in (")
for i in range(n):
    print ("    aritynS (@T"+str(i), end="")
    for j in range(i):
        print (" x"+str(j), end="")
    print (") (fun x"+str(i)+" =>")
print ("    arityn0", end="")
for i in range(n):
    print(")", end="")
print (").")
print ("")
print ("""
Definition _paco (gf : rel -> rel) (r : rel) : rel :=
  _paco (t := t) gf r.
Arguments _paco : clear implicits.
""")
print ("Inductive paco"+str(n)+" (gf : rel -> rel) (r : rel) "+itrstr(" x", n)+" : Prop :=")
print ("  internal_mk_paco (_ : _paco gf r"+itrstr(" x", n)+").")
print ("")
print ("Definition upaco"+str(n)+" (gf : rel -> rel) (r : rel) : rel := paco"+str(n)+" gf r \\/ r.")
print ("Arguments paco"+str(n)+" : clear implicits.")
print ("Arguments upaco"+str(n)+" : clear implicits.")
print ("Hint Unfold upaco"+str(n)+" : core.")
print ("")
print ("Local Notation bot := bot"+str(n)+".")
print ("Local Notation paco := paco"+str(n)+".")
print ("Local Notation upaco := upaco"+str(n)+".")
print ("""
Let unpaco gf r :
  (paco gf r) <= (_paco gf r).
Proof. destruct 1; assumption. Qed.

Lemma spec_proof :
  let le (r r' : rel) : Prop := r <= r' in
  paco_spec (rel_ := rel) le bot paco upaco.
Proof. Time apply (paco_spec_proof t); [ exact internal_mk_paco | exact unpaco ]. Time Qed.

Definition monotone (gf: rel -> rel) :=
  forall r r' (LE: r <= r'), gf r <= gf r'.

Lemma monotone_compose : forall (gf gf': rel -> rel)
      (MON1: monotone gf)
      (MON2: monotone gf'),
  monotone (compose gf gf').
Proof. exact (_monotone_compose (t := t)). Qed.

Lemma monotone_union : forall (gf gf': rel -> rel)
      (MON1: monotone gf)
      (MON2: monotone gf'),
  monotone (gf \\1/ gf').
Proof. exact (_monotone_union (t := t)). Qed.

Lemma mon_gen : forall (gf gf': rel -> rel)
    (LEgf: gf <1= gf')
    r r' (LEr: r <= r'),
  paco gf r <= paco gf' r'.
Proof. exact (_paco_mon_gen spec_proof). Qed.

Lemma mon_bot : forall (gf gf': rel -> rel) r'
    (LEgf: gf <1= gf'),
  paco gf bot <= paco gf' r'.
Proof. exact (_paco_mon_bot spec_proof). Qed.

Lemma u_mon_gen : forall (gf gf': rel -> rel)
    (LEgf: gf <1= gf')
    r r' (LEr: r <= r'),
  upaco gf r <= upaco gf' r'.
Proof. exact (_upaco_mon_gen spec_proof). Qed.

Lemma u_mon_bot : forall (gf gf': rel -> rel) r'
    (LEgf: gf <1= gf'),
  upaco gf bot <= upaco gf' r'.
Proof. exact (_upaco_mon_bot spec_proof). Qed.

Section Arg.

Variable gf : rel -> rel.
Arguments gf : clear implicits.

Theorem acc: forall
  l r (OBG: forall rr (INC: r <= rr) (CIH: l <= rr), l <= paco gf rr),
  l <= paco gf r.
Proof. exact (_paco_acc spec_proof gf). Qed.

Theorem mon: monotone (paco gf).
Proof. exact (_paco_mon spec_proof gf). Qed.

Theorem u_mon: monotone (upaco gf).
Proof. exact (_upaco_mon spec_proof gf). Qed.

Theorem mult_strong: forall r,
  paco gf (upaco gf r) <= paco gf r.
Proof. exact (_paco_mult_strong spec_proof gf). Qed.

Corollary mult: forall r,
  paco gf (paco gf r) <= paco gf r.
Proof. exact (_paco_mult spec_proof gf). Qed.

Theorem fold: forall r,
  gf (upaco gf r) <= paco gf r.
Proof. exact (_paco_fold spec_proof gf). Qed.

Theorem unfold: forall (MON: monotone gf) r,
  paco gf r <= gf (upaco gf r).
Proof. exact (_paco_unfold spec_proof gf). Qed.

End Arg.

""")
print ("Definition inst (gf : rel->_) r"+itrstr(" x", n)+" : paco_class (paco gf r"+itrstr(" x", n)+") := {|")
print ("""
  pacoacc    := @acc gf;
  pacomult   := @mult gf;
  pacofold   := @fold gf;
  pacounfold := @unfold gf |}.

End PACO.
""")
print ("End paco"+str(n)+".")
print ("")
print ("Hint Unfold upaco"+str(n)+" : core.")
print ("Hint Resolve fold : core.")
print ("Hint Unfold monotone : core.")
print ("Existing Instance inst.")
print ("")
print ("Notation paco"+str(n)+" := paco"+str(n)+".paco"+str(n)+".")
print ("Notation upaco"+str(n)+" := paco"+str(n)+".upaco"+str(n)+".")
print ("Notation monotone"+str(n)+" := paco"+str(n)+".monotone.")
