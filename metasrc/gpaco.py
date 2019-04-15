from __future__ import print_function
import sys
from pacolib import *
if len(sys.argv) < 2:
    sys.stderr.write("\nUsage: "+sys.argv[0]+" relsize\n\n")
    sys.exit(1)
n = int(sys.argv[1])

print ("Require Export Program.Basics. Open Scope program_scope.")
print ("Require Import paco"+str(n)+" pacotac.")
print ("Set Implicit Arguments.")
print ("")
print ("Section GeneralizedPaco"+str(n)+".")
print ("")
for i in range(n):
    print ("Variable T"+str(i)+" : "+ifpstr(i,"forall"),end="")
    for j in range(i):
        print (" (x"+str(j)+": @T"+str(j)+itrstr(" x",j)+")",end="")
    print (ifpstr(i,", ")+"Type.")
print ("")
print ("Local Notation rel := (rel"+str(n)+""+itrstr(" T", n)+").")
print ("")
print ("Lemma monotone"+str(n)+"_compose (clo1 clo2: rel -> rel)")
print ("      (MON1: monotone"+str(n)+" clo1)")
print ("      (MON2: monotone"+str(n)+" clo2):")
print ("  monotone"+str(n)+" (compose clo1 clo2).")
print ("Proof.")
print ("  red; intros. eapply MON1. apply IN.")
print ("  intros. eapply MON2. apply PR. apply LE.")
print ("Qed.")
print ("")
print ("Lemma monotone"+str(n)+"_union (clo1 clo2: rel -> rel)")
print ("      (MON1: monotone"+str(n)+" clo1)")
print ("      (MON2: monotone"+str(n)+" clo2):")
print ("  monotone"+str(n)+" (clo1 \\"+str(n+1)+"/ clo2).")
print ("Proof.")
print ("  red; intros. destruct IN.")
print ("  - left. eapply MON1. apply H. apply LE.")
print ("  - right. eapply MON2. apply H. apply LE.")
print ("Qed.")
print ("")
print ("Section RClo.")
print ("")
print ("Inductive rclo"+str(n)+" (clo: rel->rel) (r: rel): rel :=")
print ("| rclo"+str(n)+"_base")
print ("   "+itrstr(" x", n)+"")
print ("    (IN: r"+itrstr(" x", n)+"):")
print ("    @rclo"+str(n)+" clo r"+itrstr(" x", n)+"")
print ("| rclo"+str(n)+"_clo'")
print ("    r'"+itrstr(" x", n)+"")
print ("    (LE: r' <"+str(n)+"= rclo"+str(n)+" clo r)")
print ("    (IN: clo r'"+itrstr(" x", n)+"):")
print ("    @rclo"+str(n)+" clo r"+itrstr(" x", n)+"")
print (".           ")
print ("")
print ("Lemma rclo"+str(n)+"_mon_gen clo clo' r r'"+itrstr(" x", n)+"")
print ("      (IN: @rclo"+str(n)+" clo r"+itrstr(" x", n)+")")
print ("      (LEclo: clo <"+str(n+1)+"= clo')")
print ("      (LEr: r <"+str(n)+"= r') :")
print ("  @rclo"+str(n)+" clo' r'"+itrstr(" x", n)+".")
print ("Proof.")
print ("  induction IN; intros.")
print ("  - econstructor 1. apply LEr, IN.")
print ("  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].")
print ("Qed.")
print ("")
print ("Lemma rclo"+str(n)+"_mon clo:")
print ("  monotone"+str(n)+" (rclo"+str(n)+" clo).")
print ("Proof.")
print ("  repeat intro. eapply rclo"+str(n)+"_mon_gen; [apply IN|intros; apply PR|apply LE].")
print ("Qed.")
print ("")
print ("Lemma rclo"+str(n)+"_clo clo r:")
print ("  clo (rclo"+str(n)+" clo r) <"+str(n)+"= rclo"+str(n)+" clo r.")
print ("Proof.")
print ("  intros. econstructor 2; [|apply PR]. ")
print ("  intros. apply PR0.")
print ("Qed.")
print ("")
print ("Lemma rclo"+str(n)+"_rclo clo r:")
print ("  rclo"+str(n)+" clo (rclo"+str(n)+" clo r) <"+str(n)+"= rclo"+str(n)+" clo r.")
print ("Proof.")
print ("  intros. induction PR.")
print ("  - eapply IN.")
print ("  - econstructor 2; [eapply H | eapply IN].")
print ("Qed.")
print ("")
print ("Lemma rclo"+str(n)+"_compose clo r:")
print ("  rclo"+str(n)+" (rclo"+str(n)+" clo) r <"+str(n)+"= rclo"+str(n)+" clo r.")
print ("Proof.")
print ("  intros. induction PR.")
print ("  - apply rclo"+str(n)+"_base, IN.")
print ("  - apply rclo"+str(n)+"_rclo.")
print ("    eapply rclo"+str(n)+"_mon; [apply IN|apply H].")
print ("Qed.")
print ("")
print ("End RClo.  ")
print ("")
print ("Section Main.")
print ("")
print ("Variable gf: rel -> rel.")
print ("Hypothesis gf_mon: monotone"+str(n)+" gf.")
print ("")
print ("Variant gpaco"+str(n)+" clo r rg"+itrstr(" x", n)+" : Prop :=")
print ("| gpaco"+str(n)+"_intro (IN: @rclo"+str(n)+" clo (paco"+str(n)+" (compose gf (rclo"+str(n)+" clo)) (rg \\"+str(n)+"/ r) \\"+str(n)+"/ r)"+itrstr(" x", n)+")")
print (".")
print ("")
print ("Definition gupaco"+str(n)+" clo r := gpaco"+str(n)+" clo r r.")
print ("")
print ("Lemma gpaco"+str(n)+"_def_mon clo : monotone"+str(n)+" (compose gf (rclo"+str(n)+" clo)).")
print ("Proof.")
print ("  eapply monotone"+str(n)+"_compose. apply gf_mon. apply rclo"+str(n)+"_mon.")
print ("Qed.")
print ("")
print ("Hint Resolve gpaco"+str(n)+"_def_mon : paco.")
print ("")
print ("Lemma gpaco"+str(n)+"_mon clo r r' rg rg'"+itrstr(" x", n)+"")
print ("      (IN: @gpaco"+str(n)+" clo r rg"+itrstr(" x", n)+")")
print ("      (LEr: r <"+str(n)+"= r')")
print ("      (LErg: rg <"+str(n)+"= rg'):")
print ("  @gpaco"+str(n)+" clo r' rg'"+itrstr(" x", n)+".")
print ("Proof.")
print ("  destruct IN. econstructor.")
print ("  eapply rclo"+str(n)+"_mon. apply IN.")
print ("  intros. destruct PR; [|right; apply LEr, H].")
print ("  left. eapply paco"+str(n)+"_mon. apply H.")
print ("  intros. destruct PR.")
print ("  - left. apply LErg, H0.")
print ("  - right. apply LEr, H0.")
print ("Qed.")
print ("")
print ("Lemma gupaco"+str(n)+"_mon clo r r'"+itrstr(" x", n)+"")
print ("      (IN: @gupaco"+str(n)+" clo r"+itrstr(" x", n)+")")
print ("      (LEr: r <"+str(n)+"= r'):")
print ("  @gupaco"+str(n)+" clo r'"+itrstr(" x", n)+".")
print ("Proof.")
print ("  eapply gpaco"+str(n)+"_mon. apply IN. apply LEr. apply LEr.")
print ("Qed.")
print ("")
print ("Lemma gpaco"+str(n)+"_base clo r rg: r <"+str(n)+"= gpaco"+str(n)+" clo r rg.")
print ("Proof.")
print ("  econstructor. apply rclo"+str(n)+"_base. right. apply PR.")
print ("Qed.")
print ("")
print ("Lemma gpaco"+str(n)+"_rclo clo r:")
print ("  rclo"+str(n)+" clo r <"+str(n)+"= gupaco"+str(n)+" clo r.")
print ("Proof.")
print ("  intros. econstructor.")
print ("  eapply rclo"+str(n)+"_mon. apply PR.")
print ("  intros. right. apply PR0.")
print ("Qed.")
print ("")
print ("Lemma gpaco"+str(n)+"_clo clo r:")
print ("  clo r <"+str(n)+"= gupaco"+str(n)+" clo r.")
print ("Proof.")
print ("  intros. apply gpaco"+str(n)+"_rclo. eapply rclo"+str(n)+"_clo', PR.")
print ("  apply rclo"+str(n)+"_base.")
print ("Qed.")
print ("")
print ("Lemma gpaco"+str(n)+"_step_gen clo r rg:")
print ("  gf (gpaco"+str(n)+" clo (rg \\"+str(n)+"/ r) (rg \\"+str(n)+"/ r)) <"+str(n)+"= gpaco"+str(n)+" clo r rg.")
print ("Proof.")
print ("  intros. econstructor. apply rclo"+str(n)+"_base. left.")
print ("  pstep. eapply gf_mon. apply PR.")
print ("  intros. destruct PR0. eapply rclo"+str(n)+"_mon. apply IN.")
print ("  intros. destruct PR0.")
print ("  - left. eapply paco"+str(n)+"_mon. apply H. intros. destruct PR0; apply H0.")
print ("  - right. apply H.")
print ("Qed.")
print ("")
print ("Lemma gpaco"+str(n)+"_step clo r rg:")
print ("  gf (gpaco"+str(n)+" clo rg rg) <"+str(n)+"= gpaco"+str(n)+" clo r rg.")
print ("Proof.")
print ("  intros. apply gpaco"+str(n)+"_step_gen.")
print ("  eapply gf_mon. apply PR. intros.")
print ("  eapply gpaco"+str(n)+"_mon. apply PR0. left; apply PR1. left; apply PR1.")
print ("Qed.")
print ("")
print ("Lemma gpaco"+str(n)+"_final clo r rg:")
print ("  (r \\"+str(n)+"/ paco"+str(n)+" gf rg) <"+str(n)+"= gpaco"+str(n)+" clo r rg.")
print ("Proof.")
print ("  intros. destruct PR. apply gpaco"+str(n)+"_base, H.")
print ("  econstructor. apply rclo"+str(n)+"_base.")
print ("  left. eapply paco"+str(n)+"_mon_gen. apply H.")
print ("  - intros. eapply gf_mon. apply PR.")
print ("    intros. apply rclo"+str(n)+"_base. apply PR0.")
print ("  - intros. left. apply PR.")
print ("Qed.")
print ("")
print ("Lemma gpaco"+str(n)+"_unfold clo r rg:")
print ("  gpaco"+str(n)+" clo r rg <"+str(n)+"= rclo"+str(n)+" clo (gf (gupaco"+str(n)+" clo (rg \\"+str(n)+"/ r)) \\"+str(n)+"/ r).")
print ("Proof.")
print ("  intros. destruct PR.")
print ("  eapply rclo"+str(n)+"_mon. apply IN.")
print ("  intros. destruct PR; cycle 1. right; apply H.")
print ("  left. _punfold H; [|apply gpaco"+str(n)+"_def_mon].")
print ("  eapply gf_mon. apply H.")
print ("  intros. econstructor.")
print ("  eapply rclo"+str(n)+"_mon. apply PR.")
print ("  intros. destruct PR0; cycle 1. right. apply H0.")
print ("  left. eapply paco"+str(n)+"_mon. apply H0.")
print ("  intros. left. apply PR0.")
print ("Qed.")
print ("  ")
print ("Lemma gpaco"+str(n)+"_cofix clo r rg ")
print ("      l (OBG: forall rr (INC: rg <"+str(n)+"= rr) (CIH: l <"+str(n)+"= rr), l <"+str(n)+"= gpaco"+str(n)+" clo r rr):")
print ("  l <"+str(n)+"= gpaco"+str(n)+" clo r rg.")
print ("Proof.")
print ("  assert (IN: l <"+str(n)+"= gpaco"+str(n)+" clo r (rg \\"+str(n)+"/ l)).")
print ("  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }")
print ("  clear OBG. intros. apply IN in PR.")
print ("  destruct PR. econstructor.")
print ("  eapply rclo"+str(n)+"_mon. apply IN0.")
print ("  clear"+itrstr(" x", n)+" IN0.")
print ("  intros. destruct PR; [|right; apply H].")
print ("  left. revert"+itrstr(" x", n)+" H.")
print ("  pcofix CIH. intros.")
print ("  _punfold H0; [..|apply gpaco"+str(n)+"_def_mon]. pstep.")
print ("  eapply gf_mon. apply H0. intros.")
print ("  apply rclo"+str(n)+"_rclo. eapply rclo"+str(n)+"_mon. apply PR.")
print ("  intros. destruct PR0.")
print ("  - apply rclo"+str(n)+"_base. right. apply CIH. apply H.")
print ("  - destruct H; [destruct H|].")
print ("    + apply rclo"+str(n)+"_base. right. apply CIH0. left. apply H.")
print ("    + apply IN in H. destruct H.")
print ("      eapply rclo"+str(n)+"_mon. apply IN0.")
print ("      intros. destruct PR0.")
print ("      * right. apply CIH. apply H.      ")
print ("      * right. apply CIH0. right. apply H.")
print ("    + apply rclo"+str(n)+"_base. right. apply CIH0. right. apply H.")
print ("Qed.")
print ("")
print ("Lemma gpaco"+str(n)+"_gupaco clo r rg:")
print ("  gupaco"+str(n)+" clo (gpaco"+str(n)+" clo r rg) <"+str(n)+"= gpaco"+str(n)+" clo r rg.")
print ("Proof.")
print ("  eapply gpaco"+str(n)+"_cofix.")
print ("  intros. destruct PR. econstructor.")
print ("  apply rclo"+str(n)+"_rclo. eapply rclo"+str(n)+"_mon. apply IN.")
print ("  intros. destruct PR.")
print ("  - apply rclo"+str(n)+"_base. left.")
print ("    eapply paco"+str(n)+"_mon. apply H.")
print ("    intros. left; apply CIH.")
print ("    econstructor. apply rclo"+str(n)+"_base. right.")
print ("    destruct PR; apply H0.")
print ("  - destruct H. eapply rclo"+str(n)+"_mon. apply IN0.")
print ("    intros. destruct PR; [| right; apply H].")
print ("    left. eapply paco"+str(n)+"_mon. apply H.")
print ("    intros. destruct PR.")
print ("    + left. apply INC. apply H0.")
print ("    + right. apply H0.")
print ("Qed.")
print ("")
print ("Lemma gpaco"+str(n)+"_uclo uclo clo r rg ")
print ("      (LEclo: uclo <"+str(n+1)+"= gupaco"+str(n)+" clo) :")
print ("  uclo (gpaco"+str(n)+" clo r rg) <"+str(n)+"= gpaco"+str(n)+" clo r rg.")
print ("Proof.")
print ("  intros. apply gpaco"+str(n)+"_gupaco. apply LEclo, PR.")
print ("Qed.")
print ("")
print ("Lemma gpaco"+str(n)+"_weaken  clo r rg:")
print ("  gpaco"+str(n)+" (gupaco"+str(n)+" clo) r rg <"+str(n)+"= gpaco"+str(n)+" clo r rg.")
print ("Proof.")
print ("  intros. apply gpaco"+str(n)+"_unfold in PR.")
print ("  induction PR.")
print ("  - destruct IN; cycle 1. apply gpaco"+str(n)+"_base, H.")
print ("    apply gpaco"+str(n)+"_step_gen. eapply gf_mon. apply H.")
print ("    clear"+itrstr(" x", n)+" H.")
print ("    eapply gpaco"+str(n)+"_cofix. intros.")
print ("    apply gpaco"+str(n)+"_unfold in PR.")
print ("    induction PR.")
print ("    + destruct IN; cycle 1. apply gpaco"+str(n)+"_base, H.")
print ("      apply gpaco"+str(n)+"_step. eapply gf_mon. apply H.")
print ("      intros. apply gpaco"+str(n)+"_base. apply CIH.")
print ("      eapply gupaco"+str(n)+"_mon. apply PR.")
print ("      intros. destruct PR0; apply H0.")
print ("    + apply gpaco"+str(n)+"_gupaco.")
print ("      eapply gupaco"+str(n)+"_mon. apply IN. apply H.")
print ("  - apply gpaco"+str(n)+"_gupaco.")
print ("    eapply gupaco"+str(n)+"_mon. apply IN. apply H.")
print ("Qed.")
print ("")
print ("End Main.")
print ("")
print ("Hint Resolve gpaco"+str(n)+"_def_mon : paco.")
print ("")
print ("Section GeneralMonotonicity.")
print ("")
print ("Variable gf: rel -> rel.")
print ("Hypothesis gf_mon: monotone"+str(n)+" gf.")
print ("  ")
print ("Lemma gpaco"+str(n)+"_mon_gen (gf' clo clo': rel -> rel)"+itrstr(" x", n)+" r r' rg rg'")
print ("      (IN: @gpaco"+str(n)+" gf clo r rg"+itrstr(" x", n)+")")
print ("      (LEgf: gf <"+str(n+1)+"= gf')")
print ("      (LEclo: clo <"+str(n+1)+"= clo')")
print ("      (LEr: r <"+str(n)+"= r')")
print ("      (LErg: rg <"+str(n)+"= rg') :")
print ("  @gpaco"+str(n)+" gf' clo' r' rg'"+itrstr(" x", n)+".")
print ("Proof.")
print ("  eapply gpaco"+str(n)+"_mon; [|apply LEr|apply LErg].")
print ("  destruct IN. econstructor.")
print ("  eapply rclo"+str(n)+"_mon_gen. apply IN. apply LEclo.")
print ("  intros. destruct PR; [| right; apply H].")
print ("  left. eapply paco"+str(n)+"_mon_gen. apply H.")
print ("  - intros. eapply LEgf.")
print ("    eapply gf_mon. apply PR.")
print ("    intros. eapply rclo"+str(n)+"_mon_gen. apply PR0. apply LEclo. intros; apply PR1.")
print ("  - intros. apply PR.")
print ("Qed.")
print ("")
print ("Lemma gpaco"+str(n)+"_mon_bot (gf' clo clo': rel -> rel)"+itrstr(" x", n)+" r' rg'")
print ("      (IN: @gpaco"+str(n)+" gf clo bot"+str(n)+" bot"+str(n)+""+itrstr(" x", n)+")")
print ("      (LEgf: gf <"+str(n+1)+"= gf')")
print ("      (LEclo: clo <"+str(n+1)+"= clo'):")
print ("  @gpaco"+str(n)+" gf' clo' r' rg'"+itrstr(" x", n)+".")
print ("Proof.")
print ("  eapply gpaco"+str(n)+"_mon_gen. apply IN. apply LEgf. apply LEclo. contradiction. contradiction.")
print ("Qed.")
print ("")
print ("Lemma gupaco"+str(n)+"_mon_gen (gf' clo clo': rel -> rel)"+itrstr(" x", n)+" r r'")
print ("      (IN: @gupaco"+str(n)+" gf clo r"+itrstr(" x", n)+")")
print ("      (LEgf: gf <"+str(n+1)+"= gf')")
print ("      (LEclo: clo <"+str(n+1)+"= clo')")
print ("      (LEr: r <"+str(n)+"= r'):")
print ("  @gupaco"+str(n)+" gf' clo' r'"+itrstr(" x", n)+".")
print ("Proof.")
print ("  eapply gpaco"+str(n)+"_mon_gen. apply IN. apply LEgf. apply LEclo. apply LEr. apply LEr.")
print ("Qed.")
print ("")
print ("End GeneralMonotonicity.")
print ("")
print ("Section Compatibility.")
print ("")
print ("Variable gf: rel -> rel.")
print ("Hypothesis gf_mon: monotone"+str(n)+" gf.")
print ("")
print ("Structure compatible"+str(n)+" (clo: rel -> rel) : Prop :=")
print ("  compat"+str(n)+"_intro {")
print ("      compat"+str(n)+"_mon: monotone"+str(n)+" clo;")
print ("      compat"+str(n)+"_compat : forall r,")
print ("          clo (gf r) <"+str(n)+"= gf (clo r);")
print ("    }.")
print ("")
print ("Structure wcompatible"+str(n)+" clo : Prop :=")
print ("  wcompat"+str(n)+"_intro {")
print ("      wcompat"+str(n)+"_mon: monotone"+str(n)+" clo;")
print ("      wcompat"+str(n)+"_wcompat : forall r,")
print ("          clo (gf r) <"+str(n)+"= gf (gupaco"+str(n)+" gf clo r);")
print ("    }.")
print ("")
print ("Inductive cpn"+str(n)+" (r: rel)"+itrstr(" x", n)+" : Prop :=")
print ("| cpn"+str(n)+"_intro")
print ("    clo")
print ("    (COM: compatible"+str(n)+" clo)")
print ("    (CLO: clo r"+itrstr(" x", n)+")")
print (".")
print ("")
print ("Lemma rclo"+str(n)+"_compat clo")
print ("      (COM: compatible"+str(n)+" clo):")
print ("  compatible"+str(n)+" (rclo"+str(n)+" clo).")
print ("Proof.")
print ("  econstructor.")
print ("  - apply rclo"+str(n)+"_mon.")
print ("  - intros. induction PR.")
print ("    + eapply gf_mon. apply IN.")
print ("      intros. eapply rclo"+str(n)+"_base. apply PR.")
print ("    + eapply gf_mon.")
print ("      * eapply COM. eapply COM. apply IN. apply H.")
print ("      * intros. eapply rclo"+str(n)+"_clo. apply PR.")
print ("Qed.")
print ("")
print ("Lemma compat"+str(n)+"_wcompat clo")
print ("      (CMP: compatible"+str(n)+" clo):")
print ("  wcompatible"+str(n)+" clo.")
print ("Proof.")
print ("  econstructor. apply CMP.")
print ("  intros. apply CMP in PR.")
print ("  eapply gf_mon. apply PR.")
print ("  intros. apply gpaco"+str(n)+"_clo, PR0. ")
print ("Qed.")
print ("")
print ("Lemma wcompat"+str(n)+"_compat clo")
print ("      (WCMP: wcompatible"+str(n)+" clo) :")
print ("  compatible"+str(n)+" (gupaco"+str(n)+" gf clo).")
print ("Proof.")
print ("  econstructor.")
print ("  { red; intros. eapply gpaco"+str(n)+"_mon. apply IN. apply LE. apply LE. }")
print ("")
print ("  intros. apply gpaco"+str(n)+"_unfold in PR; [|apply gf_mon].")
print ("  induction PR.")
print ("  - destruct IN; cycle 1.")
print ("    + eapply gf_mon. apply H.")
print ("      intros. apply gpaco"+str(n)+"_base, PR.")
print ("    + eapply gf_mon. apply H.")
print ("      intros. apply gpaco"+str(n)+"_gupaco. apply gf_mon.")
print ("      eapply gupaco"+str(n)+"_mon. apply PR.")
print ("      intros. apply gpaco"+str(n)+"_step. apply gf_mon.")
print ("      eapply gf_mon. destruct PR0 as [X|X]; apply X.")
print ("      intros. apply gpaco"+str(n)+"_base, PR1.")
print ("  - eapply gf_mon, gpaco"+str(n)+"_gupaco, gf_mon.")
print ("    apply WCMP. eapply WCMP. apply IN.")
print ("    intros. apply H, PR.")
print ("Qed.")
print ("")
print ("Lemma wcompat"+str(n)+"_union clo1 clo2")
print ("      (WCMP1: wcompatible"+str(n)+" clo1)")
print ("      (WCMP2: wcompatible"+str(n)+" clo2):")
print ("  wcompatible"+str(n)+" (clo1 \\"+str(n+1)+"/ clo2).")
print ("Proof.")
print ("  econstructor.")
print ("  - apply monotone"+str(n)+"_union. apply WCMP1. apply WCMP2.")
print ("  - intros. destruct PR.")
print ("    + apply WCMP1 in H. eapply gf_mon. apply H.")
print ("      intros. eapply gupaco"+str(n)+"_mon_gen. apply gf_mon. apply PR. ")
print ("      intros; apply PR0. left; apply PR0. intros; apply PR0.")
print ("    + apply WCMP2 in H. eapply gf_mon. apply H.")
print ("      intros. eapply gupaco"+str(n)+"_mon_gen. apply gf_mon. apply PR.")
print ("      intros; apply PR0. right; apply PR0. intros; apply PR0.")
print ("Qed.")
print ("")
print ("Lemma cpn"+str(n)+"_mon: monotone"+str(n)+" cpn"+str(n)+".")
print ("Proof.")
print ("  red. intros.")
print ("  destruct IN. exists clo.")
print ("  - apply COM.")
print ("  - eapply compat"+str(n)+"_mon; [apply COM|apply CLO|apply LE].")
print ("Qed.")
print ("")
print ("Lemma cpn"+str(n)+"_greatest: forall clo (COM: compatible"+str(n)+" clo), clo <"+str(n+1)+"= cpn"+str(n)+".")
print ("Proof. intros. econstructor;[apply COM|apply PR]. Qed.")
print ("")
print ("Lemma cpn"+str(n)+"_compat: compatible"+str(n)+" cpn"+str(n)+".")
print ("Proof.")
print ("  econstructor; [apply cpn"+str(n)+"_mon|intros].")
print ("  destruct PR; eapply gf_mon with (r:=clo r).")
print ("  - eapply (compat"+str(n)+"_compat COM); apply CLO.")
print ("  - intros. econstructor; [apply COM|apply PR].")
print ("Qed.")
print ("")
print ("Lemma cpn"+str(n)+"_wcompat: wcompatible"+str(n)+" cpn"+str(n)+".")
print ("Proof. apply compat"+str(n)+"_wcompat, cpn"+str(n)+"_compat. Qed.")
print ("")
print ("Lemma cpn"+str(n)+"_uclo uclo")
print ("      (MON: monotone"+str(n)+" uclo)")
print ("      (WCOM: forall r, uclo (gf r) <"+str(n)+"= gf (gupaco"+str(n)+" gf (uclo \\"+str(n+1)+"/ cpn"+str(n)+") r)):")
print ("  uclo <"+str(n+1)+"= gupaco"+str(n)+" gf cpn"+str(n)+".")
print ("Proof.")
print ("  intros. apply gpaco"+str(n)+"_clo.")
print ("  exists (gupaco"+str(n)+" gf (uclo \\"+str(n+1)+"/ cpn"+str(n)+")).")
print ("  - apply wcompat"+str(n)+"_compat.")
print ("    econstructor.")
print ("    + apply monotone"+str(n)+"_union. apply MON. apply cpn"+str(n)+"_mon.")
print ("    + intros. destruct PR0.")
print ("      * apply WCOM, H.")
print ("      * apply compat"+str(n)+"_compat in H; [| apply cpn"+str(n)+"_compat].")
print ("        eapply gf_mon. apply H. intros.")
print ("        apply gpaco"+str(n)+"_clo. right. apply PR0.")
print ("  - apply gpaco"+str(n)+"_clo. left. apply PR.")
print ("Qed.")
print ("")
print ("End Compatibility.")
print ("")
print ("Section Soundness.")
print ("")
print ("Variable gf: rel -> rel.")
print ("Hypothesis gf_mon: monotone"+str(n)+" gf.")
print ("")
print ("Lemma gpaco"+str(n)+"_compat_init clo")
print ("      (CMP: compatible"+str(n)+" gf clo):")
print ("  gpaco"+str(n)+" gf clo bot"+str(n)+" bot"+str(n)+" <"+str(n)+"= paco"+str(n)+" gf bot"+str(n)+".")
print ("Proof.")
print ("  intros. destruct PR. revert"+itrstr(" x", n)+" IN.")
print ("  pcofix CIH. intros.")
print ("  pstep. eapply gf_mon; [| right; apply CIH, rclo"+str(n)+"_rclo, PR]. ")
print ("  apply compat"+str(n)+"_compat with (gf:=gf). apply rclo"+str(n)+"_compat. apply gf_mon. apply CMP.")
print ("  eapply rclo"+str(n)+"_mon. apply IN.")
print ("  intros. destruct PR; [|contradiction]. _punfold H; [..|apply gpaco"+str(n)+"_def_mon, gf_mon].")
print ("  eapply gpaco"+str(n)+"_def_mon. apply gf_mon. apply H.")
print ("  intros. destruct PR; [|destruct H0; contradiction]. left. apply H0.")
print ("Qed.")
print ("")
print ("Lemma gpaco"+str(n)+"_init clo")
print ("      (WCMP: wcompatible"+str(n)+" gf clo):")
print ("  gpaco"+str(n)+" gf clo bot"+str(n)+" bot"+str(n)+" <"+str(n)+"= paco"+str(n)+" gf bot"+str(n)+".")
print ("Proof.")
print ("  intros. eapply gpaco"+str(n)+"_compat_init.")
print ("  - apply wcompat"+str(n)+"_compat, WCMP. apply gf_mon.")
print ("  - eapply gpaco"+str(n)+"_mon_bot. apply gf_mon. apply PR. intros; apply PR0.")
print ("    intros. apply gpaco"+str(n)+"_clo, PR0.")
print ("Qed.")
print ("")
print ("Lemma gpaco"+str(n)+"_unfold_bot clo")
print ("      (WCMP: wcompatible"+str(n)+" gf clo):")
print ("  gpaco"+str(n)+" gf clo bot"+str(n)+" bot"+str(n)+" <"+str(n)+"= gf (gpaco"+str(n)+" gf clo bot"+str(n)+" bot"+str(n)+").")
print ("Proof.")
print ("  intros. apply gpaco"+str(n)+"_init in PR; [|apply WCMP].")
print ("  _punfold PR; [..|apply gf_mon].")
print ("  eapply gf_mon. apply PR.")
print ("  intros. destruct PR0; [|contradiction]. apply gpaco"+str(n)+"_final. apply gf_mon. right. apply H.")
print ("Qed.")
print ("")
print ("End Soundness.")
print ("")
print ("End GeneralizedPaco"+str(n)+".")
print ("")
print ("Hint Resolve gpaco"+str(n)+"_def_mon : paco.")
print ("Hint Resolve gpaco"+str(n)+"_base : paco.")
print ("Hint Resolve gpaco"+str(n)+"_step : paco.")
print ("Hint Resolve gpaco"+str(n)+"_final : paco.")
