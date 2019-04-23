Require Export Program.Basics. Open Scope program_scope.
Require Import paco14 pacotac.
Set Implicit Arguments.

Section GeneralizedPaco14.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.

Local Notation rel := (rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13).

Section RClo.

Inductive rclo14 (clo: rel->rel) (r: rel): rel :=
| rclo14_base
    x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
    (IN: r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13):
    @rclo14 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
| rclo14_clo'
    r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
    (LE: r' <14= rclo14 clo r)
    (IN: clo r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13):
    @rclo14 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
.           

Lemma rclo14_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      (IN: @rclo14 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (LEclo: clo <15= clo')
      (LEr: r <14= r') :
  @rclo14 clo' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo14_mon clo:
  monotone14 (rclo14 clo).
Proof.
  repeat intro. eapply rclo14_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo14_clo clo r:
  clo (rclo14 clo r) <14= rclo14 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo14_rclo clo r:
  rclo14 clo (rclo14 clo r) <14= rclo14 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo14_compose clo r:
  rclo14 (rclo14 clo) r <14= rclo14 clo r.
Proof.
  intros. induction PR.
  - apply rclo14_base, IN.
  - apply rclo14_rclo.
    eapply rclo14_mon; [apply IN|apply H].
Qed.

End RClo.  

Section Main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone14 gf.

Variant gpaco14 clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Prop :=
| gpaco14_intro (IN: @rclo14 clo (paco14 (compose gf (rclo14 clo)) (rg \14/ r) \14/ r) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
.

Definition gupaco14 clo r := gpaco14 clo r r.

Lemma gpaco14_def_mon clo : monotone14 (compose gf (rclo14 clo)).
Proof.
  eapply monotone14_compose. apply gf_mon. apply rclo14_mon.
Qed.

Hint Resolve gpaco14_def_mon : paco.

Lemma gpaco14_mon clo r r' rg rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      (IN: @gpaco14 clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (LEr: r <14= r')
      (LErg: rg <14= rg'):
  @gpaco14 clo r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  destruct IN. econstructor.
  eapply rclo14_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco14_mon. apply H.
  intros. destruct PR.
  - left. apply LErg, H0.
  - right. apply LEr, H0.
Qed.

Lemma gupaco14_mon clo r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      (IN: @gupaco14 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (LEr: r <14= r'):
  @gupaco14 clo r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  eapply gpaco14_mon. apply IN. apply LEr. apply LEr.
Qed.

Lemma gpaco14_base clo r rg: r <14= gpaco14 clo r rg.
Proof.
  econstructor. apply rclo14_base. right. apply PR.
Qed.

Lemma gpaco14_rclo clo r:
  rclo14 clo r <14= gupaco14 clo r.
Proof.
  intros. econstructor.
  eapply rclo14_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco14_clo clo r:
  clo r <14= gupaco14 clo r.
Proof.
  intros. apply gpaco14_rclo. eapply rclo14_clo', PR.
  apply rclo14_base.
Qed.

Lemma gpaco14_step_gen clo r rg:
  gf (gpaco14 clo (rg \14/ r) (rg \14/ r)) <14= gpaco14 clo r rg.
Proof.
  intros. econstructor. apply rclo14_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo14_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco14_mon. apply H. intros. destruct PR0; apply H0.
  - right. apply H.
Qed.

Lemma gpaco14_step clo r rg:
  gf (gpaco14 clo rg rg) <14= gpaco14 clo r rg.
Proof.
  intros. apply gpaco14_step_gen.
  eapply gf_mon. apply PR. intros.
  eapply gpaco14_mon. apply PR0. left; apply PR1. left; apply PR1.
Qed.

Lemma gpaco14_final clo r rg:
  (r \14/ paco14 gf rg) <14= gpaco14 clo r rg.
Proof.
  intros. destruct PR. apply gpaco14_base, H.
  econstructor. apply rclo14_base.
  left. eapply paco14_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo14_base. apply PR0.
  - intros. left. apply PR.
Qed.

Lemma gpaco14_unfold clo r rg:
  gpaco14 clo r rg <14= rclo14 clo (gf (gupaco14 clo (rg \14/ r)) \14/ r).
Proof.
  intros. destruct PR.
  eapply rclo14_mon. apply IN.
  intros. destruct PR; cycle 1. right; apply H.
  left. _punfold H; [|apply gpaco14_def_mon].
  eapply gf_mon. apply H.
  intros. econstructor.
  eapply rclo14_mon. apply PR.
  intros. destruct PR0; cycle 1. right. apply H0.
  left. eapply paco14_mon. apply H0.
  intros. left. apply PR0.
Qed.
  
Lemma gpaco14_cofix clo r rg 
      l (OBG: forall rr (INC: rg <14= rr) (CIH: l <14= rr), l <14= gpaco14 clo r rr):
  l <14= gpaco14 clo r rg.
Proof.
  assert (IN: l <14= gpaco14 clo r (rg \14/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo14_mon. apply IN0.
  clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply gpaco14_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo14_rclo. eapply rclo14_mon. apply PR.
  intros. destruct PR0.
  - apply rclo14_base. right. apply CIH. apply H.
  - destruct H; [destruct H|].
    + apply rclo14_base. right. apply CIH0. left. apply H.
    + apply IN in H. destruct H.
      eapply rclo14_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. right. apply H.
    + apply rclo14_base. right. apply CIH0. right. apply H.
Qed.

Lemma gpaco14_gupaco clo r rg:
  gupaco14 clo (gpaco14 clo r rg) <14= gpaco14 clo r rg.
Proof.
  eapply gpaco14_cofix.
  intros. destruct PR. econstructor.
  apply rclo14_rclo. eapply rclo14_mon. apply IN.
  intros. destruct PR.
  - apply rclo14_base. left.
    eapply paco14_mon. apply H.
    intros. left; apply CIH.
    econstructor. apply rclo14_base. right.
    destruct PR; apply H0.
  - destruct H. eapply rclo14_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco14_mon. apply H.
    intros. destruct PR.
    + left. apply INC. apply H0.
    + right. apply H0.
Qed.

Lemma gpaco14_uclo uclo clo r rg 
      (LEclo: uclo <15= gupaco14 clo) :
  uclo (gpaco14 clo r rg) <14= gpaco14 clo r rg.
Proof.
  intros. apply gpaco14_gupaco. apply LEclo, PR.
Qed.

Lemma gpaco14_weaken  clo r rg:
  gpaco14 (gupaco14 clo) r rg <14= gpaco14 clo r rg.
Proof.
  intros. apply gpaco14_unfold in PR.
  induction PR.
  - destruct IN; cycle 1. apply gpaco14_base, H.
    apply gpaco14_step_gen. eapply gf_mon. apply H.
    clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 H.
    eapply gpaco14_cofix. intros.
    apply gpaco14_unfold in PR.
    induction PR.
    + destruct IN; cycle 1. apply gpaco14_base, H.
      apply gpaco14_step. eapply gf_mon. apply H.
      intros. apply gpaco14_base. apply CIH.
      eapply gupaco14_mon. apply PR.
      intros. destruct PR0; apply H0.
    + apply gpaco14_gupaco.
      eapply gupaco14_mon. apply IN. apply H.
  - apply gpaco14_gupaco.
    eapply gupaco14_mon. apply IN. apply H.
Qed.

End Main.

Hint Resolve gpaco14_def_mon : paco.

Section GeneralMonotonicity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone14 gf.
  
Lemma gpaco14_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r r' rg rg'
      (IN: @gpaco14 gf clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (LEgf: gf <15= gf')
      (LEclo: clo <15= clo')
      (LEr: r <14= r')
      (LErg: rg <14= rg') :
  @gpaco14 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  eapply gpaco14_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo14_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco14_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply gf_mon. apply PR.
    intros. eapply rclo14_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma gpaco14_mon_bot (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r' rg'
      (IN: @gpaco14 gf clo bot14 bot14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (LEgf: gf <15= gf')
      (LEclo: clo <15= clo'):
  @gpaco14 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  eapply gpaco14_mon_gen. apply IN. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco14_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r r'
      (IN: @gupaco14 gf clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (LEgf: gf <15= gf')
      (LEclo: clo <15= clo')
      (LEr: r <14= r'):
  @gupaco14 gf' clo' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  eapply gpaco14_mon_gen. apply IN. apply LEgf. apply LEclo. apply LEr. apply LEr.
Qed.

End GeneralMonotonicity.

Section Compatibility.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone14 gf.

Structure compatible14 (clo: rel -> rel) : Prop :=
  compat14_intro {
      compat14_mon: monotone14 clo;
      compat14_compat : forall r,
          clo (gf r) <14= gf (clo r);
    }.

Structure wcompatible14 clo : Prop :=
  wcompat14_intro {
      wcompat14_mon: monotone14 clo;
      wcompat14_wcompat : forall r,
          clo (gf r) <14= gf (gupaco14 gf clo r);
    }.

Inductive cpn14 (r: rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Prop :=
| cpn14_intro
    clo
    (COM: compatible14 clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
.

Lemma rclo14_dist clo
      (MON: monotone14 clo)
      (DIST: forall r1 r2, clo (r1 \14/ r2) <14= (clo r1 \14/ clo r2)):
  forall r1 r2, rclo14 clo (r1 \14/ r2) <14= (rclo14 clo r1 \14/ rclo14 clo r2).
Proof.
  intros. induction PR.
  + destruct IN; [left|right]; apply rclo14_base, H.
  + assert (REL: clo (rclo14 clo r1 \14/ rclo14 clo r2) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13).
    { eapply MON. apply IN. apply H. }
    apply DIST in REL. destruct REL; [left|right]; apply rclo14_clo, H0.
Qed.

Lemma rclo14_compat clo
      (COM: compatible14 clo):
  compatible14 (rclo14 clo).
Proof.
  econstructor.
  - apply rclo14_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo14_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo14_clo. apply PR.
Qed.

Lemma compat14_wcompat clo
      (CMP: compatible14 clo):
  wcompatible14 clo.
Proof.
  econstructor. apply CMP.
  intros. apply CMP in PR.
  eapply gf_mon. apply PR.
  intros. apply gpaco14_clo, PR0. 
Qed.

Lemma wcompat14_compat clo
      (WCMP: wcompatible14 clo) :
  compatible14 (gupaco14 gf clo).
Proof.
  econstructor.
  { red; intros. eapply gpaco14_mon. apply IN. apply LE. apply LE. }

  intros. apply gpaco14_unfold in PR; [|apply gf_mon].
  induction PR.
  - destruct IN; cycle 1.
    + eapply gf_mon. apply H.
      intros. apply gpaco14_base, PR.
    + eapply gf_mon. apply H.
      intros. apply gpaco14_gupaco. apply gf_mon.
      eapply gupaco14_mon. apply PR.
      intros. apply gpaco14_step. apply gf_mon.
      eapply gf_mon. destruct PR0 as [X|X]; apply X.
      intros. apply gpaco14_base, PR1.
  - eapply gf_mon, gpaco14_gupaco, gf_mon.
    apply WCMP. eapply WCMP. apply IN.
    intros. apply H, PR.
Qed.

Lemma wcompat14_union clo1 clo2
      (WCMP1: wcompatible14 clo1)
      (WCMP2: wcompatible14 clo2):
  wcompatible14 (clo1 \15/ clo2).
Proof.
  econstructor.
  - apply monotone14_union. apply WCMP1. apply WCMP2.
  - intros. destruct PR.
    + apply WCMP1 in H. eapply gf_mon. apply H.
      intros. eapply gupaco14_mon_gen. apply gf_mon. apply PR. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco14_mon_gen. apply gf_mon. apply PR.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
Qed.

Lemma cpn14_mon: monotone14 cpn14.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat14_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn14_greatest: forall clo (COM: compatible14 clo), clo <15= cpn14.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn14_compat: compatible14 cpn14.
Proof.
  econstructor; [apply cpn14_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat14_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn14_wcompat: wcompatible14 cpn14.
Proof. apply compat14_wcompat, cpn14_compat. Qed.

Lemma cpn14_gupaco:
  gupaco14 gf cpn14 <15= cpn14.
Proof.
  intros. eapply cpn14_greatest, PR. apply wcompat14_compat. apply cpn14_wcompat.
Qed.

Lemma cpn14_uclo uclo
      (MON: monotone14 uclo)
      (WCOM: forall r, uclo (gf r) <14= gf (gupaco14 gf (uclo \15/ cpn14) r)):
  uclo <15= gupaco14 gf cpn14.
Proof.
  intros. apply gpaco14_clo.
  exists (gupaco14 gf (uclo \15/ cpn14)).
  - apply wcompat14_compat.
    econstructor.
    + apply monotone14_union. apply MON. apply cpn14_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat14_compat in H; [| apply cpn14_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco14_clo. right. apply PR0.
  - apply gpaco14_clo. left. apply PR.
Qed.

End Compatibility.

Section Soundness.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone14 gf.

Lemma gpaco14_compat_init clo
      (CMP: compatible14 gf clo):
  gpaco14 gf clo bot14 bot14 <14= paco14 gf bot14.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo14_rclo, PR]. 
  apply compat14_compat with (gf:=gf). apply rclo14_compat. apply gf_mon. apply CMP.
  eapply rclo14_mon. apply IN.
  intros. destruct PR; [|contradiction]. _punfold H; [..|apply gpaco14_def_mon, gf_mon].
  eapply gpaco14_def_mon. apply gf_mon. apply H.
  intros. destruct PR; [|destruct H0; contradiction]. left. apply H0.
Qed.

Lemma gpaco14_init clo
      (WCMP: wcompatible14 gf clo):
  gpaco14 gf clo bot14 bot14 <14= paco14 gf bot14.
Proof.
  intros. eapply gpaco14_compat_init.
  - apply wcompat14_compat, WCMP. apply gf_mon.
  - eapply gpaco14_mon_bot. apply gf_mon. apply PR. intros; apply PR0.
    intros. apply gpaco14_clo, PR0.
Qed.

Lemma gpaco14_unfold_bot clo
      (WCMP: wcompatible14 gf clo):
  gpaco14 gf clo bot14 bot14 <14= gf (gpaco14 gf clo bot14 bot14).
Proof.
  intros. apply gpaco14_init in PR; [|apply WCMP].
  _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. destruct PR0; [|contradiction]. apply gpaco14_final. apply gf_mon. right. apply H.
Qed.

Lemma gpaco14_dist clo r rg
      (CMP: compatible14 gf clo)
      (DIST: forall r1 r2, clo (r1 \14/ r2) <14= (clo r1 \14/ clo r2)):
  gpaco14 gf clo r rg <14= (paco14 gf (rclo14 clo (rg \14/ r)) \14/ rclo14 clo r).
Proof.
  intros. apply gpaco14_unfold in PR; [|apply gf_mon].
  apply rclo14_dist in PR; [|apply CMP|apply DIST].
  destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 H.
  pcofix CIH; intros.
  apply rclo14_compat in H0; [|apply gf_mon|apply CMP].
  pstep. eapply gf_mon. apply H0. intros.
  assert (REL: @rclo14 clo (rclo14 clo (gf (gupaco14 gf clo ((rg \14/ r) \14/ (rg \14/ r))) \14/ (rg \14/ r))) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13).
  { eapply rclo14_mon. apply PR. intros. apply gpaco14_unfold in PR0. apply PR0. apply gf_mon. }
  apply rclo14_rclo in REL.
  apply rclo14_dist in REL; [|apply CMP|apply DIST].
  destruct REL; cycle 1.
  - right. apply CIH0, H.
  - right. apply CIH.
    eapply rclo14_mon. apply H. intros.
    eapply gf_mon. apply PR0. intros.
    eapply gupaco14_mon. apply PR1. intros.
    destruct PR2; apply H1.
Qed.

End Soundness.

End GeneralizedPaco14.

Hint Resolve gpaco14_def_mon : paco.
Hint Unfold gupaco14 : paco.
Hint Resolve gpaco14_base : paco.
Hint Resolve gpaco14_step : paco.
Hint Resolve gpaco14_final : paco.
