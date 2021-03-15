Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco14 pacotac.
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

Lemma rclo14_clo_base clo r:
  clo r <14= rclo14 clo r.
Proof.
  intros. eapply rclo14_clo', PR.
  intros. apply rclo14_base, PR0.
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

Lemma gpaco14_gen_guard  clo r rg:
  gpaco14 clo r (rg \14/ r) <14= gpaco14 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  eapply rclo14_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco14_mon_gen; intros. apply H. apply PR.
  destruct PR. apply H0. right. apply H0.
Qed.

Lemma gpaco14_rclo clo r rg:
  rclo14 clo r <14= gpaco14 clo r rg.
Proof.
  intros. econstructor.
  eapply rclo14_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco14_clo clo r rg:
  clo r <14= gpaco14 clo r rg.
Proof.
  intros. apply gpaco14_rclo. eapply rclo14_clo_base, PR.
Qed.

Lemma gpaco14_gen_rclo clo r rg:
  gpaco14 (rclo14 clo) r rg <14= gpaco14 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  apply rclo14_compose.
  eapply rclo14_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco14_mon_gen; intros; [apply H| |apply PR].
  eapply gf_mon, rclo14_compose. apply PR.
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

Lemma gpaco14_gpaco clo r rg:
  gpaco14 clo (gpaco14 clo r rg) (gupaco14 clo (rg \14/ r)) <14= gpaco14 clo r rg.
Proof.
  intros. apply gpaco14_unfold in PR.
  econstructor. apply rclo14_rclo. eapply rclo14_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 PR. intros.
  destruct PR; [|destruct H; apply IN].
  apply rclo14_base. left. pstep.
  eapply gf_mon. apply H. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 H. intros.
  cut (@gupaco14 clo (rg \14/ r) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13).
  { intros. destruct H. eapply rclo14_mon. apply IN. intros.
    destruct PR0; [|right; apply H].
    left. eapply paco14_mon. apply H. intros. destruct PR0; apply H0.
  }
  apply gpaco14_gupaco. eapply gupaco14_mon. apply PR. intros.
  destruct PR0; [apply H|].
  eapply gpaco14_mon; [apply H|right|left]; intros; apply PR0.
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
  
Lemma gpaco14_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r r' rg rg'
      (IN: @gpaco14 gf clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (gf_mon: monotone14 gf)
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
      (gf_mon: monotone14 gf)
      (LEgf: gf <15= gf')
      (LEclo: clo <15= clo'):
  @gpaco14 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  eapply gpaco14_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco14_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r r'
      (IN: @gupaco14 gf clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (gf_mon: monotone14 gf)
      (LEgf: gf <15= gf')
      (LEclo: clo <15= clo')
      (LEr: r <14= r'):
  @gupaco14 gf' clo' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  eapply gpaco14_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. apply LEr. apply LEr.
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

Lemma rclo14_wcompat clo
      (COM: wcompatible14 clo):
  wcompatible14 (rclo14 clo).
Proof.
  econstructor.
  - apply rclo14_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. apply gpaco14_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply gpaco14_gupaco. apply gf_mon.
        eapply gupaco14_mon_gen; intros; [apply PR|apply gf_mon|apply PR0| |apply PR0].
        apply rclo14_clo_base, PR0.
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
      intros. eapply gupaco14_mon_gen. apply PR. apply gf_mon. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco14_mon_gen. apply PR. apply gf_mon.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
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
  - eapply gpaco14_mon_bot. apply PR. apply gf_mon. intros; apply PR0.
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

End Soundness.

Section Distributivity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone14 gf.

Lemma gpaco14_dist clo r rg
      (CMP: wcompatible14 gf clo)
      (DIST: forall r1 r2, clo (r1 \14/ r2) <14= (clo r1 \14/ clo r2)):
  gpaco14 gf clo r rg <14= (paco14 gf (rclo14 clo (rg \14/ r)) \14/ rclo14 clo r).
Proof.
  intros. apply gpaco14_unfold in PR; [|apply gf_mon].
  apply rclo14_dist in PR; [|apply CMP|apply DIST].
  destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 H.
  pcofix CIH; intros.
  apply rclo14_wcompat in H0; [|apply gf_mon|apply CMP].
  pstep. eapply gf_mon. apply H0. intros.
  apply gpaco14_unfold in PR; [|apply gf_mon].
  apply rclo14_compose in PR.
  apply rclo14_dist in PR; [|apply CMP|apply DIST].
  destruct PR.
  - right. apply CIH.
    eapply rclo14_mon. apply H. intros.
    eapply gf_mon. apply PR. intros.
    apply gpaco14_gupaco. apply gf_mon.
    apply gpaco14_gen_rclo. apply gf_mon.
    eapply gupaco14_mon. apply PR0. intros.
    destruct PR1; apply H1.
  - assert (REL: @rclo14 clo (rclo14 clo (gf (gupaco14 gf clo ((rg \14/ r) \14/ (rg \14/ r))) \14/ (rg \14/ r))) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13).
    { eapply rclo14_mon. apply H. intros. apply gpaco14_unfold in PR. apply PR. apply gf_mon. }
    apply rclo14_rclo in REL.
    apply rclo14_dist in REL; [|apply CMP|apply DIST].
    right. destruct REL; cycle 1.
    + apply CIH0, H1.
    + apply CIH.
      eapply rclo14_mon. apply H1. intros.
      eapply gf_mon. apply PR. intros.
      eapply gupaco14_mon. apply PR0. intros.
      destruct PR1; apply H2.
Qed.

Lemma gpaco14_dist_reverse clo r rg:
  (paco14 gf (rclo14 clo (rg \14/ r)) \14/ rclo14 clo r) <14= gpaco14 gf clo r rg.
Proof.
  intros. destruct PR; cycle 1.
  - eapply gpaco14_rclo. apply H.
  - econstructor. apply rclo14_base. left.
    revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 H. pcofix CIH; intros.
    _punfold H0; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H0. intros.
    destruct PR.
    + apply rclo14_base. right. apply CIH, H.
    + eapply rclo14_mon. apply H. intros.
      right. apply CIH0. apply PR.
Qed.

End Distributivity.

Section Companion.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone14 gf.

Inductive cpn14 (r: rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Prop :=
| cpn14_intro
    clo
    (COM: compatible14 gf clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
.

Lemma cpn14_mon: monotone14 cpn14.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat14_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn14_greatest: forall clo (COM: compatible14 gf clo), clo <15= cpn14.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn14_compat: compatible14 gf cpn14.
Proof.
  econstructor; [apply cpn14_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat14_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn14_wcompat: wcompatible14 gf cpn14.
Proof. apply compat14_wcompat, cpn14_compat. apply gf_mon. Qed.

Lemma cpn14_gupaco:
  gupaco14 gf cpn14 <15= cpn14.
Proof.
  intros. eapply cpn14_greatest, PR. apply wcompat14_compat. apply gf_mon. apply cpn14_wcompat.
Qed.

Lemma cpn14_cpn r:
  cpn14 (cpn14 r) <14= cpn14 r.
Proof.
  intros. apply cpn14_gupaco, gpaco14_gupaco, gpaco14_clo. apply gf_mon.
  eapply cpn14_mon, gpaco14_clo. apply PR.
Qed.

Lemma cpn14_base r:
  r <14= cpn14 r.
Proof.
  intros. apply cpn14_gupaco. apply gpaco14_base, PR.
Qed.

Lemma cpn14_clo
      r clo (LE: clo <15= cpn14):
  clo (cpn14 r) <14= cpn14 r.
Proof.
  intros. apply cpn14_cpn, LE, PR.
Qed.

Lemma cpn14_step r:
  gf (cpn14 r) <14= cpn14 r.
Proof.
  intros. apply cpn14_gupaco. apply gpaco14_step. apply gf_mon.
  eapply gf_mon, gpaco14_clo. apply PR.
Qed.

Lemma cpn14_uclo uclo
      (MON: monotone14 uclo)
      (WCOM: forall r, uclo (gf r) <14= gf (gupaco14 gf (uclo \15/ cpn14) r)):
  uclo <15= gupaco14 gf cpn14.
Proof.
  intros. apply gpaco14_clo.
  exists (gupaco14 gf (uclo \15/ cpn14)).
  - apply wcompat14_compat. apply gf_mon.
    econstructor.
    + apply monotone14_union. apply MON. apply cpn14_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat14_compat with (gf:=gf) in H; [| apply cpn14_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco14_clo. right. apply PR0.
  - apply gpaco14_clo. left. apply PR.
Qed.

End Companion.

Section Respectful.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone14 gf.

Structure wrespectful14 (clo: rel -> rel) : Prop :=
  wrespect14_intro {
      wrespect14_mon: monotone14 clo;
      wrespect14_respect :
        forall l r
               (LE: l <14= r)
               (GF: l <14= gf r),
        clo l <14= gf (rclo14 clo r);
    }.

Structure prespectful14 (clo: rel -> rel) : Prop :=
  prespect14_intro {
      prespect14_mon: monotone14 clo;
      prespect14_respect :
        forall l r
               (LE: l <14= r)
               (GF: l <14= gf r),
        clo l <14= paco14 gf (r \14/ clo r);
    }.

Structure grespectful14 (clo: rel -> rel) : Prop :=
  grespect14_intro {
      grespect14_mon: monotone14 clo;
      grespect14_respect :
        forall l r
               (LE: l <14= r)
               (GF: l <14= gf r),
        clo l <14= rclo14 (cpn14 gf) (gf (rclo14 (clo \15/ gupaco14 gf (cpn14 gf)) r));
    }.

Definition gf'14 := id /15\ gf.

Definition compatible'14 := compatible14 gf'14.

Lemma wrespect14_compatible'
      clo (RES: wrespectful14 clo):
  compatible'14 (rclo14 clo).
Proof.
  intros. econstructor. apply rclo14_mon.
  intros. destruct RES. split.
  { eapply rclo14_mon. apply PR. intros. apply PR0. }
  induction PR; intros.
  - eapply gf_mon. apply IN.
    intros. apply rclo14_base, PR.
  - eapply gf_mon.
    + eapply wrespect14_respect0; [|apply H|apply IN].
      intros. eapply rclo14_mon; intros; [apply LE, PR|apply PR0].
    + intros. apply rclo14_rclo, PR.
Qed.

Lemma prespect14_compatible'
      clo (RES: prespectful14 clo):
  compatible'14 (fun r => upaco14 gf (r \14/ clo r)).
Proof.
  econstructor.
  { red; intros. eapply upaco14_mon. apply IN.
    intros. destruct PR.
    - left. apply LE, H.
    - right. eapply RES. apply H. intros. apply LE, PR. }

  intros r.
  assert (LEM: (gf'14 r \14/ clo (gf'14 r)) <14= (r \14/ clo r)).
  { intros. destruct PR.
    - left. apply H.
    - right. eapply RES. apply H. intros. apply PR.
  }

  intros. destruct PR.
  - split.
    + left. eapply paco14_mon. apply H. apply LEM.
    + apply paco14_unfold; [apply gf_mon|].
      eapply paco14_mon. apply H. apply LEM.
  - split.
    + right. apply LEM. apply H.
    + destruct H.
      * eapply gf_mon. apply H. intros. right. left. apply PR.
      * apply paco14_unfold; [apply gf_mon|].
        eapply RES, H; intros; apply PR.
Qed.

Lemma grespect14_compatible'
      clo (RES: grespectful14 clo):
  compatible'14 (rclo14 (clo \15/ cpn14 gf)).
Proof.
  apply wrespect14_compatible'.
  econstructor.
  { red; intros. destruct IN.
    - left. eapply RES; [apply H|]. apply LE.
    - right. eapply cpn14_mon; [apply H|]. apply LE. }
  intros. destruct PR.
  - eapply RES.(grespect14_respect) in H; [|apply LE|apply GF].
    apply (@compat14_compat gf (rclo14 (cpn14 gf))) in H.
    2: { apply rclo14_compat; [apply gf_mon|]. apply cpn14_compat. apply gf_mon. }
    eapply gf_mon; [apply H|].
    intros. apply rclo14_clo. right.
    exists (rclo14 (cpn14 gf)).
    { apply rclo14_compat; [apply gf_mon|]. apply cpn14_compat. apply gf_mon. }
    eapply rclo14_mon; [eapply PR|].
    intros. eapply rclo14_mon_gen; [eapply PR0|..].
    + intros. destruct PR1.
      * left. apply H0.
      * right. apply cpn14_gupaco; [apply gf_mon|apply H0].
    + intros. apply PR1.
  - eapply gf_mon.
    + apply (@compat14_compat gf (rclo14 (cpn14 gf))).
      { apply rclo14_compat; [apply gf_mon|]. apply cpn14_compat. apply gf_mon. }
      eapply rclo14_clo_base. eapply cpn14_mon; [apply H|apply GF].
    + intros. eapply rclo14_mon_gen; [eapply PR|..].
      * intros. right. apply PR0.
      * intros. apply PR0.
Qed.

Lemma compat14_compatible'
      clo (COM: compatible14 gf clo):
  compatible'14 clo.
Proof.
  destruct COM. econstructor; [apply compat14_mon0|].
  intros. split.
  - eapply compat14_mon0; intros; [apply PR| apply PR0].
  - apply compat14_compat0.
    eapply compat14_mon0; intros; [apply PR| apply PR0].
Qed.

Lemma compatible'14_companion
      clo (RES: compatible'14 clo):
  clo <15= cpn14 gf.
Proof.
  assert (MON: monotone14 gf'14).
  { econstructor. apply LE, IN.
    eapply gf_mon, LE. apply IN.
  }
  assert (CPN: clo <15= cpn14 gf'14).
  { intros. econstructor. apply RES. apply PR.
  }
  intros. apply CPN in PR.
  econstructor; [|apply PR].
  econstructor; [apply cpn14_mon|]; intros.
  assert (PR1: cpn14 gf'14 (gf r) <14= cpn14 gf'14 (gf'14 (cpn14 gf r))).
  { intros. eapply cpn14_mon. apply PR1.
    intros. assert (TMP: gf (cpn14 gf r) <14= (cpn14 gf r /14\ gf (cpn14 gf r))).
    { split; [apply cpn14_step; [apply gf_mon|]|]; assumption. }
    apply TMP.
    eapply gf_mon. apply PR2. intros. apply cpn14_base; assumption.
  }
  apply PR1 in PR0. clear PR1. 
  eapply compat14_compat with (gf:=gf'14) in PR0; [|apply cpn14_compat, MON].
  eapply gf_mon; [apply PR0|].
  intros. eapply cpn14_cpn; [apply MON|].
  eapply cpn14_mon; [apply PR1|].
  intros. econstructor; [|apply PR2].
  apply compat14_compatible', cpn14_compat, gf_mon.
Qed.

Lemma wrespect14_companion
      clo (RES: wrespectful14 clo):
  clo <15= cpn14 gf.
Proof.
  intros. eapply wrespect14_compatible' in RES.
  eapply (@compatible'14_companion (rclo14 clo)) in RES; [apply RES|].
  eapply rclo14_clo_base, PR.
Qed.

Lemma prespect14_companion
      clo (RES: prespectful14 clo):
  clo <15= cpn14 gf.
Proof.
  intros. eapply compatible'14_companion. apply prespect14_compatible'. apply RES.
  right. right. apply PR.
Qed.

Lemma grespect14_companion
      clo (RES: grespectful14 clo):
  clo <15= cpn14 gf.
Proof.
  intros. eapply grespect14_compatible' in RES.
  eapply (@compatible'14_companion (rclo14 (clo \15/ cpn14 gf))); [apply RES|].
  apply rclo14_clo_base. left. apply PR.
Qed.

Lemma wrespect14_uclo
      clo (RES: wrespectful14 clo):
  clo <15= gupaco14 gf (cpn14 gf).
Proof.
  intros. eapply gpaco14_clo, wrespect14_companion, PR. apply RES.
Qed.

Lemma prespect14_uclo
      clo (RES: prespectful14 clo):
  clo <15= gupaco14 gf (cpn14 gf).
Proof.
  intros. eapply gpaco14_clo, prespect14_companion, PR. apply RES.
Qed.

Lemma grespect14_uclo
      clo (RES: grespectful14 clo):
  clo <15= gupaco14 gf (cpn14 gf).
Proof.
  intros. eapply gpaco14_clo, grespect14_companion, PR. apply RES.
Qed.

End Respectful.

End GeneralizedPaco14.

Hint Resolve gpaco14_def_mon : paco.
Hint Unfold gupaco14 : paco.
Hint Resolve gpaco14_base : paco.
Hint Resolve gpaco14_step : paco.
Hint Resolve gpaco14_final : paco.
Hint Resolve rclo14_base : paco.
Hint Constructors gpaco14 : paco.
Hint Resolve wrespect14_uclo : paco.
Hint Resolve prespect14_uclo : paco.
