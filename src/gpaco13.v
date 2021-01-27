Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco13 pacotac.
Set Implicit Arguments.

Section GeneralizedPaco13.

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

Local Notation rel := (rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12).

Section RClo.

Inductive rclo13 (clo: rel->rel) (r: rel): rel :=
| rclo13_base
    x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
    (IN: r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12):
    @rclo13 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
| rclo13_clo'
    r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
    (LE: r' <13= rclo13 clo r)
    (IN: clo r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12):
    @rclo13 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
.           

Lemma rclo13_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
      (IN: @rclo13 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (LEclo: clo <14= clo')
      (LEr: r <13= r') :
  @rclo13 clo' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo13_mon clo:
  monotone13 (rclo13 clo).
Proof.
  repeat intro. eapply rclo13_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo13_clo clo r:
  clo (rclo13 clo r) <13= rclo13 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo13_clo_base clo r:
  clo r <13= rclo13 clo r.
Proof.
  intros. eapply rclo13_clo', PR.
  intros. apply rclo13_base, PR0.
Qed.

Lemma rclo13_rclo clo r:
  rclo13 clo (rclo13 clo r) <13= rclo13 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo13_compose clo r:
  rclo13 (rclo13 clo) r <13= rclo13 clo r.
Proof.
  intros. induction PR.
  - apply rclo13_base, IN.
  - apply rclo13_rclo.
    eapply rclo13_mon; [apply IN|apply H].
Qed.

End RClo.  

Section Main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone13 gf.

Variant gpaco13 clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Prop :=
| gpaco13_intro (IN: @rclo13 clo (paco13 (compose gf (rclo13 clo)) (rg \13/ r) \13/ r) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
.

Definition gupaco13 clo r := gpaco13 clo r r.

Lemma gpaco13_def_mon clo : monotone13 (compose gf (rclo13 clo)).
Proof.
  eapply monotone13_compose. apply gf_mon. apply rclo13_mon.
Qed.

Hint Resolve gpaco13_def_mon : paco.

Lemma gpaco13_mon clo r r' rg rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
      (IN: @gpaco13 clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (LEr: r <13= r')
      (LErg: rg <13= rg'):
  @gpaco13 clo r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  destruct IN. econstructor.
  eapply rclo13_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco13_mon. apply H.
  intros. destruct PR.
  - left. apply LErg, H0.
  - right. apply LEr, H0.
Qed.

Lemma gupaco13_mon clo r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
      (IN: @gupaco13 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (LEr: r <13= r'):
  @gupaco13 clo r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  eapply gpaco13_mon. apply IN. apply LEr. apply LEr.
Qed.

Lemma gpaco13_base clo r rg: r <13= gpaco13 clo r rg.
Proof.
  econstructor. apply rclo13_base. right. apply PR.
Qed.

Lemma gpaco13_gen_guard  clo r rg:
  gpaco13 clo r (rg \13/ r) <13= gpaco13 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  eapply rclo13_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco13_mon_gen; intros. apply H. apply PR.
  destruct PR. apply H0. right. apply H0.
Qed.

Lemma gpaco13_rclo clo r rg:
  rclo13 clo r <13= gpaco13 clo r rg.
Proof.
  intros. econstructor.
  eapply rclo13_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco13_clo clo r rg:
  clo r <13= gpaco13 clo r rg.
Proof.
  intros. apply gpaco13_rclo. eapply rclo13_clo_base, PR.
Qed.

Lemma gpaco13_gen_rclo clo r rg:
  gpaco13 (rclo13 clo) r rg <13= gpaco13 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  apply rclo13_compose.
  eapply rclo13_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco13_mon_gen; intros; [apply H| |apply PR].
  eapply gf_mon, rclo13_compose. apply PR.
Qed.

Lemma gpaco13_step_gen clo r rg:
  gf (gpaco13 clo (rg \13/ r) (rg \13/ r)) <13= gpaco13 clo r rg.
Proof.
  intros. econstructor. apply rclo13_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo13_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco13_mon. apply H. intros. destruct PR0; apply H0.
  - right. apply H.
Qed.

Lemma gpaco13_step clo r rg:
  gf (gpaco13 clo rg rg) <13= gpaco13 clo r rg.
Proof.
  intros. apply gpaco13_step_gen.
  eapply gf_mon. apply PR. intros.
  eapply gpaco13_mon. apply PR0. left; apply PR1. left; apply PR1.
Qed.

Lemma gpaco13_final clo r rg:
  (r \13/ paco13 gf rg) <13= gpaco13 clo r rg.
Proof.
  intros. destruct PR. apply gpaco13_base, H.
  econstructor. apply rclo13_base.
  left. eapply paco13_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo13_base. apply PR0.
  - intros. left. apply PR.
Qed.

Lemma gpaco13_unfold clo r rg:
  gpaco13 clo r rg <13= rclo13 clo (gf (gupaco13 clo (rg \13/ r)) \13/ r).
Proof.
  intros. destruct PR.
  eapply rclo13_mon. apply IN.
  intros. destruct PR; cycle 1. right; apply H.
  left. _punfold H; [|apply gpaco13_def_mon].
  eapply gf_mon. apply H.
  intros. econstructor.
  eapply rclo13_mon. apply PR.
  intros. destruct PR0; cycle 1. right. apply H0.
  left. eapply paco13_mon. apply H0.
  intros. left. apply PR0.
Qed.
  
Lemma gpaco13_cofix clo r rg 
      l (OBG: forall rr (INC: rg <13= rr) (CIH: l <13= rr), l <13= gpaco13 clo r rr):
  l <13= gpaco13 clo r rg.
Proof.
  assert (IN: l <13= gpaco13 clo r (rg \13/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo13_mon. apply IN0.
  clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply gpaco13_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo13_rclo. eapply rclo13_mon. apply PR.
  intros. destruct PR0.
  - apply rclo13_base. right. apply CIH. apply H.
  - destruct H; [destruct H|].
    + apply rclo13_base. right. apply CIH0. left. apply H.
    + apply IN in H. destruct H.
      eapply rclo13_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. right. apply H.
    + apply rclo13_base. right. apply CIH0. right. apply H.
Qed.

Lemma gpaco13_gupaco clo r rg:
  gupaco13 clo (gpaco13 clo r rg) <13= gpaco13 clo r rg.
Proof.
  eapply gpaco13_cofix.
  intros. destruct PR. econstructor.
  apply rclo13_rclo. eapply rclo13_mon. apply IN.
  intros. destruct PR.
  - apply rclo13_base. left.
    eapply paco13_mon. apply H.
    intros. left; apply CIH.
    econstructor. apply rclo13_base. right.
    destruct PR; apply H0.
  - destruct H. eapply rclo13_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco13_mon. apply H.
    intros. destruct PR.
    + left. apply INC. apply H0.
    + right. apply H0.
Qed.

Lemma gpaco13_gpaco clo r rg:
  gpaco13 clo (gpaco13 clo r rg) (gupaco13 clo (rg \13/ r)) <13= gpaco13 clo r rg.
Proof.
  intros. apply gpaco13_unfold in PR.
  econstructor. apply rclo13_rclo. eapply rclo13_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 PR. intros.
  destruct PR; [|destruct H; apply IN].
  apply rclo13_base. left. pstep.
  eapply gf_mon. apply H. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 H. intros.
  cut (@gupaco13 clo (rg \13/ r) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12).
  { intros. destruct H. eapply rclo13_mon. apply IN. intros.
    destruct PR0; [|right; apply H].
    left. eapply paco13_mon. apply H. intros. destruct PR0; apply H0.
  }
  apply gpaco13_gupaco. eapply gupaco13_mon. apply PR. intros.
  destruct PR0; [apply H|].
  eapply gpaco13_mon; [apply H|right|left]; intros; apply PR0.
Qed.

Lemma gpaco13_uclo uclo clo r rg 
      (LEclo: uclo <14= gupaco13 clo) :
  uclo (gpaco13 clo r rg) <13= gpaco13 clo r rg.
Proof.
  intros. apply gpaco13_gupaco. apply LEclo, PR.
Qed.

Lemma gpaco13_weaken  clo r rg:
  gpaco13 (gupaco13 clo) r rg <13= gpaco13 clo r rg.
Proof.
  intros. apply gpaco13_unfold in PR.
  induction PR.
  - destruct IN; cycle 1. apply gpaco13_base, H.
    apply gpaco13_step_gen. eapply gf_mon. apply H.
    clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 H.
    eapply gpaco13_cofix. intros.
    apply gpaco13_unfold in PR.
    induction PR.
    + destruct IN; cycle 1. apply gpaco13_base, H.
      apply gpaco13_step. eapply gf_mon. apply H.
      intros. apply gpaco13_base. apply CIH.
      eapply gupaco13_mon. apply PR.
      intros. destruct PR0; apply H0.
    + apply gpaco13_gupaco.
      eapply gupaco13_mon. apply IN. apply H.
  - apply gpaco13_gupaco.
    eapply gupaco13_mon. apply IN. apply H.
Qed.

End Main.

Hint Resolve gpaco13_def_mon : paco.

Section GeneralMonotonicity.

Variable gf: rel -> rel.
  
Lemma gpaco13_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r r' rg rg'
      (IN: @gpaco13 gf clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (gf_mon: monotone13 gf)
      (LEgf: gf <14= gf')
      (LEclo: clo <14= clo')
      (LEr: r <13= r')
      (LErg: rg <13= rg') :
  @gpaco13 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  eapply gpaco13_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo13_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco13_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply gf_mon. apply PR.
    intros. eapply rclo13_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma gpaco13_mon_bot (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r' rg'
      (IN: @gpaco13 gf clo bot13 bot13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (gf_mon: monotone13 gf)
      (LEgf: gf <14= gf')
      (LEclo: clo <14= clo'):
  @gpaco13 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  eapply gpaco13_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco13_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r r'
      (IN: @gupaco13 gf clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (gf_mon: monotone13 gf)
      (LEgf: gf <14= gf')
      (LEclo: clo <14= clo')
      (LEr: r <13= r'):
  @gupaco13 gf' clo' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  eapply gpaco13_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. apply LEr. apply LEr.
Qed.

End GeneralMonotonicity.

Section Compatibility.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone13 gf.

Structure compatible13 (clo: rel -> rel) : Prop :=
  compat13_intro {
      compat13_mon: monotone13 clo;
      compat13_compat : forall r,
          clo (gf r) <13= gf (clo r);
    }.

Structure wcompatible13 clo : Prop :=
  wcompat13_intro {
      wcompat13_mon: monotone13 clo;
      wcompat13_wcompat : forall r,
          clo (gf r) <13= gf (gupaco13 gf clo r);
    }.

Lemma rclo13_dist clo
      (MON: monotone13 clo)
      (DIST: forall r1 r2, clo (r1 \13/ r2) <13= (clo r1 \13/ clo r2)):
  forall r1 r2, rclo13 clo (r1 \13/ r2) <13= (rclo13 clo r1 \13/ rclo13 clo r2).
Proof.
  intros. induction PR.
  + destruct IN; [left|right]; apply rclo13_base, H.
  + assert (REL: clo (rclo13 clo r1 \13/ rclo13 clo r2) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12).
    { eapply MON. apply IN. apply H. }
    apply DIST in REL. destruct REL; [left|right]; apply rclo13_clo, H0.
Qed.

Lemma rclo13_compat clo
      (COM: compatible13 clo):
  compatible13 (rclo13 clo).
Proof.
  econstructor.
  - apply rclo13_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo13_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo13_clo. apply PR.
Qed.

Lemma rclo13_wcompat clo
      (COM: wcompatible13 clo):
  wcompatible13 (rclo13 clo).
Proof.
  econstructor.
  - apply rclo13_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. apply gpaco13_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply gpaco13_gupaco. apply gf_mon.
        eapply gupaco13_mon_gen; intros; [apply PR|apply gf_mon|apply PR0| |apply PR0].
        apply rclo13_clo_base, PR0.
Qed.

Lemma compat13_wcompat clo
      (CMP: compatible13 clo):
  wcompatible13 clo.
Proof.
  econstructor. apply CMP.
  intros. apply CMP in PR.
  eapply gf_mon. apply PR.
  intros. apply gpaco13_clo, PR0. 
Qed.

Lemma wcompat13_compat clo
      (WCMP: wcompatible13 clo) :
  compatible13 (gupaco13 gf clo).
Proof.
  econstructor.
  { red; intros. eapply gpaco13_mon. apply IN. apply LE. apply LE. }

  intros. apply gpaco13_unfold in PR; [|apply gf_mon].
  induction PR.
  - destruct IN; cycle 1.
    + eapply gf_mon. apply H.
      intros. apply gpaco13_base, PR.
    + eapply gf_mon. apply H.
      intros. apply gpaco13_gupaco. apply gf_mon.
      eapply gupaco13_mon. apply PR.
      intros. apply gpaco13_step. apply gf_mon.
      eapply gf_mon. destruct PR0 as [X|X]; apply X.
      intros. apply gpaco13_base, PR1.
  - eapply gf_mon, gpaco13_gupaco, gf_mon.
    apply WCMP. eapply WCMP. apply IN.
    intros. apply H, PR.
Qed.

Lemma wcompat13_union clo1 clo2
      (WCMP1: wcompatible13 clo1)
      (WCMP2: wcompatible13 clo2):
  wcompatible13 (clo1 \14/ clo2).
Proof.
  econstructor.
  - apply monotone13_union. apply WCMP1. apply WCMP2.
  - intros. destruct PR.
    + apply WCMP1 in H. eapply gf_mon. apply H.
      intros. eapply gupaco13_mon_gen. apply PR. apply gf_mon. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco13_mon_gen. apply PR. apply gf_mon.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
Qed.

End Compatibility.

Section Soundness.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone13 gf.

Lemma gpaco13_compat_init clo
      (CMP: compatible13 gf clo):
  gpaco13 gf clo bot13 bot13 <13= paco13 gf bot13.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo13_rclo, PR]. 
  apply compat13_compat with (gf:=gf). apply rclo13_compat. apply gf_mon. apply CMP.
  eapply rclo13_mon. apply IN.
  intros. destruct PR; [|contradiction]. _punfold H; [..|apply gpaco13_def_mon, gf_mon].
  eapply gpaco13_def_mon. apply gf_mon. apply H.
  intros. destruct PR; [|destruct H0; contradiction]. left. apply H0.
Qed.

Lemma gpaco13_init clo
      (WCMP: wcompatible13 gf clo):
  gpaco13 gf clo bot13 bot13 <13= paco13 gf bot13.
Proof.
  intros. eapply gpaco13_compat_init.
  - apply wcompat13_compat, WCMP. apply gf_mon.
  - eapply gpaco13_mon_bot. apply PR. apply gf_mon. intros; apply PR0.
    intros. apply gpaco13_clo, PR0.
Qed.

Lemma gpaco13_unfold_bot clo
      (WCMP: wcompatible13 gf clo):
  gpaco13 gf clo bot13 bot13 <13= gf (gpaco13 gf clo bot13 bot13).
Proof.
  intros. apply gpaco13_init in PR; [|apply WCMP].
  _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. destruct PR0; [|contradiction]. apply gpaco13_final. apply gf_mon. right. apply H.
Qed.

End Soundness.

Section Distributivity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone13 gf.

Lemma gpaco13_dist clo r rg
      (CMP: wcompatible13 gf clo)
      (DIST: forall r1 r2, clo (r1 \13/ r2) <13= (clo r1 \13/ clo r2)):
  gpaco13 gf clo r rg <13= (paco13 gf (rclo13 clo (rg \13/ r)) \13/ rclo13 clo r).
Proof.
  intros. apply gpaco13_unfold in PR; [|apply gf_mon].
  apply rclo13_dist in PR; [|apply CMP|apply DIST].
  destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 H.
  pcofix CIH; intros.
  apply rclo13_wcompat in H0; [|apply gf_mon|apply CMP].
  pstep. eapply gf_mon. apply H0. intros.
  apply gpaco13_unfold in PR; [|apply gf_mon].
  apply rclo13_compose in PR.
  apply rclo13_dist in PR; [|apply CMP|apply DIST].
  destruct PR.
  - right. apply CIH.
    eapply rclo13_mon. apply H. intros.
    eapply gf_mon. apply PR. intros.
    apply gpaco13_gupaco. apply gf_mon.
    apply gpaco13_gen_rclo. apply gf_mon.
    eapply gupaco13_mon. apply PR0. intros.
    destruct PR1; apply H1.
  - assert (REL: @rclo13 clo (rclo13 clo (gf (gupaco13 gf clo ((rg \13/ r) \13/ (rg \13/ r))) \13/ (rg \13/ r))) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12).
    { eapply rclo13_mon. apply H. intros. apply gpaco13_unfold in PR. apply PR. apply gf_mon. }
    apply rclo13_rclo in REL.
    apply rclo13_dist in REL; [|apply CMP|apply DIST].
    right. destruct REL; cycle 1.
    + apply CIH0, H1.
    + apply CIH.
      eapply rclo13_mon. apply H1. intros.
      eapply gf_mon. apply PR. intros.
      eapply gupaco13_mon. apply PR0. intros.
      destruct PR1; apply H2.
Qed.

Lemma gpaco13_dist_reverse clo r rg:
  (paco13 gf (rclo13 clo (rg \13/ r)) \13/ rclo13 clo r) <13= gpaco13 gf clo r rg.
Proof.
  intros. destruct PR; cycle 1.
  - eapply gpaco13_rclo. apply H.
  - econstructor. apply rclo13_base. left.
    revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 H. pcofix CIH; intros.
    _punfold H0; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H0. intros.
    destruct PR.
    + apply rclo13_base. right. apply CIH, H.
    + eapply rclo13_mon. apply H. intros.
      right. apply CIH0. apply PR.
Qed.

End Distributivity.

Section Companion.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone13 gf.

Inductive cpn13 (r: rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Prop :=
| cpn13_intro
    clo
    (COM: compatible13 gf clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
.

Lemma cpn13_mon: monotone13 cpn13.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat13_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn13_greatest: forall clo (COM: compatible13 gf clo), clo <14= cpn13.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn13_compat: compatible13 gf cpn13.
Proof.
  econstructor; [apply cpn13_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat13_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn13_wcompat: wcompatible13 gf cpn13.
Proof. apply compat13_wcompat, cpn13_compat. apply gf_mon. Qed.

Lemma cpn13_gupaco:
  gupaco13 gf cpn13 <14= cpn13.
Proof.
  intros. eapply cpn13_greatest, PR. apply wcompat13_compat. apply gf_mon. apply cpn13_wcompat.
Qed.

Lemma cpn13_cpn r:
  cpn13 (cpn13 r) <13= cpn13 r.
Proof.
  intros. apply cpn13_gupaco, gpaco13_gupaco, gpaco13_clo. apply gf_mon.
  eapply cpn13_mon, gpaco13_clo. apply PR.
Qed.

Lemma cpn13_base r:
  r <13= cpn13 r.
Proof.
  intros. apply cpn13_gupaco. apply gpaco13_base, PR.
Qed.

Lemma cpn13_clo
      r clo (LE: clo <14= cpn13):
  clo (cpn13 r) <13= cpn13 r.
Proof.
  intros. apply cpn13_cpn, LE, PR.
Qed.

Lemma cpn13_step r:
  gf (cpn13 r) <13= cpn13 r.
Proof.
  intros. apply cpn13_gupaco. apply gpaco13_step. apply gf_mon.
  eapply gf_mon, gpaco13_clo. apply PR.
Qed.

Lemma cpn13_uclo uclo
      (MON: monotone13 uclo)
      (WCOM: forall r, uclo (gf r) <13= gf (gupaco13 gf (uclo \14/ cpn13) r)):
  uclo <14= gupaco13 gf cpn13.
Proof.
  intros. apply gpaco13_clo.
  exists (gupaco13 gf (uclo \14/ cpn13)).
  - apply wcompat13_compat. apply gf_mon.
    econstructor.
    + apply monotone13_union. apply MON. apply cpn13_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat13_compat with (gf:=gf) in H; [| apply cpn13_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco13_clo. right. apply PR0.
  - apply gpaco13_clo. left. apply PR.
Qed.

End Companion.

Section Respectful.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone13 gf.

Structure wrespectful13 (clo: rel -> rel) : Prop :=
  wrespect13_intro {
      wrespect13_mon: monotone13 clo;
      wrespect13_respect :
        forall l r
               (LE: l <13= r)
               (GF: l <13= gf r),
        clo l <13= gf (rclo13 clo r);
    }.

Structure prespectful13 (clo: rel -> rel) : Prop :=
  prespect13_intro {
      prespect13_mon: monotone13 clo;
      prespect13_respect :
        forall l r
               (LE: l <13= r)
               (GF: l <13= gf r),
        clo l <13= paco13 gf (r \13/ clo r);
    }.

Structure grespectful13 (clo: rel -> rel) : Prop :=
  grespect13_intro {
      grespect13_mon: monotone13 clo;
      grespect13_respect :
        forall l r
               (LE: l <13= r)
               (GF: l <13= gf r),
        clo l <13= rclo13 (cpn13 gf) (gf (rclo13 (clo \14/ gupaco13 gf (cpn13 gf)) r));
    }.

Definition gf'13 := id /14\ gf.

Definition compatible'13 := compatible13 gf'13.

Lemma wrespect13_compatible'
      clo (RES: wrespectful13 clo):
  compatible'13 (rclo13 clo).
Proof.
  intros. econstructor. apply rclo13_mon.
  intros. destruct RES. split.
  { eapply rclo13_mon. apply PR. intros. apply PR0. }
  induction PR; intros.
  - eapply gf_mon. apply IN.
    intros. apply rclo13_base, PR.
  - eapply gf_mon.
    + eapply wrespect13_respect0; [|apply H|apply IN].
      intros. eapply rclo13_mon; intros; [apply LE, PR|apply PR0].
    + intros. apply rclo13_rclo, PR.
Qed.

Lemma prespect13_compatible'
      clo (RES: prespectful13 clo):
  compatible'13 (fun r => upaco13 gf (r \13/ clo r)).
Proof.
  econstructor.
  { red; intros. eapply upaco13_mon. apply IN.
    intros. destruct PR.
    - left. apply LE, H.
    - right. eapply RES. apply H. intros. apply LE, PR. }

  intros r.
  assert (LEM: (gf'13 r \13/ clo (gf'13 r)) <13= (r \13/ clo r)).
  { intros. destruct PR.
    - left. apply H.
    - right. eapply RES. apply H. intros. apply PR.
  }

  intros. destruct PR.
  - split.
    + left. eapply paco13_mon. apply H. apply LEM.
    + apply paco13_unfold; [apply gf_mon|].
      eapply paco13_mon. apply H. apply LEM.
  - split.
    + right. apply LEM. apply H.
    + destruct H.
      * eapply gf_mon. apply H. intros. right. left. apply PR.
      * apply paco13_unfold; [apply gf_mon|].
        eapply RES, H; intros; apply PR.
Qed.

Lemma grespect13_compatible'
      clo (RES: grespectful13 clo):
  compatible'13 (rclo13 (clo \14/ cpn13 gf)).
Proof.
  apply wrespect13_compatible'.
  econstructor.
  { red; intros. destruct IN.
    - left. eapply RES; [apply H|]. apply LE.
    - right. eapply cpn13_mon; [apply H|]. apply LE. }
  intros. destruct PR.
  - eapply RES.(grespect13_respect) in H; [|apply LE|apply GF].
    apply (@compat13_compat gf (rclo13 (cpn13 gf))) in H.
    2: { apply rclo13_compat; [apply gf_mon|]. apply cpn13_compat. apply gf_mon. }
    eapply gf_mon; [apply H|].
    intros. apply rclo13_clo. right.
    exists (rclo13 (cpn13 gf)).
    { apply rclo13_compat; [apply gf_mon|]. apply cpn13_compat. apply gf_mon. }
    eapply rclo13_mon; [eapply PR|].
    intros. eapply rclo13_mon_gen; [eapply PR0|..].
    + intros. destruct PR1.
      * left. apply H0.
      * right. apply cpn13_gupaco; [apply gf_mon|apply H0].
    + intros. apply PR1.
  - eapply gf_mon.
    + apply (@compat13_compat gf (rclo13 (cpn13 gf))).
      { apply rclo13_compat; [apply gf_mon|]. apply cpn13_compat. apply gf_mon. }
      eapply rclo13_clo_base. eapply cpn13_mon; [apply H|apply GF].
    + intros. eapply rclo13_mon_gen; [eapply PR|..].
      * intros. right. apply PR0.
      * intros. apply PR0.
Qed.

Lemma compat13_compatible'
      clo (COM: compatible13 gf clo):
  compatible'13 clo.
Proof.
  destruct COM. econstructor; [apply compat13_mon0|].
  intros. split.
  - eapply compat13_mon0; intros; [apply PR| apply PR0].
  - apply compat13_compat0.
    eapply compat13_mon0; intros; [apply PR| apply PR0].
Qed.

Lemma compatible'13_companion
      clo (RES: compatible'13 clo):
  clo <14= cpn13 gf.
Proof.
  assert (MON: monotone13 gf'13).
  { econstructor. apply LE, IN.
    eapply gf_mon, LE. apply IN.
  }
  assert (CPN: clo <14= cpn13 gf'13).
  { intros. econstructor. apply RES. apply PR.
  }
  intros. apply CPN in PR.
  econstructor; [|apply PR].
  econstructor; [apply cpn13_mon|]; intros.
  assert (PR1: cpn13 gf'13 (gf r) <13= cpn13 gf'13 (gf'13 (cpn13 gf r))).
  { intros. eapply cpn13_mon. apply PR1.
    intros. assert (TMP: gf (cpn13 gf r) <13= (cpn13 gf r /13\ gf (cpn13 gf r))).
    { split; [apply cpn13_step; [apply gf_mon|]|]; assumption. }
    apply TMP.
    eapply gf_mon. apply PR2. intros. apply cpn13_base; assumption.
  }
  apply PR1 in PR0. clear PR1. 
  eapply compat13_compat with (gf:=gf'13) in PR0; [|apply cpn13_compat, MON].
  eapply gf_mon; [apply PR0|].
  intros. eapply cpn13_cpn; [apply MON|].
  eapply cpn13_mon; [apply PR1|].
  intros. econstructor; [|apply PR2].
  apply compat13_compatible', cpn13_compat, gf_mon.
Qed.

Lemma wrespect13_companion
      clo (RES: wrespectful13 clo):
  clo <14= cpn13 gf.
Proof.
  intros. eapply wrespect13_compatible' in RES.
  eapply (@compatible'13_companion (rclo13 clo)) in RES; [apply RES|].
  eapply rclo13_clo_base, PR.
Qed.

Lemma prespect13_companion
      clo (RES: prespectful13 clo):
  clo <14= cpn13 gf.
Proof.
  intros. eapply compatible'13_companion. apply prespect13_compatible'. apply RES.
  right. right. apply PR.
Qed.

Lemma grespect13_companion
      clo (RES: grespectful13 clo):
  clo <14= cpn13 gf.
Proof.
  intros. eapply grespect13_compatible' in RES.
  eapply (@compatible'13_companion (rclo13 (clo \14/ cpn13 gf))); [apply RES|].
  apply rclo13_clo_base. left. apply PR.
Qed.

Lemma wrespect13_uclo
      clo (RES: wrespectful13 clo):
  clo <14= gupaco13 gf (cpn13 gf).
Proof.
  intros. eapply gpaco13_clo, wrespect13_companion, PR. apply RES.
Qed.

Lemma prespect13_uclo
      clo (RES: prespectful13 clo):
  clo <14= gupaco13 gf (cpn13 gf).
Proof.
  intros. eapply gpaco13_clo, prespect13_companion, PR. apply RES.
Qed.

Lemma grespect13_uclo
      clo (RES: grespectful13 clo):
  clo <14= gupaco13 gf (cpn13 gf).
Proof.
  intros. eapply gpaco13_clo, grespect13_companion, PR. apply RES.
Qed.

End Respectful.

End GeneralizedPaco13.

Hint Resolve gpaco13_def_mon : paco.
Hint Unfold gupaco13 : paco.
Hint Resolve gpaco13_base : paco.
Hint Resolve gpaco13_step : paco.
Hint Resolve gpaco13_final : paco.
Hint Resolve rclo13_base : paco.
Hint Constructors gpaco13 : paco.
Hint Resolve wrespect13_uclo : paco.
Hint Resolve prespect13_uclo : paco.
