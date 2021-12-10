Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco12 pacotac.
Set Implicit Arguments.

Section GeneralizedPaco12.

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

Local Notation rel := (rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11).

Section RClo.

Inductive rclo12 (clo: rel->rel) (r: rel): rel :=
| rclo12_base
    x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    (IN: r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11):
    @rclo12 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
| rclo12_clo'
    r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    (LE: r' <12= rclo12 clo r)
    (IN: clo r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11):
    @rclo12 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
.           

Lemma rclo12_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
      (IN: @rclo12 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (LEclo: clo <13= clo')
      (LEr: r <12= r') :
  @rclo12 clo' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo12_mon clo:
  monotone12 (rclo12 clo).
Proof.
  repeat intro. eapply rclo12_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo12_clo clo r:
  clo (rclo12 clo r) <12= rclo12 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo12_clo_base clo r:
  clo r <12= rclo12 clo r.
Proof.
  intros. eapply rclo12_clo', PR.
  intros. apply rclo12_base, PR0.
Qed.

Lemma rclo12_rclo clo r:
  rclo12 clo (rclo12 clo r) <12= rclo12 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo12_compose clo r:
  rclo12 (rclo12 clo) r <12= rclo12 clo r.
Proof.
  intros. induction PR.
  - apply rclo12_base, IN.
  - apply rclo12_rclo.
    eapply rclo12_mon; [apply IN|apply H].
Qed.

End RClo.  

Section Main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone12 gf.

Variant gpaco12 clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Prop :=
| gpaco12_intro (IN: @rclo12 clo (paco12 (compose gf (rclo12 clo)) (rg \12/ r) \12/ r) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
.

Definition gupaco12 clo r := gpaco12 clo r r.

Lemma gpaco12_def_mon clo : monotone12 (compose gf (rclo12 clo)).
Proof.
  eapply monotone12_compose. apply gf_mon. apply rclo12_mon.
Qed.

#[local] Hint Resolve gpaco12_def_mon : paco.

Lemma gpaco12_mon clo r r' rg rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
      (IN: @gpaco12 clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (LEr: r <12= r')
      (LErg: rg <12= rg'):
  @gpaco12 clo r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  destruct IN. econstructor.
  eapply rclo12_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco12_mon. apply H.
  intros. destruct PR.
  - left. apply LErg, H0.
  - right. apply LEr, H0.
Qed.

Lemma gupaco12_mon clo r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
      (IN: @gupaco12 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (LEr: r <12= r'):
  @gupaco12 clo r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  eapply gpaco12_mon. apply IN. apply LEr. apply LEr.
Qed.

Lemma gpaco12_base clo r rg: r <12= gpaco12 clo r rg.
Proof.
  econstructor. apply rclo12_base. right. apply PR.
Qed.

Lemma gpaco12_gen_guard  clo r rg:
  gpaco12 clo r (rg \12/ r) <12= gpaco12 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  eapply rclo12_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco12_mon_gen; intros. apply H. apply PR.
  destruct PR. apply H0. right. apply H0.
Qed.

Lemma gpaco12_rclo clo r rg:
  rclo12 clo r <12= gpaco12 clo r rg.
Proof.
  intros. econstructor.
  eapply rclo12_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco12_clo clo r rg:
  clo r <12= gpaco12 clo r rg.
Proof.
  intros. apply gpaco12_rclo. eapply rclo12_clo_base, PR.
Qed.

Lemma gpaco12_gen_rclo clo r rg:
  gpaco12 (rclo12 clo) r rg <12= gpaco12 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  apply rclo12_compose.
  eapply rclo12_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco12_mon_gen; intros; [apply H| |apply PR].
  eapply gf_mon, rclo12_compose. apply PR.
Qed.

Lemma gpaco12_step_gen clo r rg:
  gf (gpaco12 clo (rg \12/ r) (rg \12/ r)) <12= gpaco12 clo r rg.
Proof.
  intros. econstructor. apply rclo12_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo12_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco12_mon. apply H. intros. destruct PR0; apply H0.
  - right. apply H.
Qed.

Lemma gpaco12_step clo r rg:
  gf (gpaco12 clo rg rg) <12= gpaco12 clo r rg.
Proof.
  intros. apply gpaco12_step_gen.
  eapply gf_mon. apply PR. intros.
  eapply gpaco12_mon. apply PR0. left; apply PR1. left; apply PR1.
Qed.

Lemma gpaco12_final clo r rg:
  (r \12/ paco12 gf rg) <12= gpaco12 clo r rg.
Proof.
  intros. destruct PR. apply gpaco12_base, H.
  econstructor. apply rclo12_base.
  left. eapply paco12_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo12_base. apply PR0.
  - intros. left. apply PR.
Qed.

Lemma gpaco12_unfold clo r rg:
  gpaco12 clo r rg <12= rclo12 clo (gf (gupaco12 clo (rg \12/ r)) \12/ r).
Proof.
  intros. destruct PR.
  eapply rclo12_mon. apply IN.
  intros. destruct PR; cycle 1. right; apply H.
  left. _punfold H; [|apply gpaco12_def_mon].
  eapply gf_mon. apply H.
  intros. econstructor.
  eapply rclo12_mon. apply PR.
  intros. destruct PR0; cycle 1. right. apply H0.
  left. eapply paco12_mon. apply H0.
  intros. left. apply PR0.
Qed.
  
Lemma gpaco12_cofix clo r rg 
      l (OBG: forall rr (INC: rg <12= rr) (CIH: l <12= rr), l <12= gpaco12 clo r rr):
  l <12= gpaco12 clo r rg.
Proof.
  assert (IN: l <12= gpaco12 clo r (rg \12/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo12_mon. apply IN0.
  clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply gpaco12_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo12_rclo. eapply rclo12_mon. apply PR.
  intros. destruct PR0.
  - apply rclo12_base. right. apply CIH. apply H.
  - destruct H; [destruct H|].
    + apply rclo12_base. right. apply CIH0. left. apply H.
    + apply IN in H. destruct H.
      eapply rclo12_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. right. apply H.
    + apply rclo12_base. right. apply CIH0. right. apply H.
Qed.

Lemma gpaco12_gupaco clo r rg:
  gupaco12 clo (gpaco12 clo r rg) <12= gpaco12 clo r rg.
Proof.
  eapply gpaco12_cofix.
  intros. destruct PR. econstructor.
  apply rclo12_rclo. eapply rclo12_mon. apply IN.
  intros. destruct PR.
  - apply rclo12_base. left.
    eapply paco12_mon. apply H.
    intros. left; apply CIH.
    econstructor. apply rclo12_base. right.
    destruct PR; apply H0.
  - destruct H. eapply rclo12_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco12_mon. apply H.
    intros. destruct PR.
    + left. apply INC. apply H0.
    + right. apply H0.
Qed.

Lemma gpaco12_gpaco clo r rg:
  gpaco12 clo (gpaco12 clo r rg) (gupaco12 clo (rg \12/ r)) <12= gpaco12 clo r rg.
Proof.
  intros. apply gpaco12_unfold in PR.
  econstructor. apply rclo12_rclo. eapply rclo12_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 PR. intros.
  destruct PR; [|destruct H; apply IN].
  apply rclo12_base. left. pstep.
  eapply gf_mon. apply H. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 H. intros.
  cut (@gupaco12 clo (rg \12/ r) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11).
  { intros. destruct H. eapply rclo12_mon. apply IN. intros.
    destruct PR0; [|right; apply H].
    left. eapply paco12_mon. apply H. intros. destruct PR0; apply H0.
  }
  apply gpaco12_gupaco. eapply gupaco12_mon. apply PR. intros.
  destruct PR0; [apply H|].
  eapply gpaco12_mon; [apply H|right|left]; intros; apply PR0.
Qed.

Lemma gpaco12_uclo uclo clo r rg 
      (LEclo: uclo <13= gupaco12 clo) :
  uclo (gpaco12 clo r rg) <12= gpaco12 clo r rg.
Proof.
  intros. apply gpaco12_gupaco. apply LEclo, PR.
Qed.

Lemma gpaco12_weaken  clo r rg:
  gpaco12 (gupaco12 clo) r rg <12= gpaco12 clo r rg.
Proof.
  intros. apply gpaco12_unfold in PR.
  induction PR.
  - destruct IN; cycle 1. apply gpaco12_base, H.
    apply gpaco12_step_gen. eapply gf_mon. apply H.
    clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 H.
    eapply gpaco12_cofix. intros.
    apply gpaco12_unfold in PR.
    induction PR.
    + destruct IN; cycle 1. apply gpaco12_base, H.
      apply gpaco12_step. eapply gf_mon. apply H.
      intros. apply gpaco12_base. apply CIH.
      eapply gupaco12_mon. apply PR.
      intros. destruct PR0; apply H0.
    + apply gpaco12_gupaco.
      eapply gupaco12_mon. apply IN. apply H.
  - apply gpaco12_gupaco.
    eapply gupaco12_mon. apply IN. apply H.
Qed.

End Main.

#[local] Hint Resolve gpaco12_def_mon : paco.

Section GeneralMonotonicity.

Variable gf: rel -> rel.
  
Lemma gpaco12_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r r' rg rg'
      (IN: @gpaco12 gf clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (gf_mon: monotone12 gf)
      (LEgf: gf <13= gf')
      (LEclo: clo <13= clo')
      (LEr: r <12= r')
      (LErg: rg <12= rg') :
  @gpaco12 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  eapply gpaco12_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo12_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco12_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply gf_mon. apply PR.
    intros. eapply rclo12_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma gpaco12_mon_bot (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r' rg'
      (IN: @gpaco12 gf clo bot12 bot12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (gf_mon: monotone12 gf)
      (LEgf: gf <13= gf')
      (LEclo: clo <13= clo'):
  @gpaco12 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  eapply gpaco12_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco12_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r r'
      (IN: @gupaco12 gf clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (gf_mon: monotone12 gf)
      (LEgf: gf <13= gf')
      (LEclo: clo <13= clo')
      (LEr: r <12= r'):
  @gupaco12 gf' clo' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  eapply gpaco12_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. apply LEr. apply LEr.
Qed.

End GeneralMonotonicity.

Section Compatibility.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone12 gf.

Structure compatible12 (clo: rel -> rel) : Prop :=
  compat12_intro {
      compat12_mon: monotone12 clo;
      compat12_compat : forall r,
          clo (gf r) <12= gf (clo r);
    }.

Structure wcompatible12 clo : Prop :=
  wcompat12_intro {
      wcompat12_mon: monotone12 clo;
      wcompat12_wcompat : forall r,
          clo (gf r) <12= gf (gupaco12 gf clo r);
    }.

Lemma rclo12_dist clo
      (MON: monotone12 clo)
      (DIST: forall r1 r2, clo (r1 \12/ r2) <12= (clo r1 \12/ clo r2)):
  forall r1 r2, rclo12 clo (r1 \12/ r2) <12= (rclo12 clo r1 \12/ rclo12 clo r2).
Proof.
  intros. induction PR.
  + destruct IN; [left|right]; apply rclo12_base, H.
  + assert (REL: clo (rclo12 clo r1 \12/ rclo12 clo r2) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11).
    { eapply MON. apply IN. apply H. }
    apply DIST in REL. destruct REL; [left|right]; apply rclo12_clo, H0.
Qed.

Lemma rclo12_compat clo
      (COM: compatible12 clo):
  compatible12 (rclo12 clo).
Proof.
  econstructor.
  - apply rclo12_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo12_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo12_clo. apply PR.
Qed.

Lemma rclo12_wcompat clo
      (COM: wcompatible12 clo):
  wcompatible12 (rclo12 clo).
Proof.
  econstructor.
  - apply rclo12_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. apply gpaco12_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply gpaco12_gupaco. apply gf_mon.
        eapply gupaco12_mon_gen; intros; [apply PR|apply gf_mon|apply PR0| |apply PR0].
        apply rclo12_clo_base, PR0.
Qed.

Lemma compat12_wcompat clo
      (CMP: compatible12 clo):
  wcompatible12 clo.
Proof.
  econstructor. apply CMP.
  intros. apply CMP in PR.
  eapply gf_mon. apply PR.
  intros. apply gpaco12_clo, PR0. 
Qed.

Lemma wcompat12_compat clo
      (WCMP: wcompatible12 clo) :
  compatible12 (gupaco12 gf clo).
Proof.
  econstructor.
  { red; intros. eapply gpaco12_mon. apply IN. apply LE. apply LE. }

  intros. apply gpaco12_unfold in PR; [|apply gf_mon].
  induction PR.
  - destruct IN; cycle 1.
    + eapply gf_mon. apply H.
      intros. apply gpaco12_base, PR.
    + eapply gf_mon. apply H.
      intros. apply gpaco12_gupaco. apply gf_mon.
      eapply gupaco12_mon. apply PR.
      intros. apply gpaco12_step. apply gf_mon.
      eapply gf_mon. destruct PR0 as [X|X]; apply X.
      intros. apply gpaco12_base, PR1.
  - eapply gf_mon, gpaco12_gupaco, gf_mon.
    apply WCMP. eapply WCMP. apply IN.
    intros. apply H, PR.
Qed.

Lemma wcompat12_union clo1 clo2
      (WCMP1: wcompatible12 clo1)
      (WCMP2: wcompatible12 clo2):
  wcompatible12 (clo1 \13/ clo2).
Proof.
  econstructor.
  - apply monotone12_union. apply WCMP1. apply WCMP2.
  - intros. destruct PR.
    + apply WCMP1 in H. eapply gf_mon. apply H.
      intros. eapply gupaco12_mon_gen. apply PR. apply gf_mon. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco12_mon_gen. apply PR. apply gf_mon.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
Qed.

End Compatibility.

Section Soundness.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone12 gf.

Lemma gpaco12_compat_init clo
      (CMP: compatible12 gf clo):
  gpaco12 gf clo bot12 bot12 <12= paco12 gf bot12.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo12_rclo, PR]. 
  apply compat12_compat with (gf:=gf). apply rclo12_compat. apply gf_mon. apply CMP.
  eapply rclo12_mon. apply IN.
  intros. destruct PR; [|contradiction]. _punfold H; [..|apply gpaco12_def_mon, gf_mon].
  eapply gpaco12_def_mon. apply gf_mon. apply H.
  intros. destruct PR; [|destruct H0; contradiction]. left. apply H0.
Qed.

Lemma gpaco12_init clo
      (WCMP: wcompatible12 gf clo):
  gpaco12 gf clo bot12 bot12 <12= paco12 gf bot12.
Proof.
  intros. eapply gpaco12_compat_init.
  - apply wcompat12_compat, WCMP. apply gf_mon.
  - eapply gpaco12_mon_bot. apply PR. apply gf_mon. intros; apply PR0.
    intros. apply gpaco12_clo, PR0.
Qed.

Lemma gpaco12_unfold_bot clo
      (WCMP: wcompatible12 gf clo):
  gpaco12 gf clo bot12 bot12 <12= gf (gpaco12 gf clo bot12 bot12).
Proof.
  intros. apply gpaco12_init in PR; [|apply WCMP].
  _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. destruct PR0; [|contradiction]. apply gpaco12_final. apply gf_mon. right. apply H.
Qed.

End Soundness.

Section Distributivity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone12 gf.

Lemma gpaco12_dist clo r rg
      (CMP: wcompatible12 gf clo)
      (DIST: forall r1 r2, clo (r1 \12/ r2) <12= (clo r1 \12/ clo r2)):
  gpaco12 gf clo r rg <12= (paco12 gf (rclo12 clo (rg \12/ r)) \12/ rclo12 clo r).
Proof.
  intros. apply gpaco12_unfold in PR; [|apply gf_mon].
  apply rclo12_dist in PR; [|apply CMP|apply DIST].
  destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 H.
  pcofix CIH; intros.
  apply rclo12_wcompat in H0; [|apply gf_mon|apply CMP].
  pstep. eapply gf_mon. apply H0. intros.
  apply gpaco12_unfold in PR; [|apply gf_mon].
  apply rclo12_compose in PR.
  apply rclo12_dist in PR; [|apply CMP|apply DIST].
  destruct PR.
  - right. apply CIH.
    eapply rclo12_mon. apply H. intros.
    eapply gf_mon. apply PR. intros.
    apply gpaco12_gupaco. apply gf_mon.
    apply gpaco12_gen_rclo. apply gf_mon.
    eapply gupaco12_mon. apply PR0. intros.
    destruct PR1; apply H1.
  - assert (REL: @rclo12 clo (rclo12 clo (gf (gupaco12 gf clo ((rg \12/ r) \12/ (rg \12/ r))) \12/ (rg \12/ r))) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11).
    { eapply rclo12_mon. apply H. intros. apply gpaco12_unfold in PR. apply PR. apply gf_mon. }
    apply rclo12_rclo in REL.
    apply rclo12_dist in REL; [|apply CMP|apply DIST].
    right. destruct REL; cycle 1.
    + apply CIH0, H1.
    + apply CIH.
      eapply rclo12_mon. apply H1. intros.
      eapply gf_mon. apply PR. intros.
      eapply gupaco12_mon. apply PR0. intros.
      destruct PR1; apply H2.
Qed.

Lemma gpaco12_dist_reverse clo r rg:
  (paco12 gf (rclo12 clo (rg \12/ r)) \12/ rclo12 clo r) <12= gpaco12 gf clo r rg.
Proof.
  intros. destruct PR; cycle 1.
  - eapply gpaco12_rclo. apply H.
  - econstructor. apply rclo12_base. left.
    revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 H. pcofix CIH; intros.
    _punfold H0; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H0. intros.
    destruct PR.
    + apply rclo12_base. right. apply CIH, H.
    + eapply rclo12_mon. apply H. intros.
      right. apply CIH0. apply PR.
Qed.

End Distributivity.

Section Companion.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone12 gf.

Inductive cpn12 (r: rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Prop :=
| cpn12_intro
    clo
    (COM: compatible12 gf clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
.

Lemma cpn12_mon: monotone12 cpn12.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat12_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn12_greatest: forall clo (COM: compatible12 gf clo), clo <13= cpn12.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn12_compat: compatible12 gf cpn12.
Proof.
  econstructor; [apply cpn12_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat12_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn12_wcompat: wcompatible12 gf cpn12.
Proof. apply compat12_wcompat, cpn12_compat. apply gf_mon. Qed.

Lemma cpn12_gupaco:
  gupaco12 gf cpn12 <13= cpn12.
Proof.
  intros. eapply cpn12_greatest, PR. apply wcompat12_compat. apply gf_mon. apply cpn12_wcompat.
Qed.

Lemma cpn12_cpn r:
  cpn12 (cpn12 r) <12= cpn12 r.
Proof.
  intros. apply cpn12_gupaco, gpaco12_gupaco, gpaco12_clo. apply gf_mon.
  eapply cpn12_mon, gpaco12_clo. apply PR.
Qed.

Lemma cpn12_base r:
  r <12= cpn12 r.
Proof.
  intros. apply cpn12_gupaco. apply gpaco12_base, PR.
Qed.

Lemma cpn12_clo
      r clo (LE: clo <13= cpn12):
  clo (cpn12 r) <12= cpn12 r.
Proof.
  intros. apply cpn12_cpn, LE, PR.
Qed.

Lemma cpn12_step r:
  gf (cpn12 r) <12= cpn12 r.
Proof.
  intros. apply cpn12_gupaco. apply gpaco12_step. apply gf_mon.
  eapply gf_mon, gpaco12_clo. apply PR.
Qed.

Lemma cpn12_uclo uclo
      (MON: monotone12 uclo)
      (WCOM: forall r, uclo (gf r) <12= gf (gupaco12 gf (uclo \13/ cpn12) r)):
  uclo <13= gupaco12 gf cpn12.
Proof.
  intros. apply gpaco12_clo.
  exists (gupaco12 gf (uclo \13/ cpn12)).
  - apply wcompat12_compat. apply gf_mon.
    econstructor.
    + apply monotone12_union. apply MON. apply cpn12_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat12_compat with (gf:=gf) in H; [| apply cpn12_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco12_clo. right. apply PR0.
  - apply gpaco12_clo. left. apply PR.
Qed.

End Companion.

Section Respectful.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone12 gf.

Structure wrespectful12 (clo: rel -> rel) : Prop :=
  wrespect12_intro {
      wrespect12_mon: monotone12 clo;
      wrespect12_respect :
        forall l r
               (LE: l <12= r)
               (GF: l <12= gf r),
        clo l <12= gf (rclo12 clo r);
    }.

Structure prespectful12 (clo: rel -> rel) : Prop :=
  prespect12_intro {
      prespect12_mon: monotone12 clo;
      prespect12_respect :
        forall l r
               (LE: l <12= r)
               (GF: l <12= gf r),
        clo l <12= paco12 gf (r \12/ clo r);
    }.

Structure grespectful12 (clo: rel -> rel) : Prop :=
  grespect12_intro {
      grespect12_mon: monotone12 clo;
      grespect12_respect :
        forall l r
               (LE: l <12= r)
               (GF: l <12= gf r),
        clo l <12= rclo12 (cpn12 gf) (gf (rclo12 (clo \13/ gupaco12 gf (cpn12 gf)) r));
    }.

Definition gf'12 := id /13\ gf.

Definition compatible'12 := compatible12 gf'12.

Lemma wrespect12_compatible'
      clo (RES: wrespectful12 clo):
  compatible'12 (rclo12 clo).
Proof.
  intros. econstructor. apply rclo12_mon.
  intros. destruct RES. split.
  { eapply rclo12_mon. apply PR. intros. apply PR0. }
  induction PR; intros.
  - eapply gf_mon. apply IN.
    intros. apply rclo12_base, PR.
  - eapply gf_mon.
    + eapply wrespect12_respect0; [|apply H|apply IN].
      intros. eapply rclo12_mon; intros; [apply LE, PR|apply PR0].
    + intros. apply rclo12_rclo, PR.
Qed.

Lemma prespect12_compatible'
      clo (RES: prespectful12 clo):
  compatible'12 (fun r => upaco12 gf (r \12/ clo r)).
Proof.
  econstructor.
  { red; intros. eapply upaco12_mon. apply IN.
    intros. destruct PR.
    - left. apply LE, H.
    - right. eapply RES. apply H. intros. apply LE, PR. }

  intros r.
  assert (LEM: (gf'12 r \12/ clo (gf'12 r)) <12= (r \12/ clo r)).
  { intros. destruct PR.
    - left. apply H.
    - right. eapply RES. apply H. intros. apply PR.
  }

  intros. destruct PR.
  - split.
    + left. eapply paco12_mon. apply H. apply LEM.
    + apply paco12_unfold; [apply gf_mon|].
      eapply paco12_mon. apply H. apply LEM.
  - split.
    + right. apply LEM. apply H.
    + destruct H.
      * eapply gf_mon. apply H. intros. right. left. apply PR.
      * apply paco12_unfold; [apply gf_mon|].
        eapply RES, H; intros; apply PR.
Qed.

Lemma grespect12_compatible'
      clo (RES: grespectful12 clo):
  compatible'12 (rclo12 (clo \13/ cpn12 gf)).
Proof.
  apply wrespect12_compatible'.
  econstructor.
  { red; intros. destruct IN.
    - left. eapply RES; [apply H|]. apply LE.
    - right. eapply cpn12_mon; [apply H|]. apply LE. }
  intros. destruct PR.
  - eapply RES.(grespect12_respect) in H; [|apply LE|apply GF].
    apply (@compat12_compat gf (rclo12 (cpn12 gf))) in H.
    2: { apply rclo12_compat; [apply gf_mon|]. apply cpn12_compat. apply gf_mon. }
    eapply gf_mon; [apply H|].
    intros. apply rclo12_clo. right.
    exists (rclo12 (cpn12 gf)).
    { apply rclo12_compat; [apply gf_mon|]. apply cpn12_compat. apply gf_mon. }
    eapply rclo12_mon; [eapply PR|].
    intros. eapply rclo12_mon_gen; [eapply PR0|..].
    + intros. destruct PR1.
      * left. apply H0.
      * right. apply cpn12_gupaco; [apply gf_mon|apply H0].
    + intros. apply PR1.
  - eapply gf_mon.
    + apply (@compat12_compat gf (rclo12 (cpn12 gf))).
      { apply rclo12_compat; [apply gf_mon|]. apply cpn12_compat. apply gf_mon. }
      eapply rclo12_clo_base. eapply cpn12_mon; [apply H|apply GF].
    + intros. eapply rclo12_mon_gen; [eapply PR|..].
      * intros. right. apply PR0.
      * intros. apply PR0.
Qed.

Lemma compat12_compatible'
      clo (COM: compatible12 gf clo):
  compatible'12 clo.
Proof.
  destruct COM. econstructor; [apply compat12_mon0|].
  intros. split.
  - eapply compat12_mon0; intros; [apply PR| apply PR0].
  - apply compat12_compat0.
    eapply compat12_mon0; intros; [apply PR| apply PR0].
Qed.

Lemma compatible'12_companion
      clo (RES: compatible'12 clo):
  clo <13= cpn12 gf.
Proof.
  assert (MON: monotone12 gf'12).
  { econstructor. apply LE, IN.
    eapply gf_mon, LE. apply IN.
  }
  assert (CPN: clo <13= cpn12 gf'12).
  { intros. econstructor. apply RES. apply PR.
  }
  intros. apply CPN in PR.
  econstructor; [|apply PR].
  econstructor; [apply cpn12_mon|]; intros.
  assert (PR1: cpn12 gf'12 (gf r) <12= cpn12 gf'12 (gf'12 (cpn12 gf r))).
  { intros. eapply cpn12_mon. apply PR1.
    intros. assert (TMP: gf (cpn12 gf r) <12= (cpn12 gf r /12\ gf (cpn12 gf r))).
    { split; [apply cpn12_step; [apply gf_mon|]|]; assumption. }
    apply TMP.
    eapply gf_mon. apply PR2. intros. apply cpn12_base; assumption.
  }
  apply PR1 in PR0. clear PR1. 
  eapply compat12_compat with (gf:=gf'12) in PR0; [|apply cpn12_compat, MON].
  eapply gf_mon; [apply PR0|].
  intros. eapply cpn12_cpn; [apply MON|].
  eapply cpn12_mon; [apply PR1|].
  intros. econstructor; [|apply PR2].
  apply compat12_compatible', cpn12_compat, gf_mon.
Qed.

Lemma wrespect12_companion
      clo (RES: wrespectful12 clo):
  clo <13= cpn12 gf.
Proof.
  intros. eapply wrespect12_compatible' in RES.
  eapply (@compatible'12_companion (rclo12 clo)) in RES; [apply RES|].
  eapply rclo12_clo_base, PR.
Qed.

Lemma prespect12_companion
      clo (RES: prespectful12 clo):
  clo <13= cpn12 gf.
Proof.
  intros. eapply compatible'12_companion. apply prespect12_compatible'. apply RES.
  right. right. apply PR.
Qed.

Lemma grespect12_companion
      clo (RES: grespectful12 clo):
  clo <13= cpn12 gf.
Proof.
  intros. eapply grespect12_compatible' in RES.
  eapply (@compatible'12_companion (rclo12 (clo \13/ cpn12 gf))); [apply RES|].
  apply rclo12_clo_base. left. apply PR.
Qed.

Lemma wrespect12_uclo
      clo (RES: wrespectful12 clo):
  clo <13= gupaco12 gf (cpn12 gf).
Proof.
  intros. eapply gpaco12_clo, wrespect12_companion, PR. apply RES.
Qed.

Lemma prespect12_uclo
      clo (RES: prespectful12 clo):
  clo <13= gupaco12 gf (cpn12 gf).
Proof.
  intros. eapply gpaco12_clo, prespect12_companion, PR. apply RES.
Qed.

Lemma grespect12_uclo
      clo (RES: grespectful12 clo):
  clo <13= gupaco12 gf (cpn12 gf).
Proof.
  intros. eapply gpaco12_clo, grespect12_companion, PR. apply RES.
Qed.

End Respectful.

End GeneralizedPaco12.

#[export] Hint Resolve gpaco12_def_mon : paco.
#[export] Hint Unfold gupaco12 : paco.
#[export] Hint Resolve gpaco12_base : paco.
#[export] Hint Resolve gpaco12_step : paco.
#[export] Hint Resolve gpaco12_final : paco.
#[export] Hint Resolve rclo12_base : paco.
#[export] Hint Constructors gpaco12 : paco.
#[export] Hint Resolve wrespect12_uclo : paco.
#[export] Hint Resolve prespect12_uclo : paco.
