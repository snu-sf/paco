Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco10 pacotac.
Set Implicit Arguments.

Section GeneralizedPaco10.

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

Local Notation rel := (rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9).

Section RClo.

Inductive rclo10 (clo: rel->rel) (r: rel): rel :=
| rclo10_base
    x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    (IN: r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9):
    @rclo10 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
| rclo10_clo'
    r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    (LE: r' <10= rclo10 clo r)
    (IN: clo r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9):
    @rclo10 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
.           

Lemma rclo10_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
      (IN: @rclo10 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (LEclo: clo <11= clo')
      (LEr: r <10= r') :
  @rclo10 clo' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo10_mon clo:
  monotone10 (rclo10 clo).
Proof.
  repeat intro. eapply rclo10_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo10_clo clo r:
  clo (rclo10 clo r) <10= rclo10 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo10_clo_base clo r:
  clo r <10= rclo10 clo r.
Proof.
  intros. eapply rclo10_clo', PR.
  intros. apply rclo10_base, PR0.
Qed.

Lemma rclo10_rclo clo r:
  rclo10 clo (rclo10 clo r) <10= rclo10 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo10_compose clo r:
  rclo10 (rclo10 clo) r <10= rclo10 clo r.
Proof.
  intros. induction PR.
  - apply rclo10_base, IN.
  - apply rclo10_rclo.
    eapply rclo10_mon; [apply IN|apply H].
Qed.

End RClo.  

Section Main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone10 gf.

Variant gpaco10 clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop :=
| gpaco10_intro (IN: @rclo10 clo (paco10 (compose gf (rclo10 clo)) (rg \10/ r) \10/ r) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
.

Definition gupaco10 clo r := gpaco10 clo r r.

Lemma gpaco10_def_mon clo : monotone10 (compose gf (rclo10 clo)).
Proof.
  eapply monotone10_compose. apply gf_mon. apply rclo10_mon.
Qed.

Hint Resolve gpaco10_def_mon : paco.

Lemma gpaco10_mon clo r r' rg rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
      (IN: @gpaco10 clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (LEr: r <10= r')
      (LErg: rg <10= rg'):
  @gpaco10 clo r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  destruct IN. econstructor.
  eapply rclo10_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco10_mon. apply H.
  intros. destruct PR.
  - left. apply LErg, H0.
  - right. apply LEr, H0.
Qed.

Lemma gupaco10_mon clo r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
      (IN: @gupaco10 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (LEr: r <10= r'):
  @gupaco10 clo r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  eapply gpaco10_mon. apply IN. apply LEr. apply LEr.
Qed.

Lemma gpaco10_base clo r rg: r <10= gpaco10 clo r rg.
Proof.
  econstructor. apply rclo10_base. right. apply PR.
Qed.

Lemma gpaco10_gen_guard  clo r rg:
  gpaco10 clo r (rg \10/ r) <10= gpaco10 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  eapply rclo10_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco10_mon_gen; intros. apply H. apply PR.
  destruct PR. apply H0. right. apply H0.
Qed.

Lemma gpaco10_rclo clo r rg:
  rclo10 clo r <10= gpaco10 clo r rg.
Proof.
  intros. econstructor.
  eapply rclo10_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco10_clo clo r rg:
  clo r <10= gpaco10 clo r rg.
Proof.
  intros. apply gpaco10_rclo. eapply rclo10_clo_base, PR.
Qed.

Lemma gpaco10_gen_rclo clo r rg:
  gpaco10 (rclo10 clo) r rg <10= gpaco10 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  apply rclo10_compose.
  eapply rclo10_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco10_mon_gen; intros; [apply H| |apply PR].
  eapply gf_mon, rclo10_compose. apply PR.
Qed.

Lemma gpaco10_step_gen clo r rg:
  gf (gpaco10 clo (rg \10/ r) (rg \10/ r)) <10= gpaco10 clo r rg.
Proof.
  intros. econstructor. apply rclo10_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo10_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco10_mon. apply H. intros. destruct PR0; apply H0.
  - right. apply H.
Qed.

Lemma gpaco10_step clo r rg:
  gf (gpaco10 clo rg rg) <10= gpaco10 clo r rg.
Proof.
  intros. apply gpaco10_step_gen.
  eapply gf_mon. apply PR. intros.
  eapply gpaco10_mon. apply PR0. left; apply PR1. left; apply PR1.
Qed.

Lemma gpaco10_final clo r rg:
  (r \10/ paco10 gf rg) <10= gpaco10 clo r rg.
Proof.
  intros. destruct PR. apply gpaco10_base, H.
  econstructor. apply rclo10_base.
  left. eapply paco10_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo10_base. apply PR0.
  - intros. left. apply PR.
Qed.

Lemma gpaco10_unfold clo r rg:
  gpaco10 clo r rg <10= rclo10 clo (gf (gupaco10 clo (rg \10/ r)) \10/ r).
Proof.
  intros. destruct PR.
  eapply rclo10_mon. apply IN.
  intros. destruct PR; cycle 1. right; apply H.
  left. _punfold H; [|apply gpaco10_def_mon].
  eapply gf_mon. apply H.
  intros. econstructor.
  eapply rclo10_mon. apply PR.
  intros. destruct PR0; cycle 1. right. apply H0.
  left. eapply paco10_mon. apply H0.
  intros. left. apply PR0.
Qed.
  
Lemma gpaco10_cofix clo r rg 
      l (OBG: forall rr (INC: rg <10= rr) (CIH: l <10= rr), l <10= gpaco10 clo r rr):
  l <10= gpaco10 clo r rg.
Proof.
  assert (IN: l <10= gpaco10 clo r (rg \10/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo10_mon. apply IN0.
  clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply gpaco10_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo10_rclo. eapply rclo10_mon. apply PR.
  intros. destruct PR0.
  - apply rclo10_base. right. apply CIH. apply H.
  - destruct H; [destruct H|].
    + apply rclo10_base. right. apply CIH0. left. apply H.
    + apply IN in H. destruct H.
      eapply rclo10_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. right. apply H.
    + apply rclo10_base. right. apply CIH0. right. apply H.
Qed.

Lemma gpaco10_gupaco clo r rg:
  gupaco10 clo (gpaco10 clo r rg) <10= gpaco10 clo r rg.
Proof.
  eapply gpaco10_cofix.
  intros. destruct PR. econstructor.
  apply rclo10_rclo. eapply rclo10_mon. apply IN.
  intros. destruct PR.
  - apply rclo10_base. left.
    eapply paco10_mon. apply H.
    intros. left; apply CIH.
    econstructor. apply rclo10_base. right.
    destruct PR; apply H0.
  - destruct H. eapply rclo10_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco10_mon. apply H.
    intros. destruct PR.
    + left. apply INC. apply H0.
    + right. apply H0.
Qed.

Lemma gpaco10_gpaco clo r rg:
  gpaco10 clo (gpaco10 clo r rg) (gupaco10 clo (rg \10/ r)) <10= gpaco10 clo r rg.
Proof.
  intros. apply gpaco10_unfold in PR.
  econstructor. apply rclo10_rclo. eapply rclo10_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 PR. intros.
  destruct PR; [|destruct H; apply IN].
  apply rclo10_base. left. pstep.
  eapply gf_mon. apply H. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 H. intros.
  cut (@gupaco10 clo (rg \10/ r) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9).
  { intros. destruct H. eapply rclo10_mon. apply IN. intros.
    destruct PR0; [|right; apply H].
    left. eapply paco10_mon. apply H. intros. destruct PR0; apply H0.
  }
  apply gpaco10_gupaco. eapply gupaco10_mon. apply PR. intros.
  destruct PR0; [apply H|].
  eapply gpaco10_mon; [apply H|right|left]; intros; apply PR0.
Qed.

Lemma gpaco10_uclo uclo clo r rg 
      (LEclo: uclo <11= gupaco10 clo) :
  uclo (gpaco10 clo r rg) <10= gpaco10 clo r rg.
Proof.
  intros. apply gpaco10_gupaco. apply LEclo, PR.
Qed.

Lemma gpaco10_weaken  clo r rg:
  gpaco10 (gupaco10 clo) r rg <10= gpaco10 clo r rg.
Proof.
  intros. apply gpaco10_unfold in PR.
  induction PR.
  - destruct IN; cycle 1. apply gpaco10_base, H.
    apply gpaco10_step_gen. eapply gf_mon. apply H.
    clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 H.
    eapply gpaco10_cofix. intros.
    apply gpaco10_unfold in PR.
    induction PR.
    + destruct IN; cycle 1. apply gpaco10_base, H.
      apply gpaco10_step. eapply gf_mon. apply H.
      intros. apply gpaco10_base. apply CIH.
      eapply gupaco10_mon. apply PR.
      intros. destruct PR0; apply H0.
    + apply gpaco10_gupaco.
      eapply gupaco10_mon. apply IN. apply H.
  - apply gpaco10_gupaco.
    eapply gupaco10_mon. apply IN. apply H.
Qed.

End Main.

Hint Resolve gpaco10_def_mon : paco.

Section GeneralMonotonicity.

Variable gf: rel -> rel.
  
Lemma gpaco10_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r r' rg rg'
      (IN: @gpaco10 gf clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (gf_mon: monotone10 gf)
      (LEgf: gf <11= gf')
      (LEclo: clo <11= clo')
      (LEr: r <10= r')
      (LErg: rg <10= rg') :
  @gpaco10 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  eapply gpaco10_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo10_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco10_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply gf_mon. apply PR.
    intros. eapply rclo10_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma gpaco10_mon_bot (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r' rg'
      (IN: @gpaco10 gf clo bot10 bot10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (gf_mon: monotone10 gf)
      (LEgf: gf <11= gf')
      (LEclo: clo <11= clo'):
  @gpaco10 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  eapply gpaco10_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco10_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r r'
      (IN: @gupaco10 gf clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (gf_mon: monotone10 gf)
      (LEgf: gf <11= gf')
      (LEclo: clo <11= clo')
      (LEr: r <10= r'):
  @gupaco10 gf' clo' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  eapply gpaco10_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. apply LEr. apply LEr.
Qed.

End GeneralMonotonicity.

Section Compatibility.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone10 gf.

Structure compatible10 (clo: rel -> rel) : Prop :=
  compat10_intro {
      compat10_mon: monotone10 clo;
      compat10_compat : forall r,
          clo (gf r) <10= gf (clo r);
    }.

Structure wcompatible10 clo : Prop :=
  wcompat10_intro {
      wcompat10_mon: monotone10 clo;
      wcompat10_wcompat : forall r,
          clo (gf r) <10= gf (gupaco10 gf clo r);
    }.

Lemma rclo10_dist clo
      (MON: monotone10 clo)
      (DIST: forall r1 r2, clo (r1 \10/ r2) <10= (clo r1 \10/ clo r2)):
  forall r1 r2, rclo10 clo (r1 \10/ r2) <10= (rclo10 clo r1 \10/ rclo10 clo r2).
Proof.
  intros. induction PR.
  + destruct IN; [left|right]; apply rclo10_base, H.
  + assert (REL: clo (rclo10 clo r1 \10/ rclo10 clo r2) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9).
    { eapply MON. apply IN. apply H. }
    apply DIST in REL. destruct REL; [left|right]; apply rclo10_clo, H0.
Qed.

Lemma rclo10_compat clo
      (COM: compatible10 clo):
  compatible10 (rclo10 clo).
Proof.
  econstructor.
  - apply rclo10_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo10_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo10_clo. apply PR.
Qed.

Lemma rclo10_wcompat clo
      (COM: wcompatible10 clo):
  wcompatible10 (rclo10 clo).
Proof.
  econstructor.
  - apply rclo10_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. apply gpaco10_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply gpaco10_gupaco. apply gf_mon.
        eapply gupaco10_mon_gen; intros; [apply PR|apply gf_mon|apply PR0| |apply PR0].
        apply rclo10_clo_base, PR0.
Qed.

Lemma compat10_wcompat clo
      (CMP: compatible10 clo):
  wcompatible10 clo.
Proof.
  econstructor. apply CMP.
  intros. apply CMP in PR.
  eapply gf_mon. apply PR.
  intros. apply gpaco10_clo, PR0. 
Qed.

Lemma wcompat10_compat clo
      (WCMP: wcompatible10 clo) :
  compatible10 (gupaco10 gf clo).
Proof.
  econstructor.
  { red; intros. eapply gpaco10_mon. apply IN. apply LE. apply LE. }

  intros. apply gpaco10_unfold in PR; [|apply gf_mon].
  induction PR.
  - destruct IN; cycle 1.
    + eapply gf_mon. apply H.
      intros. apply gpaco10_base, PR.
    + eapply gf_mon. apply H.
      intros. apply gpaco10_gupaco. apply gf_mon.
      eapply gupaco10_mon. apply PR.
      intros. apply gpaco10_step. apply gf_mon.
      eapply gf_mon. destruct PR0 as [X|X]; apply X.
      intros. apply gpaco10_base, PR1.
  - eapply gf_mon, gpaco10_gupaco, gf_mon.
    apply WCMP. eapply WCMP. apply IN.
    intros. apply H, PR.
Qed.

Lemma wcompat10_union clo1 clo2
      (WCMP1: wcompatible10 clo1)
      (WCMP2: wcompatible10 clo2):
  wcompatible10 (clo1 \11/ clo2).
Proof.
  econstructor.
  - apply monotone10_union. apply WCMP1. apply WCMP2.
  - intros. destruct PR.
    + apply WCMP1 in H. eapply gf_mon. apply H.
      intros. eapply gupaco10_mon_gen. apply PR. apply gf_mon. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco10_mon_gen. apply PR. apply gf_mon.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
Qed.

End Compatibility.

Section Soundness.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone10 gf.

Lemma gpaco10_compat_init clo
      (CMP: compatible10 gf clo):
  gpaco10 gf clo bot10 bot10 <10= paco10 gf bot10.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo10_rclo, PR]. 
  apply compat10_compat with (gf:=gf). apply rclo10_compat. apply gf_mon. apply CMP.
  eapply rclo10_mon. apply IN.
  intros. destruct PR; [|contradiction]. _punfold H; [..|apply gpaco10_def_mon, gf_mon].
  eapply gpaco10_def_mon. apply gf_mon. apply H.
  intros. destruct PR; [|destruct H0; contradiction]. left. apply H0.
Qed.

Lemma gpaco10_init clo
      (WCMP: wcompatible10 gf clo):
  gpaco10 gf clo bot10 bot10 <10= paco10 gf bot10.
Proof.
  intros. eapply gpaco10_compat_init.
  - apply wcompat10_compat, WCMP. apply gf_mon.
  - eapply gpaco10_mon_bot. apply PR. apply gf_mon. intros; apply PR0.
    intros. apply gpaco10_clo, PR0.
Qed.

Lemma gpaco10_unfold_bot clo
      (WCMP: wcompatible10 gf clo):
  gpaco10 gf clo bot10 bot10 <10= gf (gpaco10 gf clo bot10 bot10).
Proof.
  intros. apply gpaco10_init in PR; [|apply WCMP].
  _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. destruct PR0; [|contradiction]. apply gpaco10_final. apply gf_mon. right. apply H.
Qed.

End Soundness.

Section Distributivity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone10 gf.

Lemma gpaco10_dist clo r rg
      (CMP: wcompatible10 gf clo)
      (DIST: forall r1 r2, clo (r1 \10/ r2) <10= (clo r1 \10/ clo r2)):
  gpaco10 gf clo r rg <10= (paco10 gf (rclo10 clo (rg \10/ r)) \10/ rclo10 clo r).
Proof.
  intros. apply gpaco10_unfold in PR; [|apply gf_mon].
  apply rclo10_dist in PR; [|apply CMP|apply DIST].
  destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 H.
  pcofix CIH; intros.
  apply rclo10_wcompat in H0; [|apply gf_mon|apply CMP].
  pstep. eapply gf_mon. apply H0. intros.
  apply gpaco10_unfold in PR; [|apply gf_mon].
  apply rclo10_compose in PR.
  apply rclo10_dist in PR; [|apply CMP|apply DIST].
  destruct PR.
  - right. apply CIH.
    eapply rclo10_mon. apply H. intros.
    eapply gf_mon. apply PR. intros.
    apply gpaco10_gupaco. apply gf_mon.
    apply gpaco10_gen_rclo. apply gf_mon.
    eapply gupaco10_mon. apply PR0. intros.
    destruct PR1; apply H1.
  - assert (REL: @rclo10 clo (rclo10 clo (gf (gupaco10 gf clo ((rg \10/ r) \10/ (rg \10/ r))) \10/ (rg \10/ r))) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9).
    { eapply rclo10_mon. apply H. intros. apply gpaco10_unfold in PR. apply PR. apply gf_mon. }
    apply rclo10_rclo in REL.
    apply rclo10_dist in REL; [|apply CMP|apply DIST].
    right. destruct REL; cycle 1.
    + apply CIH0, H1.
    + apply CIH.
      eapply rclo10_mon. apply H1. intros.
      eapply gf_mon. apply PR. intros.
      eapply gupaco10_mon. apply PR0. intros.
      destruct PR1; apply H2.
Qed.

Lemma gpaco10_dist_reverse clo r rg:
  (paco10 gf (rclo10 clo (rg \10/ r)) \10/ rclo10 clo r) <10= gpaco10 gf clo r rg.
Proof.
  intros. destruct PR; cycle 1.
  - eapply gpaco10_rclo. apply H.
  - econstructor. apply rclo10_base. left.
    revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 H. pcofix CIH; intros.
    _punfold H0; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H0. intros.
    destruct PR.
    + apply rclo10_base. right. apply CIH, H.
    + eapply rclo10_mon. apply H. intros.
      right. apply CIH0. apply PR.
Qed.

End Distributivity.

Section Companion.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone10 gf.

Inductive cpn10 (r: rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop :=
| cpn10_intro
    clo
    (COM: compatible10 gf clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
.

Lemma cpn10_mon: monotone10 cpn10.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat10_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn10_greatest: forall clo (COM: compatible10 gf clo), clo <11= cpn10.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn10_compat: compatible10 gf cpn10.
Proof.
  econstructor; [apply cpn10_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat10_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn10_wcompat: wcompatible10 gf cpn10.
Proof. apply compat10_wcompat, cpn10_compat. apply gf_mon. Qed.

Lemma cpn10_gupaco:
  gupaco10 gf cpn10 <11= cpn10.
Proof.
  intros. eapply cpn10_greatest, PR. apply wcompat10_compat. apply gf_mon. apply cpn10_wcompat.
Qed.

Lemma cpn10_cpn r:
  cpn10 (cpn10 r) <10= cpn10 r.
Proof.
  intros. apply cpn10_gupaco, gpaco10_gupaco, gpaco10_clo. apply gf_mon.
  eapply cpn10_mon, gpaco10_clo. apply PR.
Qed.

Lemma cpn10_base r:
  r <10= cpn10 r.
Proof.
  intros. apply cpn10_gupaco. apply gpaco10_base, PR.
Qed.

Lemma cpn10_clo
      r clo (LE: clo <11= cpn10):
  clo (cpn10 r) <10= cpn10 r.
Proof.
  intros. apply cpn10_cpn, LE, PR.
Qed.

Lemma cpn10_step r:
  gf (cpn10 r) <10= cpn10 r.
Proof.
  intros. apply cpn10_gupaco. apply gpaco10_step. apply gf_mon.
  eapply gf_mon, gpaco10_clo. apply PR.
Qed.

Lemma cpn10_uclo uclo
      (MON: monotone10 uclo)
      (WCOM: forall r, uclo (gf r) <10= gf (gupaco10 gf (uclo \11/ cpn10) r)):
  uclo <11= gupaco10 gf cpn10.
Proof.
  intros. apply gpaco10_clo.
  exists (gupaco10 gf (uclo \11/ cpn10)).
  - apply wcompat10_compat. apply gf_mon.
    econstructor.
    + apply monotone10_union. apply MON. apply cpn10_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat10_compat with (gf:=gf) in H; [| apply cpn10_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco10_clo. right. apply PR0.
  - apply gpaco10_clo. left. apply PR.
Qed.

End Companion.

Section Respectful.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone10 gf.

Structure wrespectful10 (clo: rel -> rel) : Prop :=
  wrespect10_intro {
      wrespect10_mon: monotone10 clo;
      wrespect10_respect :
        forall l r
               (LE: l <10= r)
               (GF: l <10= gf r),
        clo l <10= gf (rclo10 clo r);
    }.

Structure prespectful10 (clo: rel -> rel) : Prop :=
  prespect10_intro {
      prespect10_mon: monotone10 clo;
      prespect10_respect :
        forall l r
               (LE: l <10= r)
               (GF: l <10= gf r),
        clo l <10= paco10 gf (r \10/ clo r);
    }.

Structure grespectful10 (clo: rel -> rel) : Prop :=
  grespect10_intro {
      grespect10_mon: monotone10 clo;
      grespect10_respect :
        forall l r
               (LE: l <10= r)
               (GF: l <10= gf r),
        clo l <10= rclo10 (cpn10 gf) (gf (rclo10 (clo \11/ gupaco10 gf (cpn10 gf)) r));
    }.

Definition gf'10 := id /11\ gf.

Definition compatible'10 := compatible10 gf'10.

Lemma wrespect10_compatible'
      clo (RES: wrespectful10 clo):
  compatible'10 (rclo10 clo).
Proof.
  intros. econstructor. apply rclo10_mon.
  intros. destruct RES. split.
  { eapply rclo10_mon. apply PR. intros. apply PR0. }
  induction PR; intros.
  - eapply gf_mon. apply IN.
    intros. apply rclo10_base, PR.
  - eapply gf_mon.
    + eapply wrespect10_respect0; [|apply H|apply IN].
      intros. eapply rclo10_mon; intros; [apply LE, PR|apply PR0].
    + intros. apply rclo10_rclo, PR.
Qed.

Lemma prespect10_compatible'
      clo (RES: prespectful10 clo):
  compatible'10 (fun r => upaco10 gf (r \10/ clo r)).
Proof.
  econstructor.
  { red; intros. eapply upaco10_mon. apply IN.
    intros. destruct PR.
    - left. apply LE, H.
    - right. eapply RES. apply H. intros. apply LE, PR. }

  intros r.
  assert (LEM: (gf'10 r \10/ clo (gf'10 r)) <10= (r \10/ clo r)).
  { intros. destruct PR.
    - left. apply H.
    - right. eapply RES. apply H. intros. apply PR.
  }

  intros. destruct PR.
  - split.
    + left. eapply paco10_mon. apply H. apply LEM.
    + apply paco10_unfold; [apply gf_mon|].
      eapply paco10_mon. apply H. apply LEM.
  - split.
    + right. apply LEM. apply H.
    + destruct H.
      * eapply gf_mon. apply H. intros. right. left. apply PR.
      * apply paco10_unfold; [apply gf_mon|].
        eapply RES, H; intros; apply PR.
Qed.

Lemma grespect10_compatible'
      clo (RES: grespectful10 clo):
  compatible'10 (rclo10 (clo \11/ cpn10 gf)).
Proof.
  apply wrespect10_compatible'.
  econstructor.
  { red; intros. destruct IN.
    - left. eapply RES; [apply H|]. apply LE.
    - right. eapply cpn10_mon; [apply H|]. apply LE. }
  intros. destruct PR.
  - eapply RES.(grespect10_respect) in H; [|apply LE|apply GF].
    apply (@compat10_compat gf (rclo10 (cpn10 gf))) in H.
    2: { apply rclo10_compat; [apply gf_mon|]. apply cpn10_compat. apply gf_mon. }
    eapply gf_mon; [apply H|].
    intros. apply rclo10_clo. right.
    exists (rclo10 (cpn10 gf)).
    { apply rclo10_compat; [apply gf_mon|]. apply cpn10_compat. apply gf_mon. }
    eapply rclo10_mon; [eapply PR|].
    intros. eapply rclo10_mon_gen; [eapply PR0|..].
    + intros. destruct PR1.
      * left. apply H0.
      * right. apply cpn10_gupaco; [apply gf_mon|apply H0].
    + intros. apply PR1.
  - eapply gf_mon.
    + apply (@compat10_compat gf (rclo10 (cpn10 gf))).
      { apply rclo10_compat; [apply gf_mon|]. apply cpn10_compat. apply gf_mon. }
      eapply rclo10_clo_base. eapply cpn10_mon; [apply H|apply GF].
    + intros. eapply rclo10_mon_gen; [eapply PR|..].
      * intros. right. apply PR0.
      * intros. apply PR0.
Qed.

Lemma compat10_compatible'
      clo (COM: compatible10 gf clo):
  compatible'10 clo.
Proof.
  destruct COM. econstructor; [apply compat10_mon0|].
  intros. split.
  - eapply compat10_mon0; intros; [apply PR| apply PR0].
  - apply compat10_compat0.
    eapply compat10_mon0; intros; [apply PR| apply PR0].
Qed.

Lemma compatible'10_companion
      clo (RES: compatible'10 clo):
  clo <11= cpn10 gf.
Proof.
  assert (MON: monotone10 gf'10).
  { econstructor. apply LE, IN.
    eapply gf_mon, LE. apply IN.
  }
  assert (CPN: clo <11= cpn10 gf'10).
  { intros. econstructor. apply RES. apply PR.
  }
  intros. apply CPN in PR.
  econstructor; [|apply PR].
  econstructor; [apply cpn10_mon|]; intros.
  assert (PR1: cpn10 gf'10 (gf r) <10= cpn10 gf'10 (gf'10 (cpn10 gf r))).
  { intros. eapply cpn10_mon. apply PR1.
    intros. assert (TMP: gf (cpn10 gf r) <10= (cpn10 gf r /10\ gf (cpn10 gf r))).
    { split; [apply cpn10_step; [apply gf_mon|]|]; assumption. }
    apply TMP.
    eapply gf_mon. apply PR2. intros. apply cpn10_base; assumption.
  }
  apply PR1 in PR0. clear PR1. 
  eapply compat10_compat with (gf:=gf'10) in PR0; [|apply cpn10_compat, MON].
  eapply gf_mon; [apply PR0|].
  intros. eapply cpn10_cpn; [apply MON|].
  eapply cpn10_mon; [apply PR1|].
  intros. econstructor; [|apply PR2].
  apply compat10_compatible', cpn10_compat, gf_mon.
Qed.

Lemma wrespect10_companion
      clo (RES: wrespectful10 clo):
  clo <11= cpn10 gf.
Proof.
  intros. eapply wrespect10_compatible' in RES.
  eapply (@compatible'10_companion (rclo10 clo)) in RES; [apply RES|].
  eapply rclo10_clo_base, PR.
Qed.

Lemma prespect10_companion
      clo (RES: prespectful10 clo):
  clo <11= cpn10 gf.
Proof.
  intros. eapply compatible'10_companion. apply prespect10_compatible'. apply RES.
  right. right. apply PR.
Qed.

Lemma grespect10_companion
      clo (RES: grespectful10 clo):
  clo <11= cpn10 gf.
Proof.
  intros. eapply grespect10_compatible' in RES.
  eapply (@compatible'10_companion (rclo10 (clo \11/ cpn10 gf))); [apply RES|].
  apply rclo10_clo_base. left. apply PR.
Qed.

Lemma wrespect10_uclo
      clo (RES: wrespectful10 clo):
  clo <11= gupaco10 gf (cpn10 gf).
Proof.
  intros. eapply gpaco10_clo, wrespect10_companion, PR. apply RES.
Qed.

Lemma prespect10_uclo
      clo (RES: prespectful10 clo):
  clo <11= gupaco10 gf (cpn10 gf).
Proof.
  intros. eapply gpaco10_clo, prespect10_companion, PR. apply RES.
Qed.

Lemma grespect10_uclo
      clo (RES: grespectful10 clo):
  clo <11= gupaco10 gf (cpn10 gf).
Proof.
  intros. eapply gpaco10_clo, grespect10_companion, PR. apply RES.
Qed.

End Respectful.

End GeneralizedPaco10.

Hint Resolve gpaco10_def_mon : paco.
Hint Unfold gupaco10 : paco.
Hint Resolve gpaco10_base : paco.
Hint Resolve gpaco10_step : paco.
Hint Resolve gpaco10_final : paco.
Hint Resolve rclo10_base : paco.
Hint Constructors gpaco10 : paco.
Hint Resolve wrespect10_uclo : paco.
Hint Resolve prespect10_uclo : paco.
