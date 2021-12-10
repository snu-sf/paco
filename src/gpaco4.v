Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco4 pacotac.
Set Implicit Arguments.

Section GeneralizedPaco4.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.

Local Notation rel := (rel4 T0 T1 T2 T3).

Section RClo.

Inductive rclo4 (clo: rel->rel) (r: rel): rel :=
| rclo4_base
    x0 x1 x2 x3
    (IN: r x0 x1 x2 x3):
    @rclo4 clo r x0 x1 x2 x3
| rclo4_clo'
    r' x0 x1 x2 x3
    (LE: r' <4= rclo4 clo r)
    (IN: clo r' x0 x1 x2 x3):
    @rclo4 clo r x0 x1 x2 x3
.           

Lemma rclo4_mon_gen clo clo' r r' x0 x1 x2 x3
      (IN: @rclo4 clo r x0 x1 x2 x3)
      (LEclo: clo <5= clo')
      (LEr: r <4= r') :
  @rclo4 clo' r' x0 x1 x2 x3.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo4_mon clo:
  monotone4 (rclo4 clo).
Proof.
  repeat intro. eapply rclo4_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo4_clo clo r:
  clo (rclo4 clo r) <4= rclo4 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo4_clo_base clo r:
  clo r <4= rclo4 clo r.
Proof.
  intros. eapply rclo4_clo', PR.
  intros. apply rclo4_base, PR0.
Qed.

Lemma rclo4_rclo clo r:
  rclo4 clo (rclo4 clo r) <4= rclo4 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo4_compose clo r:
  rclo4 (rclo4 clo) r <4= rclo4 clo r.
Proof.
  intros. induction PR.
  - apply rclo4_base, IN.
  - apply rclo4_rclo.
    eapply rclo4_mon; [apply IN|apply H].
Qed.

End RClo.  

Section Main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone4 gf.

Variant gpaco4 clo r rg x0 x1 x2 x3 : Prop :=
| gpaco4_intro (IN: @rclo4 clo (paco4 (compose gf (rclo4 clo)) (rg \4/ r) \4/ r) x0 x1 x2 x3)
.

Definition gupaco4 clo r := gpaco4 clo r r.

Lemma gpaco4_def_mon clo : monotone4 (compose gf (rclo4 clo)).
Proof.
  eapply monotone4_compose. apply gf_mon. apply rclo4_mon.
Qed.

#[local] Hint Resolve gpaco4_def_mon : paco.

Lemma gpaco4_mon clo r r' rg rg' x0 x1 x2 x3
      (IN: @gpaco4 clo r rg x0 x1 x2 x3)
      (LEr: r <4= r')
      (LErg: rg <4= rg'):
  @gpaco4 clo r' rg' x0 x1 x2 x3.
Proof.
  destruct IN. econstructor.
  eapply rclo4_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco4_mon. apply H.
  intros. destruct PR.
  - left. apply LErg, H0.
  - right. apply LEr, H0.
Qed.

Lemma gupaco4_mon clo r r' x0 x1 x2 x3
      (IN: @gupaco4 clo r x0 x1 x2 x3)
      (LEr: r <4= r'):
  @gupaco4 clo r' x0 x1 x2 x3.
Proof.
  eapply gpaco4_mon. apply IN. apply LEr. apply LEr.
Qed.

Lemma gpaco4_base clo r rg: r <4= gpaco4 clo r rg.
Proof.
  econstructor. apply rclo4_base. right. apply PR.
Qed.

Lemma gpaco4_gen_guard  clo r rg:
  gpaco4 clo r (rg \4/ r) <4= gpaco4 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  eapply rclo4_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco4_mon_gen; intros. apply H. apply PR.
  destruct PR. apply H0. right. apply H0.
Qed.

Lemma gpaco4_rclo clo r rg:
  rclo4 clo r <4= gpaco4 clo r rg.
Proof.
  intros. econstructor.
  eapply rclo4_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco4_clo clo r rg:
  clo r <4= gpaco4 clo r rg.
Proof.
  intros. apply gpaco4_rclo. eapply rclo4_clo_base, PR.
Qed.

Lemma gpaco4_gen_rclo clo r rg:
  gpaco4 (rclo4 clo) r rg <4= gpaco4 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  apply rclo4_compose.
  eapply rclo4_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco4_mon_gen; intros; [apply H| |apply PR].
  eapply gf_mon, rclo4_compose. apply PR.
Qed.

Lemma gpaco4_step_gen clo r rg:
  gf (gpaco4 clo (rg \4/ r) (rg \4/ r)) <4= gpaco4 clo r rg.
Proof.
  intros. econstructor. apply rclo4_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo4_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco4_mon. apply H. intros. destruct PR0; apply H0.
  - right. apply H.
Qed.

Lemma gpaco4_step clo r rg:
  gf (gpaco4 clo rg rg) <4= gpaco4 clo r rg.
Proof.
  intros. apply gpaco4_step_gen.
  eapply gf_mon. apply PR. intros.
  eapply gpaco4_mon. apply PR0. left; apply PR1. left; apply PR1.
Qed.

Lemma gpaco4_final clo r rg:
  (r \4/ paco4 gf rg) <4= gpaco4 clo r rg.
Proof.
  intros. destruct PR. apply gpaco4_base, H.
  econstructor. apply rclo4_base.
  left. eapply paco4_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo4_base. apply PR0.
  - intros. left. apply PR.
Qed.

Lemma gpaco4_unfold clo r rg:
  gpaco4 clo r rg <4= rclo4 clo (gf (gupaco4 clo (rg \4/ r)) \4/ r).
Proof.
  intros. destruct PR.
  eapply rclo4_mon. apply IN.
  intros. destruct PR; cycle 1. right; apply H.
  left. _punfold H; [|apply gpaco4_def_mon].
  eapply gf_mon. apply H.
  intros. econstructor.
  eapply rclo4_mon. apply PR.
  intros. destruct PR0; cycle 1. right. apply H0.
  left. eapply paco4_mon. apply H0.
  intros. left. apply PR0.
Qed.
  
Lemma gpaco4_cofix clo r rg 
      l (OBG: forall rr (INC: rg <4= rr) (CIH: l <4= rr), l <4= gpaco4 clo r rr):
  l <4= gpaco4 clo r rg.
Proof.
  assert (IN: l <4= gpaco4 clo r (rg \4/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo4_mon. apply IN0.
  clear x0 x1 x2 x3 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply gpaco4_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo4_rclo. eapply rclo4_mon. apply PR.
  intros. destruct PR0.
  - apply rclo4_base. right. apply CIH. apply H.
  - destruct H; [destruct H|].
    + apply rclo4_base. right. apply CIH0. left. apply H.
    + apply IN in H. destruct H.
      eapply rclo4_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. right. apply H.
    + apply rclo4_base. right. apply CIH0. right. apply H.
Qed.

Lemma gpaco4_gupaco clo r rg:
  gupaco4 clo (gpaco4 clo r rg) <4= gpaco4 clo r rg.
Proof.
  eapply gpaco4_cofix.
  intros. destruct PR. econstructor.
  apply rclo4_rclo. eapply rclo4_mon. apply IN.
  intros. destruct PR.
  - apply rclo4_base. left.
    eapply paco4_mon. apply H.
    intros. left; apply CIH.
    econstructor. apply rclo4_base. right.
    destruct PR; apply H0.
  - destruct H. eapply rclo4_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco4_mon. apply H.
    intros. destruct PR.
    + left. apply INC. apply H0.
    + right. apply H0.
Qed.

Lemma gpaco4_gpaco clo r rg:
  gpaco4 clo (gpaco4 clo r rg) (gupaco4 clo (rg \4/ r)) <4= gpaco4 clo r rg.
Proof.
  intros. apply gpaco4_unfold in PR.
  econstructor. apply rclo4_rclo. eapply rclo4_mon. apply PR. clear x0 x1 x2 x3 PR. intros.
  destruct PR; [|destruct H; apply IN].
  apply rclo4_base. left. pstep.
  eapply gf_mon. apply H. clear x0 x1 x2 x3 H. intros.
  cut (@gupaco4 clo (rg \4/ r) x0 x1 x2 x3).
  { intros. destruct H. eapply rclo4_mon. apply IN. intros.
    destruct PR0; [|right; apply H].
    left. eapply paco4_mon. apply H. intros. destruct PR0; apply H0.
  }
  apply gpaco4_gupaco. eapply gupaco4_mon. apply PR. intros.
  destruct PR0; [apply H|].
  eapply gpaco4_mon; [apply H|right|left]; intros; apply PR0.
Qed.

Lemma gpaco4_uclo uclo clo r rg 
      (LEclo: uclo <5= gupaco4 clo) :
  uclo (gpaco4 clo r rg) <4= gpaco4 clo r rg.
Proof.
  intros. apply gpaco4_gupaco. apply LEclo, PR.
Qed.

Lemma gpaco4_weaken  clo r rg:
  gpaco4 (gupaco4 clo) r rg <4= gpaco4 clo r rg.
Proof.
  intros. apply gpaco4_unfold in PR.
  induction PR.
  - destruct IN; cycle 1. apply gpaco4_base, H.
    apply gpaco4_step_gen. eapply gf_mon. apply H.
    clear x0 x1 x2 x3 H.
    eapply gpaco4_cofix. intros.
    apply gpaco4_unfold in PR.
    induction PR.
    + destruct IN; cycle 1. apply gpaco4_base, H.
      apply gpaco4_step. eapply gf_mon. apply H.
      intros. apply gpaco4_base. apply CIH.
      eapply gupaco4_mon. apply PR.
      intros. destruct PR0; apply H0.
    + apply gpaco4_gupaco.
      eapply gupaco4_mon. apply IN. apply H.
  - apply gpaco4_gupaco.
    eapply gupaco4_mon. apply IN. apply H.
Qed.

End Main.

#[local] Hint Resolve gpaco4_def_mon : paco.

Section GeneralMonotonicity.

Variable gf: rel -> rel.
  
Lemma gpaco4_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 r r' rg rg'
      (IN: @gpaco4 gf clo r rg x0 x1 x2 x3)
      (gf_mon: monotone4 gf)
      (LEgf: gf <5= gf')
      (LEclo: clo <5= clo')
      (LEr: r <4= r')
      (LErg: rg <4= rg') :
  @gpaco4 gf' clo' r' rg' x0 x1 x2 x3.
Proof.
  eapply gpaco4_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo4_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco4_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply gf_mon. apply PR.
    intros. eapply rclo4_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma gpaco4_mon_bot (gf' clo clo': rel -> rel) x0 x1 x2 x3 r' rg'
      (IN: @gpaco4 gf clo bot4 bot4 x0 x1 x2 x3)
      (gf_mon: monotone4 gf)
      (LEgf: gf <5= gf')
      (LEclo: clo <5= clo'):
  @gpaco4 gf' clo' r' rg' x0 x1 x2 x3.
Proof.
  eapply gpaco4_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco4_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 r r'
      (IN: @gupaco4 gf clo r x0 x1 x2 x3)
      (gf_mon: monotone4 gf)
      (LEgf: gf <5= gf')
      (LEclo: clo <5= clo')
      (LEr: r <4= r'):
  @gupaco4 gf' clo' r' x0 x1 x2 x3.
Proof.
  eapply gpaco4_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. apply LEr. apply LEr.
Qed.

End GeneralMonotonicity.

Section Compatibility.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone4 gf.

Structure compatible4 (clo: rel -> rel) : Prop :=
  compat4_intro {
      compat4_mon: monotone4 clo;
      compat4_compat : forall r,
          clo (gf r) <4= gf (clo r);
    }.

Structure wcompatible4 clo : Prop :=
  wcompat4_intro {
      wcompat4_mon: monotone4 clo;
      wcompat4_wcompat : forall r,
          clo (gf r) <4= gf (gupaco4 gf clo r);
    }.

Lemma rclo4_dist clo
      (MON: monotone4 clo)
      (DIST: forall r1 r2, clo (r1 \4/ r2) <4= (clo r1 \4/ clo r2)):
  forall r1 r2, rclo4 clo (r1 \4/ r2) <4= (rclo4 clo r1 \4/ rclo4 clo r2).
Proof.
  intros. induction PR.
  + destruct IN; [left|right]; apply rclo4_base, H.
  + assert (REL: clo (rclo4 clo r1 \4/ rclo4 clo r2) x0 x1 x2 x3).
    { eapply MON. apply IN. apply H. }
    apply DIST in REL. destruct REL; [left|right]; apply rclo4_clo, H0.
Qed.

Lemma rclo4_compat clo
      (COM: compatible4 clo):
  compatible4 (rclo4 clo).
Proof.
  econstructor.
  - apply rclo4_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo4_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo4_clo. apply PR.
Qed.

Lemma rclo4_wcompat clo
      (COM: wcompatible4 clo):
  wcompatible4 (rclo4 clo).
Proof.
  econstructor.
  - apply rclo4_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. apply gpaco4_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply gpaco4_gupaco. apply gf_mon.
        eapply gupaco4_mon_gen; intros; [apply PR|apply gf_mon|apply PR0| |apply PR0].
        apply rclo4_clo_base, PR0.
Qed.

Lemma compat4_wcompat clo
      (CMP: compatible4 clo):
  wcompatible4 clo.
Proof.
  econstructor. apply CMP.
  intros. apply CMP in PR.
  eapply gf_mon. apply PR.
  intros. apply gpaco4_clo, PR0. 
Qed.

Lemma wcompat4_compat clo
      (WCMP: wcompatible4 clo) :
  compatible4 (gupaco4 gf clo).
Proof.
  econstructor.
  { red; intros. eapply gpaco4_mon. apply IN. apply LE. apply LE. }

  intros. apply gpaco4_unfold in PR; [|apply gf_mon].
  induction PR.
  - destruct IN; cycle 1.
    + eapply gf_mon. apply H.
      intros. apply gpaco4_base, PR.
    + eapply gf_mon. apply H.
      intros. apply gpaco4_gupaco. apply gf_mon.
      eapply gupaco4_mon. apply PR.
      intros. apply gpaco4_step. apply gf_mon.
      eapply gf_mon. destruct PR0 as [X|X]; apply X.
      intros. apply gpaco4_base, PR1.
  - eapply gf_mon, gpaco4_gupaco, gf_mon.
    apply WCMP. eapply WCMP. apply IN.
    intros. apply H, PR.
Qed.

Lemma wcompat4_union clo1 clo2
      (WCMP1: wcompatible4 clo1)
      (WCMP2: wcompatible4 clo2):
  wcompatible4 (clo1 \5/ clo2).
Proof.
  econstructor.
  - apply monotone4_union. apply WCMP1. apply WCMP2.
  - intros. destruct PR.
    + apply WCMP1 in H. eapply gf_mon. apply H.
      intros. eapply gupaco4_mon_gen. apply PR. apply gf_mon. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco4_mon_gen. apply PR. apply gf_mon.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
Qed.

End Compatibility.

Section Soundness.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone4 gf.

Lemma gpaco4_compat_init clo
      (CMP: compatible4 gf clo):
  gpaco4 gf clo bot4 bot4 <4= paco4 gf bot4.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo4_rclo, PR]. 
  apply compat4_compat with (gf:=gf). apply rclo4_compat. apply gf_mon. apply CMP.
  eapply rclo4_mon. apply IN.
  intros. destruct PR; [|contradiction]. _punfold H; [..|apply gpaco4_def_mon, gf_mon].
  eapply gpaco4_def_mon. apply gf_mon. apply H.
  intros. destruct PR; [|destruct H0; contradiction]. left. apply H0.
Qed.

Lemma gpaco4_init clo
      (WCMP: wcompatible4 gf clo):
  gpaco4 gf clo bot4 bot4 <4= paco4 gf bot4.
Proof.
  intros. eapply gpaco4_compat_init.
  - apply wcompat4_compat, WCMP. apply gf_mon.
  - eapply gpaco4_mon_bot. apply PR. apply gf_mon. intros; apply PR0.
    intros. apply gpaco4_clo, PR0.
Qed.

Lemma gpaco4_unfold_bot clo
      (WCMP: wcompatible4 gf clo):
  gpaco4 gf clo bot4 bot4 <4= gf (gpaco4 gf clo bot4 bot4).
Proof.
  intros. apply gpaco4_init in PR; [|apply WCMP].
  _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. destruct PR0; [|contradiction]. apply gpaco4_final. apply gf_mon. right. apply H.
Qed.

End Soundness.

Section Distributivity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone4 gf.

Lemma gpaco4_dist clo r rg
      (CMP: wcompatible4 gf clo)
      (DIST: forall r1 r2, clo (r1 \4/ r2) <4= (clo r1 \4/ clo r2)):
  gpaco4 gf clo r rg <4= (paco4 gf (rclo4 clo (rg \4/ r)) \4/ rclo4 clo r).
Proof.
  intros. apply gpaco4_unfold in PR; [|apply gf_mon].
  apply rclo4_dist in PR; [|apply CMP|apply DIST].
  destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 H.
  pcofix CIH; intros.
  apply rclo4_wcompat in H0; [|apply gf_mon|apply CMP].
  pstep. eapply gf_mon. apply H0. intros.
  apply gpaco4_unfold in PR; [|apply gf_mon].
  apply rclo4_compose in PR.
  apply rclo4_dist in PR; [|apply CMP|apply DIST].
  destruct PR.
  - right. apply CIH.
    eapply rclo4_mon. apply H. intros.
    eapply gf_mon. apply PR. intros.
    apply gpaco4_gupaco. apply gf_mon.
    apply gpaco4_gen_rclo. apply gf_mon.
    eapply gupaco4_mon. apply PR0. intros.
    destruct PR1; apply H1.
  - assert (REL: @rclo4 clo (rclo4 clo (gf (gupaco4 gf clo ((rg \4/ r) \4/ (rg \4/ r))) \4/ (rg \4/ r))) x0 x1 x2 x3).
    { eapply rclo4_mon. apply H. intros. apply gpaco4_unfold in PR. apply PR. apply gf_mon. }
    apply rclo4_rclo in REL.
    apply rclo4_dist in REL; [|apply CMP|apply DIST].
    right. destruct REL; cycle 1.
    + apply CIH0, H1.
    + apply CIH.
      eapply rclo4_mon. apply H1. intros.
      eapply gf_mon. apply PR. intros.
      eapply gupaco4_mon. apply PR0. intros.
      destruct PR1; apply H2.
Qed.

Lemma gpaco4_dist_reverse clo r rg:
  (paco4 gf (rclo4 clo (rg \4/ r)) \4/ rclo4 clo r) <4= gpaco4 gf clo r rg.
Proof.
  intros. destruct PR; cycle 1.
  - eapply gpaco4_rclo. apply H.
  - econstructor. apply rclo4_base. left.
    revert x0 x1 x2 x3 H. pcofix CIH; intros.
    _punfold H0; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H0. intros.
    destruct PR.
    + apply rclo4_base. right. apply CIH, H.
    + eapply rclo4_mon. apply H. intros.
      right. apply CIH0. apply PR.
Qed.

End Distributivity.

Section Companion.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone4 gf.

Inductive cpn4 (r: rel) x0 x1 x2 x3 : Prop :=
| cpn4_intro
    clo
    (COM: compatible4 gf clo)
    (CLO: clo r x0 x1 x2 x3)
.

Lemma cpn4_mon: monotone4 cpn4.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat4_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn4_greatest: forall clo (COM: compatible4 gf clo), clo <5= cpn4.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn4_compat: compatible4 gf cpn4.
Proof.
  econstructor; [apply cpn4_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat4_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn4_wcompat: wcompatible4 gf cpn4.
Proof. apply compat4_wcompat, cpn4_compat. apply gf_mon. Qed.

Lemma cpn4_gupaco:
  gupaco4 gf cpn4 <5= cpn4.
Proof.
  intros. eapply cpn4_greatest, PR. apply wcompat4_compat. apply gf_mon. apply cpn4_wcompat.
Qed.

Lemma cpn4_cpn r:
  cpn4 (cpn4 r) <4= cpn4 r.
Proof.
  intros. apply cpn4_gupaco, gpaco4_gupaco, gpaco4_clo. apply gf_mon.
  eapply cpn4_mon, gpaco4_clo. apply PR.
Qed.

Lemma cpn4_base r:
  r <4= cpn4 r.
Proof.
  intros. apply cpn4_gupaco. apply gpaco4_base, PR.
Qed.

Lemma cpn4_clo
      r clo (LE: clo <5= cpn4):
  clo (cpn4 r) <4= cpn4 r.
Proof.
  intros. apply cpn4_cpn, LE, PR.
Qed.

Lemma cpn4_step r:
  gf (cpn4 r) <4= cpn4 r.
Proof.
  intros. apply cpn4_gupaco. apply gpaco4_step. apply gf_mon.
  eapply gf_mon, gpaco4_clo. apply PR.
Qed.

Lemma cpn4_uclo uclo
      (MON: monotone4 uclo)
      (WCOM: forall r, uclo (gf r) <4= gf (gupaco4 gf (uclo \5/ cpn4) r)):
  uclo <5= gupaco4 gf cpn4.
Proof.
  intros. apply gpaco4_clo.
  exists (gupaco4 gf (uclo \5/ cpn4)).
  - apply wcompat4_compat. apply gf_mon.
    econstructor.
    + apply monotone4_union. apply MON. apply cpn4_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat4_compat with (gf:=gf) in H; [| apply cpn4_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco4_clo. right. apply PR0.
  - apply gpaco4_clo. left. apply PR.
Qed.

End Companion.

Section Respectful.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone4 gf.

Structure wrespectful4 (clo: rel -> rel) : Prop :=
  wrespect4_intro {
      wrespect4_mon: monotone4 clo;
      wrespect4_respect :
        forall l r
               (LE: l <4= r)
               (GF: l <4= gf r),
        clo l <4= gf (rclo4 clo r);
    }.

Structure prespectful4 (clo: rel -> rel) : Prop :=
  prespect4_intro {
      prespect4_mon: monotone4 clo;
      prespect4_respect :
        forall l r
               (LE: l <4= r)
               (GF: l <4= gf r),
        clo l <4= paco4 gf (r \4/ clo r);
    }.

Structure grespectful4 (clo: rel -> rel) : Prop :=
  grespect4_intro {
      grespect4_mon: monotone4 clo;
      grespect4_respect :
        forall l r
               (LE: l <4= r)
               (GF: l <4= gf r),
        clo l <4= rclo4 (cpn4 gf) (gf (rclo4 (clo \5/ gupaco4 gf (cpn4 gf)) r));
    }.

Definition gf'4 := id /5\ gf.

Definition compatible'4 := compatible4 gf'4.

Lemma wrespect4_compatible'
      clo (RES: wrespectful4 clo):
  compatible'4 (rclo4 clo).
Proof.
  intros. econstructor. apply rclo4_mon.
  intros. destruct RES. split.
  { eapply rclo4_mon. apply PR. intros. apply PR0. }
  induction PR; intros.
  - eapply gf_mon. apply IN.
    intros. apply rclo4_base, PR.
  - eapply gf_mon.
    + eapply wrespect4_respect0; [|apply H|apply IN].
      intros. eapply rclo4_mon; intros; [apply LE, PR|apply PR0].
    + intros. apply rclo4_rclo, PR.
Qed.

Lemma prespect4_compatible'
      clo (RES: prespectful4 clo):
  compatible'4 (fun r => upaco4 gf (r \4/ clo r)).
Proof.
  econstructor.
  { red; intros. eapply upaco4_mon. apply IN.
    intros. destruct PR.
    - left. apply LE, H.
    - right. eapply RES. apply H. intros. apply LE, PR. }

  intros r.
  assert (LEM: (gf'4 r \4/ clo (gf'4 r)) <4= (r \4/ clo r)).
  { intros. destruct PR.
    - left. apply H.
    - right. eapply RES. apply H. intros. apply PR.
  }

  intros. destruct PR.
  - split.
    + left. eapply paco4_mon. apply H. apply LEM.
    + apply paco4_unfold; [apply gf_mon|].
      eapply paco4_mon. apply H. apply LEM.
  - split.
    + right. apply LEM. apply H.
    + destruct H.
      * eapply gf_mon. apply H. intros. right. left. apply PR.
      * apply paco4_unfold; [apply gf_mon|].
        eapply RES, H; intros; apply PR.
Qed.

Lemma grespect4_compatible'
      clo (RES: grespectful4 clo):
  compatible'4 (rclo4 (clo \5/ cpn4 gf)).
Proof.
  apply wrespect4_compatible'.
  econstructor.
  { red; intros. destruct IN.
    - left. eapply RES; [apply H|]. apply LE.
    - right. eapply cpn4_mon; [apply H|]. apply LE. }
  intros. destruct PR.
  - eapply RES.(grespect4_respect) in H; [|apply LE|apply GF].
    apply (@compat4_compat gf (rclo4 (cpn4 gf))) in H.
    2: { apply rclo4_compat; [apply gf_mon|]. apply cpn4_compat. apply gf_mon. }
    eapply gf_mon; [apply H|].
    intros. apply rclo4_clo. right.
    exists (rclo4 (cpn4 gf)).
    { apply rclo4_compat; [apply gf_mon|]. apply cpn4_compat. apply gf_mon. }
    eapply rclo4_mon; [eapply PR|].
    intros. eapply rclo4_mon_gen; [eapply PR0|..].
    + intros. destruct PR1.
      * left. apply H0.
      * right. apply cpn4_gupaco; [apply gf_mon|apply H0].
    + intros. apply PR1.
  - eapply gf_mon.
    + apply (@compat4_compat gf (rclo4 (cpn4 gf))).
      { apply rclo4_compat; [apply gf_mon|]. apply cpn4_compat. apply gf_mon. }
      eapply rclo4_clo_base. eapply cpn4_mon; [apply H|apply GF].
    + intros. eapply rclo4_mon_gen; [eapply PR|..].
      * intros. right. apply PR0.
      * intros. apply PR0.
Qed.

Lemma compat4_compatible'
      clo (COM: compatible4 gf clo):
  compatible'4 clo.
Proof.
  destruct COM. econstructor; [apply compat4_mon0|].
  intros. split.
  - eapply compat4_mon0; intros; [apply PR| apply PR0].
  - apply compat4_compat0.
    eapply compat4_mon0; intros; [apply PR| apply PR0].
Qed.

Lemma compatible'4_companion
      clo (RES: compatible'4 clo):
  clo <5= cpn4 gf.
Proof.
  assert (MON: monotone4 gf'4).
  { econstructor. apply LE, IN.
    eapply gf_mon, LE. apply IN.
  }
  assert (CPN: clo <5= cpn4 gf'4).
  { intros. econstructor. apply RES. apply PR.
  }
  intros. apply CPN in PR.
  econstructor; [|apply PR].
  econstructor; [apply cpn4_mon|]; intros.
  assert (PR1: cpn4 gf'4 (gf r) <4= cpn4 gf'4 (gf'4 (cpn4 gf r))).
  { intros. eapply cpn4_mon. apply PR1.
    intros. assert (TMP: gf (cpn4 gf r) <4= (cpn4 gf r /4\ gf (cpn4 gf r))).
    { split; [apply cpn4_step; [apply gf_mon|]|]; assumption. }
    apply TMP.
    eapply gf_mon. apply PR2. intros. apply cpn4_base; assumption.
  }
  apply PR1 in PR0. clear PR1. 
  eapply compat4_compat with (gf:=gf'4) in PR0; [|apply cpn4_compat, MON].
  eapply gf_mon; [apply PR0|].
  intros. eapply cpn4_cpn; [apply MON|].
  eapply cpn4_mon; [apply PR1|].
  intros. econstructor; [|apply PR2].
  apply compat4_compatible', cpn4_compat, gf_mon.
Qed.

Lemma wrespect4_companion
      clo (RES: wrespectful4 clo):
  clo <5= cpn4 gf.
Proof.
  intros. eapply wrespect4_compatible' in RES.
  eapply (@compatible'4_companion (rclo4 clo)) in RES; [apply RES|].
  eapply rclo4_clo_base, PR.
Qed.

Lemma prespect4_companion
      clo (RES: prespectful4 clo):
  clo <5= cpn4 gf.
Proof.
  intros. eapply compatible'4_companion. apply prespect4_compatible'. apply RES.
  right. right. apply PR.
Qed.

Lemma grespect4_companion
      clo (RES: grespectful4 clo):
  clo <5= cpn4 gf.
Proof.
  intros. eapply grespect4_compatible' in RES.
  eapply (@compatible'4_companion (rclo4 (clo \5/ cpn4 gf))); [apply RES|].
  apply rclo4_clo_base. left. apply PR.
Qed.

Lemma wrespect4_uclo
      clo (RES: wrespectful4 clo):
  clo <5= gupaco4 gf (cpn4 gf).
Proof.
  intros. eapply gpaco4_clo, wrespect4_companion, PR. apply RES.
Qed.

Lemma prespect4_uclo
      clo (RES: prespectful4 clo):
  clo <5= gupaco4 gf (cpn4 gf).
Proof.
  intros. eapply gpaco4_clo, prespect4_companion, PR. apply RES.
Qed.

Lemma grespect4_uclo
      clo (RES: grespectful4 clo):
  clo <5= gupaco4 gf (cpn4 gf).
Proof.
  intros. eapply gpaco4_clo, grespect4_companion, PR. apply RES.
Qed.

End Respectful.

End GeneralizedPaco4.

#[export] Hint Resolve gpaco4_def_mon : paco.
#[export] Hint Unfold gupaco4 : paco.
#[export] Hint Resolve gpaco4_base : paco.
#[export] Hint Resolve gpaco4_step : paco.
#[export] Hint Resolve gpaco4_final : paco.
#[export] Hint Resolve rclo4_base : paco.
#[export] Hint Constructors gpaco4 : paco.
#[export] Hint Resolve wrespect4_uclo : paco.
#[export] Hint Resolve prespect4_uclo : paco.
