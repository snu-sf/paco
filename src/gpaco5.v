Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco5 pacotac.
Set Implicit Arguments.

Section GeneralizedPaco5.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.

Local Notation rel := (rel5 T0 T1 T2 T3 T4).

Section RClo.

Inductive rclo5 (clo: rel->rel) (r: rel): rel :=
| rclo5_base
    x0 x1 x2 x3 x4
    (IN: r x0 x1 x2 x3 x4):
    @rclo5 clo r x0 x1 x2 x3 x4
| rclo5_clo'
    r' x0 x1 x2 x3 x4
    (LE: r' <5= rclo5 clo r)
    (IN: clo r' x0 x1 x2 x3 x4):
    @rclo5 clo r x0 x1 x2 x3 x4
.           

Lemma rclo5_mon_gen clo clo' r r' x0 x1 x2 x3 x4
      (IN: @rclo5 clo r x0 x1 x2 x3 x4)
      (LEclo: clo <6= clo')
      (LEr: r <5= r') :
  @rclo5 clo' r' x0 x1 x2 x3 x4.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo5_mon clo:
  monotone5 (rclo5 clo).
Proof.
  repeat intro. eapply rclo5_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo5_clo clo r:
  clo (rclo5 clo r) <5= rclo5 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo5_clo_base clo r:
  clo r <5= rclo5 clo r.
Proof.
  intros. eapply rclo5_clo', PR.
  intros. apply rclo5_base, PR0.
Qed.

Lemma rclo5_rclo clo r:
  rclo5 clo (rclo5 clo r) <5= rclo5 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo5_compose clo r:
  rclo5 (rclo5 clo) r <5= rclo5 clo r.
Proof.
  intros. induction PR.
  - apply rclo5_base, IN.
  - apply rclo5_rclo.
    eapply rclo5_mon; [apply IN|apply H].
Qed.

End RClo.  

Section Main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone5 gf.

Variant gpaco5 clo r rg x0 x1 x2 x3 x4 : Prop :=
| gpaco5_intro (IN: @rclo5 clo (paco5 (compose gf (rclo5 clo)) (rg \5/ r) \5/ r) x0 x1 x2 x3 x4)
.

Definition gupaco5 clo r := gpaco5 clo r r.

Lemma gpaco5_def_mon clo : monotone5 (compose gf (rclo5 clo)).
Proof.
  eapply monotone5_compose. apply gf_mon. apply rclo5_mon.
Qed.

Hint Resolve gpaco5_def_mon : paco.

Lemma gpaco5_mon clo r r' rg rg' x0 x1 x2 x3 x4
      (IN: @gpaco5 clo r rg x0 x1 x2 x3 x4)
      (LEr: r <5= r')
      (LErg: rg <5= rg'):
  @gpaco5 clo r' rg' x0 x1 x2 x3 x4.
Proof.
  destruct IN. econstructor.
  eapply rclo5_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco5_mon. apply H.
  intros. destruct PR.
  - left. apply LErg, H0.
  - right. apply LEr, H0.
Qed.

Lemma gupaco5_mon clo r r' x0 x1 x2 x3 x4
      (IN: @gupaco5 clo r x0 x1 x2 x3 x4)
      (LEr: r <5= r'):
  @gupaco5 clo r' x0 x1 x2 x3 x4.
Proof.
  eapply gpaco5_mon. apply IN. apply LEr. apply LEr.
Qed.

Lemma gpaco5_base clo r rg: r <5= gpaco5 clo r rg.
Proof.
  econstructor. apply rclo5_base. right. apply PR.
Qed.

Lemma gpaco5_gen_guard  clo r rg:
  gpaco5 clo r (rg \5/ r) <5= gpaco5 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  eapply rclo5_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco5_mon_gen; intros. apply H. apply PR.
  destruct PR. apply H0. right. apply H0.
Qed.

Lemma gpaco5_rclo clo r rg:
  rclo5 clo r <5= gpaco5 clo r rg.
Proof.
  intros. econstructor.
  eapply rclo5_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco5_clo clo r rg:
  clo r <5= gpaco5 clo r rg.
Proof.
  intros. apply gpaco5_rclo. eapply rclo5_clo_base, PR.
Qed.

Lemma gpaco5_gen_rclo clo r rg:
  gpaco5 (rclo5 clo) r rg <5= gpaco5 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  apply rclo5_compose.
  eapply rclo5_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco5_mon_gen; intros; [apply H| |apply PR].
  eapply gf_mon, rclo5_compose. apply PR.
Qed.

Lemma gpaco5_step_gen clo r rg:
  gf (gpaco5 clo (rg \5/ r) (rg \5/ r)) <5= gpaco5 clo r rg.
Proof.
  intros. econstructor. apply rclo5_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo5_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco5_mon. apply H. intros. destruct PR0; apply H0.
  - right. apply H.
Qed.

Lemma gpaco5_step clo r rg:
  gf (gpaco5 clo rg rg) <5= gpaco5 clo r rg.
Proof.
  intros. apply gpaco5_step_gen.
  eapply gf_mon. apply PR. intros.
  eapply gpaco5_mon. apply PR0. left; apply PR1. left; apply PR1.
Qed.

Lemma gpaco5_final clo r rg:
  (r \5/ paco5 gf rg) <5= gpaco5 clo r rg.
Proof.
  intros. destruct PR. apply gpaco5_base, H.
  econstructor. apply rclo5_base.
  left. eapply paco5_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo5_base. apply PR0.
  - intros. left. apply PR.
Qed.

Lemma gpaco5_unfold clo r rg:
  gpaco5 clo r rg <5= rclo5 clo (gf (gupaco5 clo (rg \5/ r)) \5/ r).
Proof.
  intros. destruct PR.
  eapply rclo5_mon. apply IN.
  intros. destruct PR; cycle 1. right; apply H.
  left. _punfold H; [|apply gpaco5_def_mon].
  eapply gf_mon. apply H.
  intros. econstructor.
  eapply rclo5_mon. apply PR.
  intros. destruct PR0; cycle 1. right. apply H0.
  left. eapply paco5_mon. apply H0.
  intros. left. apply PR0.
Qed.
  
Lemma gpaco5_cofix clo r rg 
      l (OBG: forall rr (INC: rg <5= rr) (CIH: l <5= rr), l <5= gpaco5 clo r rr):
  l <5= gpaco5 clo r rg.
Proof.
  assert (IN: l <5= gpaco5 clo r (rg \5/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo5_mon. apply IN0.
  clear x0 x1 x2 x3 x4 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply gpaco5_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo5_rclo. eapply rclo5_mon. apply PR.
  intros. destruct PR0.
  - apply rclo5_base. right. apply CIH. apply H.
  - destruct H; [destruct H|].
    + apply rclo5_base. right. apply CIH0. left. apply H.
    + apply IN in H. destruct H.
      eapply rclo5_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. right. apply H.
    + apply rclo5_base. right. apply CIH0. right. apply H.
Qed.

Lemma gpaco5_gupaco clo r rg:
  gupaco5 clo (gpaco5 clo r rg) <5= gpaco5 clo r rg.
Proof.
  eapply gpaco5_cofix.
  intros. destruct PR. econstructor.
  apply rclo5_rclo. eapply rclo5_mon. apply IN.
  intros. destruct PR.
  - apply rclo5_base. left.
    eapply paco5_mon. apply H.
    intros. left; apply CIH.
    econstructor. apply rclo5_base. right.
    destruct PR; apply H0.
  - destruct H. eapply rclo5_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco5_mon. apply H.
    intros. destruct PR.
    + left. apply INC. apply H0.
    + right. apply H0.
Qed.

Lemma gpaco5_gpaco clo r rg:
  gpaco5 clo (gpaco5 clo r rg) (gupaco5 clo (rg \5/ r)) <5= gpaco5 clo r rg.
Proof.
  intros. apply gpaco5_unfold in PR.
  econstructor. apply rclo5_rclo. eapply rclo5_mon. apply PR. clear x0 x1 x2 x3 x4 PR. intros.
  destruct PR; [|destruct H; apply IN].
  apply rclo5_base. left. pstep.
  eapply gf_mon. apply H. clear x0 x1 x2 x3 x4 H. intros.
  cut (@gupaco5 clo (rg \5/ r) x0 x1 x2 x3 x4).
  { intros. destruct H. eapply rclo5_mon. apply IN. intros.
    destruct PR0; [|right; apply H].
    left. eapply paco5_mon. apply H. intros. destruct PR0; apply H0.
  }
  apply gpaco5_gupaco. eapply gupaco5_mon. apply PR. intros.
  destruct PR0; [apply H|].
  eapply gpaco5_mon; [apply H|right|left]; intros; apply PR0.
Qed.

Lemma gpaco5_uclo uclo clo r rg 
      (LEclo: uclo <6= gupaco5 clo) :
  uclo (gpaco5 clo r rg) <5= gpaco5 clo r rg.
Proof.
  intros. apply gpaco5_gupaco. apply LEclo, PR.
Qed.

Lemma gpaco5_weaken  clo r rg:
  gpaco5 (gupaco5 clo) r rg <5= gpaco5 clo r rg.
Proof.
  intros. apply gpaco5_unfold in PR.
  induction PR.
  - destruct IN; cycle 1. apply gpaco5_base, H.
    apply gpaco5_step_gen. eapply gf_mon. apply H.
    clear x0 x1 x2 x3 x4 H.
    eapply gpaco5_cofix. intros.
    apply gpaco5_unfold in PR.
    induction PR.
    + destruct IN; cycle 1. apply gpaco5_base, H.
      apply gpaco5_step. eapply gf_mon. apply H.
      intros. apply gpaco5_base. apply CIH.
      eapply gupaco5_mon. apply PR.
      intros. destruct PR0; apply H0.
    + apply gpaco5_gupaco.
      eapply gupaco5_mon. apply IN. apply H.
  - apply gpaco5_gupaco.
    eapply gupaco5_mon. apply IN. apply H.
Qed.

End Main.

Hint Resolve gpaco5_def_mon : paco.

Section GeneralMonotonicity.

Variable gf: rel -> rel.
  
Lemma gpaco5_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 r r' rg rg'
      (IN: @gpaco5 gf clo r rg x0 x1 x2 x3 x4)
      (gf_mon: monotone5 gf)
      (LEgf: gf <6= gf')
      (LEclo: clo <6= clo')
      (LEr: r <5= r')
      (LErg: rg <5= rg') :
  @gpaco5 gf' clo' r' rg' x0 x1 x2 x3 x4.
Proof.
  eapply gpaco5_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo5_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco5_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply gf_mon. apply PR.
    intros. eapply rclo5_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma gpaco5_mon_bot (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 r' rg'
      (IN: @gpaco5 gf clo bot5 bot5 x0 x1 x2 x3 x4)
      (gf_mon: monotone5 gf)
      (LEgf: gf <6= gf')
      (LEclo: clo <6= clo'):
  @gpaco5 gf' clo' r' rg' x0 x1 x2 x3 x4.
Proof.
  eapply gpaco5_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco5_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 r r'
      (IN: @gupaco5 gf clo r x0 x1 x2 x3 x4)
      (gf_mon: monotone5 gf)
      (LEgf: gf <6= gf')
      (LEclo: clo <6= clo')
      (LEr: r <5= r'):
  @gupaco5 gf' clo' r' x0 x1 x2 x3 x4.
Proof.
  eapply gpaco5_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. apply LEr. apply LEr.
Qed.

End GeneralMonotonicity.

Section Compatibility.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone5 gf.

Structure compatible5 (clo: rel -> rel) : Prop :=
  compat5_intro {
      compat5_mon: monotone5 clo;
      compat5_compat : forall r,
          clo (gf r) <5= gf (clo r);
    }.

Structure wcompatible5 clo : Prop :=
  wcompat5_intro {
      wcompat5_mon: monotone5 clo;
      wcompat5_wcompat : forall r,
          clo (gf r) <5= gf (gupaco5 gf clo r);
    }.

Lemma rclo5_dist clo
      (MON: monotone5 clo)
      (DIST: forall r1 r2, clo (r1 \5/ r2) <5= (clo r1 \5/ clo r2)):
  forall r1 r2, rclo5 clo (r1 \5/ r2) <5= (rclo5 clo r1 \5/ rclo5 clo r2).
Proof.
  intros. induction PR.
  + destruct IN; [left|right]; apply rclo5_base, H.
  + assert (REL: clo (rclo5 clo r1 \5/ rclo5 clo r2) x0 x1 x2 x3 x4).
    { eapply MON. apply IN. apply H. }
    apply DIST in REL. destruct REL; [left|right]; apply rclo5_clo, H0.
Qed.

Lemma rclo5_compat clo
      (COM: compatible5 clo):
  compatible5 (rclo5 clo).
Proof.
  econstructor.
  - apply rclo5_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo5_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo5_clo. apply PR.
Qed.

Lemma rclo5_wcompat clo
      (COM: wcompatible5 clo):
  wcompatible5 (rclo5 clo).
Proof.
  econstructor.
  - apply rclo5_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. apply gpaco5_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply gpaco5_gupaco. apply gf_mon.
        eapply gupaco5_mon_gen; intros; [apply PR|apply gf_mon|apply PR0| |apply PR0].
        apply rclo5_clo_base, PR0.
Qed.

Lemma compat5_wcompat clo
      (CMP: compatible5 clo):
  wcompatible5 clo.
Proof.
  econstructor. apply CMP.
  intros. apply CMP in PR.
  eapply gf_mon. apply PR.
  intros. apply gpaco5_clo, PR0. 
Qed.

Lemma wcompat5_compat clo
      (WCMP: wcompatible5 clo) :
  compatible5 (gupaco5 gf clo).
Proof.
  econstructor.
  { red; intros. eapply gpaco5_mon. apply IN. apply LE. apply LE. }

  intros. apply gpaco5_unfold in PR; [|apply gf_mon].
  induction PR.
  - destruct IN; cycle 1.
    + eapply gf_mon. apply H.
      intros. apply gpaco5_base, PR.
    + eapply gf_mon. apply H.
      intros. apply gpaco5_gupaco. apply gf_mon.
      eapply gupaco5_mon. apply PR.
      intros. apply gpaco5_step. apply gf_mon.
      eapply gf_mon. destruct PR0 as [X|X]; apply X.
      intros. apply gpaco5_base, PR1.
  - eapply gf_mon, gpaco5_gupaco, gf_mon.
    apply WCMP. eapply WCMP. apply IN.
    intros. apply H, PR.
Qed.

Lemma wcompat5_union clo1 clo2
      (WCMP1: wcompatible5 clo1)
      (WCMP2: wcompatible5 clo2):
  wcompatible5 (clo1 \6/ clo2).
Proof.
  econstructor.
  - apply monotone5_union. apply WCMP1. apply WCMP2.
  - intros. destruct PR.
    + apply WCMP1 in H. eapply gf_mon. apply H.
      intros. eapply gupaco5_mon_gen. apply PR. apply gf_mon. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco5_mon_gen. apply PR. apply gf_mon.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
Qed.

End Compatibility.

Section Soundness.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone5 gf.

Lemma gpaco5_compat_init clo
      (CMP: compatible5 gf clo):
  gpaco5 gf clo bot5 bot5 <5= paco5 gf bot5.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo5_rclo, PR]. 
  apply compat5_compat with (gf:=gf). apply rclo5_compat. apply gf_mon. apply CMP.
  eapply rclo5_mon. apply IN.
  intros. destruct PR; [|contradiction]. _punfold H; [..|apply gpaco5_def_mon, gf_mon].
  eapply gpaco5_def_mon. apply gf_mon. apply H.
  intros. destruct PR; [|destruct H0; contradiction]. left. apply H0.
Qed.

Lemma gpaco5_init clo
      (WCMP: wcompatible5 gf clo):
  gpaco5 gf clo bot5 bot5 <5= paco5 gf bot5.
Proof.
  intros. eapply gpaco5_compat_init.
  - apply wcompat5_compat, WCMP. apply gf_mon.
  - eapply gpaco5_mon_bot. apply PR. apply gf_mon. intros; apply PR0.
    intros. apply gpaco5_clo, PR0.
Qed.

Lemma gpaco5_unfold_bot clo
      (WCMP: wcompatible5 gf clo):
  gpaco5 gf clo bot5 bot5 <5= gf (gpaco5 gf clo bot5 bot5).
Proof.
  intros. apply gpaco5_init in PR; [|apply WCMP].
  _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. destruct PR0; [|contradiction]. apply gpaco5_final. apply gf_mon. right. apply H.
Qed.

End Soundness.

Section Distributivity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone5 gf.

Lemma gpaco5_dist clo r rg
      (CMP: wcompatible5 gf clo)
      (DIST: forall r1 r2, clo (r1 \5/ r2) <5= (clo r1 \5/ clo r2)):
  gpaco5 gf clo r rg <5= (paco5 gf (rclo5 clo (rg \5/ r)) \5/ rclo5 clo r).
Proof.
  intros. apply gpaco5_unfold in PR; [|apply gf_mon].
  apply rclo5_dist in PR; [|apply CMP|apply DIST].
  destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 H.
  pcofix CIH; intros.
  apply rclo5_wcompat in H0; [|apply gf_mon|apply CMP].
  pstep. eapply gf_mon. apply H0. intros.
  apply gpaco5_unfold in PR; [|apply gf_mon].
  apply rclo5_compose in PR.
  apply rclo5_dist in PR; [|apply CMP|apply DIST].
  destruct PR.
  - right. apply CIH.
    eapply rclo5_mon. apply H. intros.
    eapply gf_mon. apply PR. intros.
    apply gpaco5_gupaco. apply gf_mon.
    apply gpaco5_gen_rclo. apply gf_mon.
    eapply gupaco5_mon. apply PR0. intros.
    destruct PR1; apply H1.
  - assert (REL: @rclo5 clo (rclo5 clo (gf (gupaco5 gf clo ((rg \5/ r) \5/ (rg \5/ r))) \5/ (rg \5/ r))) x0 x1 x2 x3 x4).
    { eapply rclo5_mon. apply H. intros. apply gpaco5_unfold in PR. apply PR. apply gf_mon. }
    apply rclo5_rclo in REL.
    apply rclo5_dist in REL; [|apply CMP|apply DIST].
    right. destruct REL; cycle 1.
    + apply CIH0, H1.
    + apply CIH.
      eapply rclo5_mon. apply H1. intros.
      eapply gf_mon. apply PR. intros.
      eapply gupaco5_mon. apply PR0. intros.
      destruct PR1; apply H2.
Qed.

Lemma gpaco5_dist_reverse clo r rg:
  (paco5 gf (rclo5 clo (rg \5/ r)) \5/ rclo5 clo r) <5= gpaco5 gf clo r rg.
Proof.
  intros. destruct PR; cycle 1.
  - eapply gpaco5_rclo. apply H.
  - econstructor. apply rclo5_base. left.
    revert x0 x1 x2 x3 x4 H. pcofix CIH; intros.
    _punfold H0; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H0. intros.
    destruct PR.
    + apply rclo5_base. right. apply CIH, H.
    + eapply rclo5_mon. apply H. intros.
      right. apply CIH0. apply PR.
Qed.

End Distributivity.

Section Companion.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone5 gf.

Inductive cpn5 (r: rel) x0 x1 x2 x3 x4 : Prop :=
| cpn5_intro
    clo
    (COM: compatible5 gf clo)
    (CLO: clo r x0 x1 x2 x3 x4)
.

Lemma cpn5_mon: monotone5 cpn5.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat5_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn5_greatest: forall clo (COM: compatible5 gf clo), clo <6= cpn5.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn5_compat: compatible5 gf cpn5.
Proof.
  econstructor; [apply cpn5_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat5_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn5_wcompat: wcompatible5 gf cpn5.
Proof. apply compat5_wcompat, cpn5_compat. apply gf_mon. Qed.

Lemma cpn5_gupaco:
  gupaco5 gf cpn5 <6= cpn5.
Proof.
  intros. eapply cpn5_greatest, PR. apply wcompat5_compat. apply gf_mon. apply cpn5_wcompat.
Qed.

Lemma cpn5_cpn r:
  cpn5 (cpn5 r) <5= cpn5 r.
Proof.
  intros. apply cpn5_gupaco, gpaco5_gupaco, gpaco5_clo. apply gf_mon.
  eapply cpn5_mon, gpaco5_clo. apply PR.
Qed.

Lemma cpn5_base r:
  r <5= cpn5 r.
Proof.
  intros. apply cpn5_gupaco. apply gpaco5_base, PR.
Qed.

Lemma cpn5_clo
      r clo (LE: clo <6= cpn5):
  clo (cpn5 r) <5= cpn5 r.
Proof.
  intros. apply cpn5_cpn, LE, PR.
Qed.

Lemma cpn5_step r:
  gf (cpn5 r) <5= cpn5 r.
Proof.
  intros. apply cpn5_gupaco. apply gpaco5_step. apply gf_mon.
  eapply gf_mon, gpaco5_clo. apply PR.
Qed.

Lemma cpn5_uclo uclo
      (MON: monotone5 uclo)
      (WCOM: forall r, uclo (gf r) <5= gf (gupaco5 gf (uclo \6/ cpn5) r)):
  uclo <6= gupaco5 gf cpn5.
Proof.
  intros. apply gpaco5_clo.
  exists (gupaco5 gf (uclo \6/ cpn5)).
  - apply wcompat5_compat. apply gf_mon.
    econstructor.
    + apply monotone5_union. apply MON. apply cpn5_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat5_compat with (gf:=gf) in H; [| apply cpn5_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco5_clo. right. apply PR0.
  - apply gpaco5_clo. left. apply PR.
Qed.

End Companion.

Section Respectful.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone5 gf.

Structure wrespectful5 (clo: rel -> rel) : Prop :=
  wrespect5_intro {
      wrespect5_mon: monotone5 clo;
      wrespect5_respect :
        forall l r
               (LE: l <5= r)
               (GF: l <5= gf r),
        clo l <5= gf (rclo5 clo r);
    }.

Structure prespectful5 (clo: rel -> rel) : Prop :=
  prespect5_intro {
      prespect5_mon: monotone5 clo;
      prespect5_respect :
        forall l r
               (LE: l <5= r)
               (GF: l <5= gf r),
        clo l <5= paco5 gf (r \5/ clo r);
    }.

Structure grespectful5 (clo: rel -> rel) : Prop :=
  grespect5_intro {
      grespect5_mon: monotone5 clo;
      grespect5_respect :
        forall l r
               (LE: l <5= r)
               (GF: l <5= gf r),
        clo l <5= rclo5 (cpn5 gf) (gf (rclo5 (clo \6/ gupaco5 gf (cpn5 gf)) r));
    }.

Definition gf'5 := id /6\ gf.

Definition compatible'5 := compatible5 gf'5.

Lemma wrespect5_compatible'
      clo (RES: wrespectful5 clo):
  compatible'5 (rclo5 clo).
Proof.
  intros. econstructor. apply rclo5_mon.
  intros. destruct RES. split.
  { eapply rclo5_mon. apply PR. intros. apply PR0. }
  induction PR; intros.
  - eapply gf_mon. apply IN.
    intros. apply rclo5_base, PR.
  - eapply gf_mon.
    + eapply wrespect5_respect0; [|apply H|apply IN].
      intros. eapply rclo5_mon; intros; [apply LE, PR|apply PR0].
    + intros. apply rclo5_rclo, PR.
Qed.

Lemma prespect5_compatible'
      clo (RES: prespectful5 clo):
  compatible'5 (fun r => upaco5 gf (r \5/ clo r)).
Proof.
  econstructor.
  { red; intros. eapply upaco5_mon. apply IN.
    intros. destruct PR.
    - left. apply LE, H.
    - right. eapply RES. apply H. intros. apply LE, PR. }

  intros r.
  assert (LEM: (gf'5 r \5/ clo (gf'5 r)) <5= (r \5/ clo r)).
  { intros. destruct PR.
    - left. apply H.
    - right. eapply RES. apply H. intros. apply PR.
  }

  intros. destruct PR.
  - split.
    + left. eapply paco5_mon. apply H. apply LEM.
    + apply paco5_unfold; [apply gf_mon|].
      eapply paco5_mon. apply H. apply LEM.
  - split.
    + right. apply LEM. apply H.
    + destruct H.
      * eapply gf_mon. apply H. intros. right. left. apply PR.
      * apply paco5_unfold; [apply gf_mon|].
        eapply RES, H; intros; apply PR.
Qed.

Lemma grespect5_compatible'
      clo (RES: grespectful5 clo):
  compatible'5 (rclo5 (clo \6/ cpn5 gf)).
Proof.
  apply wrespect5_compatible'.
  econstructor.
  { red; intros. destruct IN.
    - left. eapply RES; [apply H|]. apply LE.
    - right. eapply cpn5_mon; [apply H|]. apply LE. }
  intros. destruct PR.
  - eapply RES.(grespect5_respect) in H; [|apply LE|apply GF].
    apply (@compat5_compat gf (rclo5 (cpn5 gf))) in H.
    2: { apply rclo5_compat; [apply gf_mon|]. apply cpn5_compat. apply gf_mon. }
    eapply gf_mon; [apply H|].
    intros. apply rclo5_clo. right.
    exists (rclo5 (cpn5 gf)).
    { apply rclo5_compat; [apply gf_mon|]. apply cpn5_compat. apply gf_mon. }
    eapply rclo5_mon; [eapply PR|].
    intros. eapply rclo5_mon_gen; [eapply PR0|..].
    + intros. destruct PR1.
      * left. apply H0.
      * right. apply cpn5_gupaco; [apply gf_mon|apply H0].
    + intros. apply PR1.
  - eapply gf_mon.
    + apply (@compat5_compat gf (rclo5 (cpn5 gf))).
      { apply rclo5_compat; [apply gf_mon|]. apply cpn5_compat. apply gf_mon. }
      eapply rclo5_clo_base. eapply cpn5_mon; [apply H|apply GF].
    + intros. eapply rclo5_mon_gen; [eapply PR|..].
      * intros. right. apply PR0.
      * intros. apply PR0.
Qed.

Lemma compat5_compatible'
      clo (COM: compatible5 gf clo):
  compatible'5 clo.
Proof.
  destruct COM. econstructor; [apply compat5_mon0|].
  intros. split.
  - eapply compat5_mon0; intros; [apply PR| apply PR0].
  - apply compat5_compat0.
    eapply compat5_mon0; intros; [apply PR| apply PR0].
Qed.

Lemma compatible'5_companion
      clo (RES: compatible'5 clo):
  clo <6= cpn5 gf.
Proof.
  assert (MON: monotone5 gf'5).
  { econstructor. apply LE, IN.
    eapply gf_mon, LE. apply IN.
  }
  assert (CPN: clo <6= cpn5 gf'5).
  { intros. econstructor. apply RES. apply PR.
  }
  intros. apply CPN in PR.
  econstructor; [|apply PR].
  econstructor; [apply cpn5_mon|]; intros.
  assert (PR1: cpn5 gf'5 (gf r) <5= cpn5 gf'5 (gf'5 (cpn5 gf r))).
  { intros. eapply cpn5_mon. apply PR1.
    intros. assert (TMP: gf (cpn5 gf r) <5= (cpn5 gf r /5\ gf (cpn5 gf r))).
    { split; [apply cpn5_step; [apply gf_mon|]|]; assumption. }
    apply TMP.
    eapply gf_mon. apply PR2. intros. apply cpn5_base; assumption.
  }
  apply PR1 in PR0. clear PR1. 
  eapply compat5_compat with (gf:=gf'5) in PR0; [|apply cpn5_compat, MON].
  eapply gf_mon; [apply PR0|].
  intros. eapply cpn5_cpn; [apply MON|].
  eapply cpn5_mon; [apply PR1|].
  intros. econstructor; [|apply PR2].
  apply compat5_compatible', cpn5_compat, gf_mon.
Qed.

Lemma wrespect5_companion
      clo (RES: wrespectful5 clo):
  clo <6= cpn5 gf.
Proof.
  intros. eapply wrespect5_compatible' in RES.
  eapply (@compatible'5_companion (rclo5 clo)) in RES; [apply RES|].
  eapply rclo5_clo_base, PR.
Qed.

Lemma prespect5_companion
      clo (RES: prespectful5 clo):
  clo <6= cpn5 gf.
Proof.
  intros. eapply compatible'5_companion. apply prespect5_compatible'. apply RES.
  right. right. apply PR.
Qed.

Lemma grespect5_companion
      clo (RES: grespectful5 clo):
  clo <6= cpn5 gf.
Proof.
  intros. eapply grespect5_compatible' in RES.
  eapply (@compatible'5_companion (rclo5 (clo \6/ cpn5 gf))); [apply RES|].
  apply rclo5_clo_base. left. apply PR.
Qed.

Lemma wrespect5_uclo
      clo (RES: wrespectful5 clo):
  clo <6= gupaco5 gf (cpn5 gf).
Proof.
  intros. eapply gpaco5_clo, wrespect5_companion, PR. apply RES.
Qed.

Lemma prespect5_uclo
      clo (RES: prespectful5 clo):
  clo <6= gupaco5 gf (cpn5 gf).
Proof.
  intros. eapply gpaco5_clo, prespect5_companion, PR. apply RES.
Qed.

Lemma grespect5_uclo
      clo (RES: grespectful5 clo):
  clo <6= gupaco5 gf (cpn5 gf).
Proof.
  intros. eapply gpaco5_clo, grespect5_companion, PR. apply RES.
Qed.

End Respectful.

End GeneralizedPaco5.

Hint Resolve gpaco5_def_mon : paco.
Hint Unfold gupaco5 : paco.
Hint Resolve gpaco5_base : paco.
Hint Resolve gpaco5_step : paco.
Hint Resolve gpaco5_final : paco.
Hint Resolve rclo5_base : paco.
Hint Constructors gpaco5 : paco.
Hint Resolve wrespect5_uclo : paco.
Hint Resolve prespect5_uclo : paco.
