Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco9 pacotac.
Set Implicit Arguments.

Section GeneralizedPaco9.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.

Local Notation rel := (rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8).

Section RClo.

Inductive rclo9 (clo: rel->rel) (r: rel): rel :=
| rclo9_base
    x0 x1 x2 x3 x4 x5 x6 x7 x8
    (IN: r x0 x1 x2 x3 x4 x5 x6 x7 x8):
    @rclo9 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8
| rclo9_clo'
    r' x0 x1 x2 x3 x4 x5 x6 x7 x8
    (LE: r' <9= rclo9 clo r)
    (IN: clo r' x0 x1 x2 x3 x4 x5 x6 x7 x8):
    @rclo9 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8
.           

Lemma rclo9_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5 x6 x7 x8
      (IN: @rclo9 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8)
      (LEclo: clo <10= clo')
      (LEr: r <9= r') :
  @rclo9 clo' r' x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo9_mon clo:
  monotone9 (rclo9 clo).
Proof.
  repeat intro. eapply rclo9_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo9_clo clo r:
  clo (rclo9 clo r) <9= rclo9 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo9_clo_base clo r:
  clo r <9= rclo9 clo r.
Proof.
  intros. eapply rclo9_clo', PR.
  intros. apply rclo9_base, PR0.
Qed.

Lemma rclo9_rclo clo r:
  rclo9 clo (rclo9 clo r) <9= rclo9 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo9_compose clo r:
  rclo9 (rclo9 clo) r <9= rclo9 clo r.
Proof.
  intros. induction PR.
  - apply rclo9_base, IN.
  - apply rclo9_rclo.
    eapply rclo9_mon; [apply IN|apply H].
Qed.

End RClo.  

Section Main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone9 gf.

Variant gpaco9 clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 : Prop :=
| gpaco9_intro (IN: @rclo9 clo (paco9 (compose gf (rclo9 clo)) (rg \9/ r) \9/ r) x0 x1 x2 x3 x4 x5 x6 x7 x8)
.

Definition gupaco9 clo r := gpaco9 clo r r.

Lemma gpaco9_def_mon clo : monotone9 (compose gf (rclo9 clo)).
Proof.
  eapply monotone9_compose. apply gf_mon. apply rclo9_mon.
Qed.

Hint Resolve gpaco9_def_mon : paco.

Lemma gpaco9_mon clo r r' rg rg' x0 x1 x2 x3 x4 x5 x6 x7 x8
      (IN: @gpaco9 clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8)
      (LEr: r <9= r')
      (LErg: rg <9= rg'):
  @gpaco9 clo r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  destruct IN. econstructor.
  eapply rclo9_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco9_mon. apply H.
  intros. destruct PR.
  - left. apply LErg, H0.
  - right. apply LEr, H0.
Qed.

Lemma gupaco9_mon clo r r' x0 x1 x2 x3 x4 x5 x6 x7 x8
      (IN: @gupaco9 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8)
      (LEr: r <9= r'):
  @gupaco9 clo r' x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  eapply gpaco9_mon. apply IN. apply LEr. apply LEr.
Qed.

Lemma gpaco9_base clo r rg: r <9= gpaco9 clo r rg.
Proof.
  econstructor. apply rclo9_base. right. apply PR.
Qed.

Lemma gpaco9_gen_guard  clo r rg:
  gpaco9 clo r (rg \9/ r) <9= gpaco9 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  eapply rclo9_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco9_mon_gen; intros. apply H. apply PR.
  destruct PR. apply H0. right. apply H0.
Qed.

Lemma gpaco9_rclo clo r rg:
  rclo9 clo r <9= gpaco9 clo r rg.
Proof.
  intros. econstructor.
  eapply rclo9_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco9_clo clo r rg:
  clo r <9= gpaco9 clo r rg.
Proof.
  intros. apply gpaco9_rclo. eapply rclo9_clo_base, PR.
Qed.

Lemma gpaco9_gen_rclo clo r rg:
  gpaco9 (rclo9 clo) r rg <9= gpaco9 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  apply rclo9_compose.
  eapply rclo9_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco9_mon_gen; intros; [apply H| |apply PR].
  eapply gf_mon, rclo9_compose. apply PR.
Qed.

Lemma gpaco9_step_gen clo r rg:
  gf (gpaco9 clo (rg \9/ r) (rg \9/ r)) <9= gpaco9 clo r rg.
Proof.
  intros. econstructor. apply rclo9_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo9_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco9_mon. apply H. intros. destruct PR0; apply H0.
  - right. apply H.
Qed.

Lemma gpaco9_step clo r rg:
  gf (gpaco9 clo rg rg) <9= gpaco9 clo r rg.
Proof.
  intros. apply gpaco9_step_gen.
  eapply gf_mon. apply PR. intros.
  eapply gpaco9_mon. apply PR0. left; apply PR1. left; apply PR1.
Qed.

Lemma gpaco9_final clo r rg:
  (r \9/ paco9 gf rg) <9= gpaco9 clo r rg.
Proof.
  intros. destruct PR. apply gpaco9_base, H.
  econstructor. apply rclo9_base.
  left. eapply paco9_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo9_base. apply PR0.
  - intros. left. apply PR.
Qed.

Lemma gpaco9_unfold clo r rg:
  gpaco9 clo r rg <9= rclo9 clo (gf (gupaco9 clo (rg \9/ r)) \9/ r).
Proof.
  intros. destruct PR.
  eapply rclo9_mon. apply IN.
  intros. destruct PR; cycle 1. right; apply H.
  left. _punfold H; [|apply gpaco9_def_mon].
  eapply gf_mon. apply H.
  intros. econstructor.
  eapply rclo9_mon. apply PR.
  intros. destruct PR0; cycle 1. right. apply H0.
  left. eapply paco9_mon. apply H0.
  intros. left. apply PR0.
Qed.
  
Lemma gpaco9_cofix clo r rg 
      l (OBG: forall rr (INC: rg <9= rr) (CIH: l <9= rr), l <9= gpaco9 clo r rr):
  l <9= gpaco9 clo r rg.
Proof.
  assert (IN: l <9= gpaco9 clo r (rg \9/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo9_mon. apply IN0.
  clear x0 x1 x2 x3 x4 x5 x6 x7 x8 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply gpaco9_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo9_rclo. eapply rclo9_mon. apply PR.
  intros. destruct PR0.
  - apply rclo9_base. right. apply CIH. apply H.
  - destruct H; [destruct H|].
    + apply rclo9_base. right. apply CIH0. left. apply H.
    + apply IN in H. destruct H.
      eapply rclo9_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. right. apply H.
    + apply rclo9_base. right. apply CIH0. right. apply H.
Qed.

Lemma gpaco9_gupaco clo r rg:
  gupaco9 clo (gpaco9 clo r rg) <9= gpaco9 clo r rg.
Proof.
  eapply gpaco9_cofix.
  intros. destruct PR. econstructor.
  apply rclo9_rclo. eapply rclo9_mon. apply IN.
  intros. destruct PR.
  - apply rclo9_base. left.
    eapply paco9_mon. apply H.
    intros. left; apply CIH.
    econstructor. apply rclo9_base. right.
    destruct PR; apply H0.
  - destruct H. eapply rclo9_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco9_mon. apply H.
    intros. destruct PR.
    + left. apply INC. apply H0.
    + right. apply H0.
Qed.

Lemma gpaco9_gpaco clo r rg:
  gpaco9 clo (gpaco9 clo r rg) (gupaco9 clo (rg \9/ r)) <9= gpaco9 clo r rg.
Proof.
  intros. apply gpaco9_unfold in PR.
  econstructor. apply rclo9_rclo. eapply rclo9_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 PR. intros.
  destruct PR; [|destruct H; apply IN].
  apply rclo9_base. left. pstep.
  eapply gf_mon. apply H. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 H. intros.
  cut (@gupaco9 clo (rg \9/ r) x0 x1 x2 x3 x4 x5 x6 x7 x8).
  { intros. destruct H. eapply rclo9_mon. apply IN. intros.
    destruct PR0; [|right; apply H].
    left. eapply paco9_mon. apply H. intros. destruct PR0; apply H0.
  }
  apply gpaco9_gupaco. eapply gupaco9_mon. apply PR. intros.
  destruct PR0; [apply H|].
  eapply gpaco9_mon; [apply H|right|left]; intros; apply PR0.
Qed.

Lemma gpaco9_uclo uclo clo r rg 
      (LEclo: uclo <10= gupaco9 clo) :
  uclo (gpaco9 clo r rg) <9= gpaco9 clo r rg.
Proof.
  intros. apply gpaco9_gupaco. apply LEclo, PR.
Qed.

Lemma gpaco9_weaken  clo r rg:
  gpaco9 (gupaco9 clo) r rg <9= gpaco9 clo r rg.
Proof.
  intros. apply gpaco9_unfold in PR.
  induction PR.
  - destruct IN; cycle 1. apply gpaco9_base, H.
    apply gpaco9_step_gen. eapply gf_mon. apply H.
    clear x0 x1 x2 x3 x4 x5 x6 x7 x8 H.
    eapply gpaco9_cofix. intros.
    apply gpaco9_unfold in PR.
    induction PR.
    + destruct IN; cycle 1. apply gpaco9_base, H.
      apply gpaco9_step. eapply gf_mon. apply H.
      intros. apply gpaco9_base. apply CIH.
      eapply gupaco9_mon. apply PR.
      intros. destruct PR0; apply H0.
    + apply gpaco9_gupaco.
      eapply gupaco9_mon. apply IN. apply H.
  - apply gpaco9_gupaco.
    eapply gupaco9_mon. apply IN. apply H.
Qed.

End Main.

Hint Resolve gpaco9_def_mon : paco.

Section GeneralMonotonicity.

Variable gf: rel -> rel.
  
Lemma gpaco9_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 r r' rg rg'
      (IN: @gpaco9 gf clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8)
      (gf_mon: monotone9 gf)
      (LEgf: gf <10= gf')
      (LEclo: clo <10= clo')
      (LEr: r <9= r')
      (LErg: rg <9= rg') :
  @gpaco9 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  eapply gpaco9_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo9_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco9_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply gf_mon. apply PR.
    intros. eapply rclo9_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma gpaco9_mon_bot (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 r' rg'
      (IN: @gpaco9 gf clo bot9 bot9 x0 x1 x2 x3 x4 x5 x6 x7 x8)
      (gf_mon: monotone9 gf)
      (LEgf: gf <10= gf')
      (LEclo: clo <10= clo'):
  @gpaco9 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  eapply gpaco9_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco9_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 r r'
      (IN: @gupaco9 gf clo r x0 x1 x2 x3 x4 x5 x6 x7 x8)
      (gf_mon: monotone9 gf)
      (LEgf: gf <10= gf')
      (LEclo: clo <10= clo')
      (LEr: r <9= r'):
  @gupaco9 gf' clo' r' x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  eapply gpaco9_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. apply LEr. apply LEr.
Qed.

End GeneralMonotonicity.

Section Compatibility.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone9 gf.

Structure compatible9 (clo: rel -> rel) : Prop :=
  compat9_intro {
      compat9_mon: monotone9 clo;
      compat9_compat : forall r,
          clo (gf r) <9= gf (clo r);
    }.

Structure wcompatible9 clo : Prop :=
  wcompat9_intro {
      wcompat9_mon: monotone9 clo;
      wcompat9_wcompat : forall r,
          clo (gf r) <9= gf (gupaco9 gf clo r);
    }.

Lemma rclo9_dist clo
      (MON: monotone9 clo)
      (DIST: forall r1 r2, clo (r1 \9/ r2) <9= (clo r1 \9/ clo r2)):
  forall r1 r2, rclo9 clo (r1 \9/ r2) <9= (rclo9 clo r1 \9/ rclo9 clo r2).
Proof.
  intros. induction PR.
  + destruct IN; [left|right]; apply rclo9_base, H.
  + assert (REL: clo (rclo9 clo r1 \9/ rclo9 clo r2) x0 x1 x2 x3 x4 x5 x6 x7 x8).
    { eapply MON. apply IN. apply H. }
    apply DIST in REL. destruct REL; [left|right]; apply rclo9_clo, H0.
Qed.

Lemma rclo9_compat clo
      (COM: compatible9 clo):
  compatible9 (rclo9 clo).
Proof.
  econstructor.
  - apply rclo9_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo9_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo9_clo. apply PR.
Qed.

Lemma rclo9_wcompat clo
      (COM: wcompatible9 clo):
  wcompatible9 (rclo9 clo).
Proof.
  econstructor.
  - apply rclo9_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. apply gpaco9_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply gpaco9_gupaco. apply gf_mon.
        eapply gupaco9_mon_gen; intros; [apply PR|apply gf_mon|apply PR0| |apply PR0].
        apply rclo9_clo_base, PR0.
Qed.

Lemma compat9_wcompat clo
      (CMP: compatible9 clo):
  wcompatible9 clo.
Proof.
  econstructor. apply CMP.
  intros. apply CMP in PR.
  eapply gf_mon. apply PR.
  intros. apply gpaco9_clo, PR0. 
Qed.

Lemma wcompat9_compat clo
      (WCMP: wcompatible9 clo) :
  compatible9 (gupaco9 gf clo).
Proof.
  econstructor.
  { red; intros. eapply gpaco9_mon. apply IN. apply LE. apply LE. }

  intros. apply gpaco9_unfold in PR; [|apply gf_mon].
  induction PR.
  - destruct IN; cycle 1.
    + eapply gf_mon. apply H.
      intros. apply gpaco9_base, PR.
    + eapply gf_mon. apply H.
      intros. apply gpaco9_gupaco. apply gf_mon.
      eapply gupaco9_mon. apply PR.
      intros. apply gpaco9_step. apply gf_mon.
      eapply gf_mon. destruct PR0 as [X|X]; apply X.
      intros. apply gpaco9_base, PR1.
  - eapply gf_mon, gpaco9_gupaco, gf_mon.
    apply WCMP. eapply WCMP. apply IN.
    intros. apply H, PR.
Qed.

Lemma wcompat9_union clo1 clo2
      (WCMP1: wcompatible9 clo1)
      (WCMP2: wcompatible9 clo2):
  wcompatible9 (clo1 \10/ clo2).
Proof.
  econstructor.
  - apply monotone9_union. apply WCMP1. apply WCMP2.
  - intros. destruct PR.
    + apply WCMP1 in H. eapply gf_mon. apply H.
      intros. eapply gupaco9_mon_gen. apply PR. apply gf_mon. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco9_mon_gen. apply PR. apply gf_mon.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
Qed.

End Compatibility.

Section Soundness.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone9 gf.

Lemma gpaco9_compat_init clo
      (CMP: compatible9 gf clo):
  gpaco9 gf clo bot9 bot9 <9= paco9 gf bot9.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo9_rclo, PR]. 
  apply compat9_compat with (gf:=gf). apply rclo9_compat. apply gf_mon. apply CMP.
  eapply rclo9_mon. apply IN.
  intros. destruct PR; [|contradiction]. _punfold H; [..|apply gpaco9_def_mon, gf_mon].
  eapply gpaco9_def_mon. apply gf_mon. apply H.
  intros. destruct PR; [|destruct H0; contradiction]. left. apply H0.
Qed.

Lemma gpaco9_init clo
      (WCMP: wcompatible9 gf clo):
  gpaco9 gf clo bot9 bot9 <9= paco9 gf bot9.
Proof.
  intros. eapply gpaco9_compat_init.
  - apply wcompat9_compat, WCMP. apply gf_mon.
  - eapply gpaco9_mon_bot. apply PR. apply gf_mon. intros; apply PR0.
    intros. apply gpaco9_clo, PR0.
Qed.

Lemma gpaco9_unfold_bot clo
      (WCMP: wcompatible9 gf clo):
  gpaco9 gf clo bot9 bot9 <9= gf (gpaco9 gf clo bot9 bot9).
Proof.
  intros. apply gpaco9_init in PR; [|apply WCMP].
  _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. destruct PR0; [|contradiction]. apply gpaco9_final. apply gf_mon. right. apply H.
Qed.

End Soundness.

Section Distributivity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone9 gf.

Lemma gpaco9_dist clo r rg
      (CMP: wcompatible9 gf clo)
      (DIST: forall r1 r2, clo (r1 \9/ r2) <9= (clo r1 \9/ clo r2)):
  gpaco9 gf clo r rg <9= (paco9 gf (rclo9 clo (rg \9/ r)) \9/ rclo9 clo r).
Proof.
  intros. apply gpaco9_unfold in PR; [|apply gf_mon].
  apply rclo9_dist in PR; [|apply CMP|apply DIST].
  destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 H.
  pcofix CIH; intros.
  apply rclo9_wcompat in H0; [|apply gf_mon|apply CMP].
  pstep. eapply gf_mon. apply H0. intros.
  apply gpaco9_unfold in PR; [|apply gf_mon].
  apply rclo9_compose in PR.
  apply rclo9_dist in PR; [|apply CMP|apply DIST].
  destruct PR.
  - right. apply CIH.
    eapply rclo9_mon. apply H. intros.
    eapply gf_mon. apply PR. intros.
    apply gpaco9_gupaco. apply gf_mon.
    apply gpaco9_gen_rclo. apply gf_mon.
    eapply gupaco9_mon. apply PR0. intros.
    destruct PR1; apply H1.
  - assert (REL: @rclo9 clo (rclo9 clo (gf (gupaco9 gf clo ((rg \9/ r) \9/ (rg \9/ r))) \9/ (rg \9/ r))) x0 x1 x2 x3 x4 x5 x6 x7 x8).
    { eapply rclo9_mon. apply H. intros. apply gpaco9_unfold in PR. apply PR. apply gf_mon. }
    apply rclo9_rclo in REL.
    apply rclo9_dist in REL; [|apply CMP|apply DIST].
    right. destruct REL; cycle 1.
    + apply CIH0, H1.
    + apply CIH.
      eapply rclo9_mon. apply H1. intros.
      eapply gf_mon. apply PR. intros.
      eapply gupaco9_mon. apply PR0. intros.
      destruct PR1; apply H2.
Qed.

Lemma gpaco9_dist_reverse clo r rg:
  (paco9 gf (rclo9 clo (rg \9/ r)) \9/ rclo9 clo r) <9= gpaco9 gf clo r rg.
Proof.
  intros. destruct PR; cycle 1.
  - eapply gpaco9_rclo. apply H.
  - econstructor. apply rclo9_base. left.
    revert x0 x1 x2 x3 x4 x5 x6 x7 x8 H. pcofix CIH; intros.
    _punfold H0; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H0. intros.
    destruct PR.
    + apply rclo9_base. right. apply CIH, H.
    + eapply rclo9_mon. apply H. intros.
      right. apply CIH0. apply PR.
Qed.

End Distributivity.

Section Companion.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone9 gf.

Inductive cpn9 (r: rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 : Prop :=
| cpn9_intro
    clo
    (COM: compatible9 gf clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6 x7 x8)
.

Lemma cpn9_mon: monotone9 cpn9.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat9_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn9_greatest: forall clo (COM: compatible9 gf clo), clo <10= cpn9.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn9_compat: compatible9 gf cpn9.
Proof.
  econstructor; [apply cpn9_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat9_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn9_wcompat: wcompatible9 gf cpn9.
Proof. apply compat9_wcompat, cpn9_compat. apply gf_mon. Qed.

Lemma cpn9_gupaco:
  gupaco9 gf cpn9 <10= cpn9.
Proof.
  intros. eapply cpn9_greatest, PR. apply wcompat9_compat. apply gf_mon. apply cpn9_wcompat.
Qed.

Lemma cpn9_cpn r:
  cpn9 (cpn9 r) <9= cpn9 r.
Proof.
  intros. apply cpn9_gupaco, gpaco9_gupaco, gpaco9_clo. apply gf_mon.
  eapply cpn9_mon, gpaco9_clo. apply PR.
Qed.

Lemma cpn9_base r:
  r <9= cpn9 r.
Proof.
  intros. apply cpn9_gupaco. apply gpaco9_base, PR.
Qed.

Lemma cpn9_clo
      r clo (LE: clo <10= cpn9):
  clo (cpn9 r) <9= cpn9 r.
Proof.
  intros. apply cpn9_cpn, LE, PR.
Qed.

Lemma cpn9_step r:
  gf (cpn9 r) <9= cpn9 r.
Proof.
  intros. apply cpn9_gupaco. apply gpaco9_step. apply gf_mon.
  eapply gf_mon, gpaco9_clo. apply PR.
Qed.

Lemma cpn9_uclo uclo
      (MON: monotone9 uclo)
      (WCOM: forall r, uclo (gf r) <9= gf (gupaco9 gf (uclo \10/ cpn9) r)):
  uclo <10= gupaco9 gf cpn9.
Proof.
  intros. apply gpaco9_clo.
  exists (gupaco9 gf (uclo \10/ cpn9)).
  - apply wcompat9_compat. apply gf_mon.
    econstructor.
    + apply monotone9_union. apply MON. apply cpn9_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat9_compat with (gf:=gf) in H; [| apply cpn9_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco9_clo. right. apply PR0.
  - apply gpaco9_clo. left. apply PR.
Qed.

End Companion.

Section Respectful.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone9 gf.

Structure wrespectful9 (clo: rel -> rel) : Prop :=
  wrespect9_intro {
      wrespect9_mon: monotone9 clo;
      wrespect9_respect :
        forall l r
               (LE: l <9= r)
               (GF: l <9= gf r),
        clo l <9= gf (rclo9 clo r);
    }.

Structure prespectful9 (clo: rel -> rel) : Prop :=
  prespect9_intro {
      prespect9_mon: monotone9 clo;
      prespect9_respect :
        forall l r
               (LE: l <9= r)
               (GF: l <9= gf r),
        clo l <9= paco9 gf (r \9/ clo r);
    }.

Structure grespectful9 (clo: rel -> rel) : Prop :=
  grespect9_intro {
      grespect9_mon: monotone9 clo;
      grespect9_respect :
        forall l r
               (LE: l <9= r)
               (GF: l <9= gf r),
        clo l <9= rclo9 (cpn9 gf) (gf (rclo9 (clo \10/ gupaco9 gf (cpn9 gf)) r));
    }.

Definition gf'9 := id /10\ gf.

Definition compatible'9 := compatible9 gf'9.

Lemma wrespect9_compatible'
      clo (RES: wrespectful9 clo):
  compatible'9 (rclo9 clo).
Proof.
  intros. econstructor. apply rclo9_mon.
  intros. destruct RES. split.
  { eapply rclo9_mon. apply PR. intros. apply PR0. }
  induction PR; intros.
  - eapply gf_mon. apply IN.
    intros. apply rclo9_base, PR.
  - eapply gf_mon.
    + eapply wrespect9_respect0; [|apply H|apply IN].
      intros. eapply rclo9_mon; intros; [apply LE, PR|apply PR0].
    + intros. apply rclo9_rclo, PR.
Qed.

Lemma prespect9_compatible'
      clo (RES: prespectful9 clo):
  compatible'9 (fun r => upaco9 gf (r \9/ clo r)).
Proof.
  econstructor.
  { red; intros. eapply upaco9_mon. apply IN.
    intros. destruct PR.
    - left. apply LE, H.
    - right. eapply RES. apply H. intros. apply LE, PR. }

  intros r.
  assert (LEM: (gf'9 r \9/ clo (gf'9 r)) <9= (r \9/ clo r)).
  { intros. destruct PR.
    - left. apply H.
    - right. eapply RES. apply H. intros. apply PR.
  }

  intros. destruct PR.
  - split.
    + left. eapply paco9_mon. apply H. apply LEM.
    + apply paco9_unfold; [apply gf_mon|].
      eapply paco9_mon. apply H. apply LEM.
  - split.
    + right. apply LEM. apply H.
    + destruct H.
      * eapply gf_mon. apply H. intros. right. left. apply PR.
      * apply paco9_unfold; [apply gf_mon|].
        eapply RES, H; intros; apply PR.
Qed.

Lemma grespect9_compatible'
      clo (RES: grespectful9 clo):
  compatible'9 (rclo9 (clo \10/ cpn9 gf)).
Proof.
  apply wrespect9_compatible'.
  econstructor.
  { red; intros. destruct IN.
    - left. eapply RES; [apply H|]. apply LE.
    - right. eapply cpn9_mon; [apply H|]. apply LE. }
  intros. destruct PR.
  - eapply RES.(grespect9_respect) in H; [|apply LE|apply GF].
    apply (@compat9_compat gf (rclo9 (cpn9 gf))) in H.
    2: { apply rclo9_compat; [apply gf_mon|]. apply cpn9_compat. apply gf_mon. }
    eapply gf_mon; [apply H|].
    intros. apply rclo9_clo. right.
    exists (rclo9 (cpn9 gf)).
    { apply rclo9_compat; [apply gf_mon|]. apply cpn9_compat. apply gf_mon. }
    eapply rclo9_mon; [eapply PR|].
    intros. eapply rclo9_mon_gen; [eapply PR0|..].
    + intros. destruct PR1.
      * left. apply H0.
      * right. apply cpn9_gupaco; [apply gf_mon|apply H0].
    + intros. apply PR1.
  - eapply gf_mon.
    + apply (@compat9_compat gf (rclo9 (cpn9 gf))).
      { apply rclo9_compat; [apply gf_mon|]. apply cpn9_compat. apply gf_mon. }
      eapply rclo9_clo_base. eapply cpn9_mon; [apply H|apply GF].
    + intros. eapply rclo9_mon_gen; [eapply PR|..].
      * intros. right. apply PR0.
      * intros. apply PR0.
Qed.

Lemma compat9_compatible'
      clo (COM: compatible9 gf clo):
  compatible'9 clo.
Proof.
  destruct COM. econstructor; [apply compat9_mon0|].
  intros. split.
  - eapply compat9_mon0; intros; [apply PR| apply PR0].
  - apply compat9_compat0.
    eapply compat9_mon0; intros; [apply PR| apply PR0].
Qed.

Lemma compatible'9_companion
      clo (RES: compatible'9 clo):
  clo <10= cpn9 gf.
Proof.
  assert (MON: monotone9 gf'9).
  { econstructor. apply LE, IN.
    eapply gf_mon, LE. apply IN.
  }
  assert (CPN: clo <10= cpn9 gf'9).
  { intros. econstructor. apply RES. apply PR.
  }
  intros. apply CPN in PR.
  econstructor; [|apply PR].
  econstructor; [apply cpn9_mon|]; intros.
  assert (PR1: cpn9 gf'9 (gf r) <9= cpn9 gf'9 (gf'9 (cpn9 gf r))).
  { intros. eapply cpn9_mon. apply PR1.
    intros. assert (TMP: gf (cpn9 gf r) <9= (cpn9 gf r /9\ gf (cpn9 gf r))).
    { split; [apply cpn9_step; [apply gf_mon|]|]; assumption. }
    apply TMP.
    eapply gf_mon. apply PR2. intros. apply cpn9_base; assumption.
  }
  apply PR1 in PR0. clear PR1. 
  eapply compat9_compat with (gf:=gf'9) in PR0; [|apply cpn9_compat, MON].
  eapply gf_mon; [apply PR0|].
  intros. eapply cpn9_cpn; [apply MON|].
  eapply cpn9_mon; [apply PR1|].
  intros. econstructor; [|apply PR2].
  apply compat9_compatible', cpn9_compat, gf_mon.
Qed.

Lemma wrespect9_companion
      clo (RES: wrespectful9 clo):
  clo <10= cpn9 gf.
Proof.
  intros. eapply wrespect9_compatible' in RES.
  eapply (@compatible'9_companion (rclo9 clo)) in RES; [apply RES|].
  eapply rclo9_clo_base, PR.
Qed.

Lemma prespect9_companion
      clo (RES: prespectful9 clo):
  clo <10= cpn9 gf.
Proof.
  intros. eapply compatible'9_companion. apply prespect9_compatible'. apply RES.
  right. right. apply PR.
Qed.

Lemma grespect9_companion
      clo (RES: grespectful9 clo):
  clo <10= cpn9 gf.
Proof.
  intros. eapply grespect9_compatible' in RES.
  eapply (@compatible'9_companion (rclo9 (clo \10/ cpn9 gf))); [apply RES|].
  apply rclo9_clo_base. left. apply PR.
Qed.

Lemma wrespect9_uclo
      clo (RES: wrespectful9 clo):
  clo <10= gupaco9 gf (cpn9 gf).
Proof.
  intros. eapply gpaco9_clo, wrespect9_companion, PR. apply RES.
Qed.

Lemma prespect9_uclo
      clo (RES: prespectful9 clo):
  clo <10= gupaco9 gf (cpn9 gf).
Proof.
  intros. eapply gpaco9_clo, prespect9_companion, PR. apply RES.
Qed.

Lemma grespect9_uclo
      clo (RES: grespectful9 clo):
  clo <10= gupaco9 gf (cpn9 gf).
Proof.
  intros. eapply gpaco9_clo, grespect9_companion, PR. apply RES.
Qed.

End Respectful.

End GeneralizedPaco9.

Hint Resolve gpaco9_def_mon : paco.
Hint Unfold gupaco9 : paco.
Hint Resolve gpaco9_base : paco.
Hint Resolve gpaco9_step : paco.
Hint Resolve gpaco9_final : paco.
Hint Resolve rclo9_base : paco.
Hint Constructors gpaco9 : paco.
Hint Resolve wrespect9_uclo : paco.
Hint Resolve prespect9_uclo : paco.
