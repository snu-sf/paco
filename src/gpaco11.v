Require Export Program.Basics. Open Scope program_scope.
Require Import paco11 pacotac.
Set Implicit Arguments.

Section GeneralizedPaco11.

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

Local Notation rel := (rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10).

Lemma monotone11_compose (clo1 clo2: rel -> rel)
      (MON1: monotone11 clo1)
      (MON2: monotone11 clo2):
  monotone11 (compose clo1 clo2).
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone11_union (clo1 clo2: rel -> rel)
      (MON1: monotone11 clo1)
      (MON2: monotone11 clo2):
  monotone11 (clo1 \12/ clo2).
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

Section RClo.

Inductive rclo11 (clo: rel->rel) (r: rel): rel :=
| rclo11_base
    x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    (IN: r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10):
    @rclo11 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
| rclo11_clo'
    r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    (LE: r' <11= rclo11 clo r)
    (IN: clo r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10):
    @rclo11 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
.           

Lemma rclo11_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
      (IN: @rclo11 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (LEclo: clo <12= clo')
      (LEr: r <11= r') :
  @rclo11 clo' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo11_mon clo:
  monotone11 (rclo11 clo).
Proof.
  repeat intro. eapply rclo11_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo11_clo clo r:
  clo (rclo11 clo r) <11= rclo11 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo11_rclo clo r:
  rclo11 clo (rclo11 clo r) <11= rclo11 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo11_compose clo r:
  rclo11 (rclo11 clo) r <11= rclo11 clo r.
Proof.
  intros. induction PR.
  - apply rclo11_base, IN.
  - apply rclo11_rclo.
    eapply rclo11_mon; [apply IN|apply H].
Qed.

End RClo.  

Section Main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone11 gf.

Variant gpaco11 clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Prop :=
| gpaco11_intro (IN: @rclo11 clo (paco11 (compose gf (rclo11 clo)) (rg \11/ r) \11/ r) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
.

Definition gupaco11 clo r := gpaco11 clo r r.

Lemma gpaco11_def_mon clo : monotone11 (compose gf (rclo11 clo)).
Proof.
  eapply monotone11_compose. apply gf_mon. apply rclo11_mon.
Qed.

Hint Resolve gpaco11_def_mon : paco.

Lemma gpaco11_mon clo r r' rg rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
      (IN: @gpaco11 clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (LEr: r <11= r')
      (LErg: rg <11= rg'):
  @gpaco11 clo r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  destruct IN. econstructor.
  eapply rclo11_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco11_mon. apply H.
  intros. destruct PR.
  - left. apply LErg, H0.
  - right. apply LEr, H0.
Qed.

Lemma gupaco11_mon clo r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
      (IN: @gupaco11 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (LEr: r <11= r'):
  @gupaco11 clo r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  eapply gpaco11_mon. apply IN. apply LEr. apply LEr.
Qed.

Lemma gpaco11_base clo r rg: r <11= gpaco11 clo r rg.
Proof.
  econstructor. apply rclo11_base. right. apply PR.
Qed.

Lemma gpaco11_rclo clo r:
  rclo11 clo r <11= gupaco11 clo r.
Proof.
  intros. econstructor.
  eapply rclo11_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco11_clo clo r:
  clo r <11= gupaco11 clo r.
Proof.
  intros. apply gpaco11_rclo. eapply rclo11_clo', PR.
  apply rclo11_base.
Qed.

Lemma gpaco11_step_gen clo r rg:
  gf (gpaco11 clo (rg \11/ r) (rg \11/ r)) <11= gpaco11 clo r rg.
Proof.
  intros. econstructor. apply rclo11_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo11_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco11_mon. apply H. intros. destruct PR0; apply H0.
  - right. apply H.
Qed.

Lemma gpaco11_step clo r rg:
  gf (gpaco11 clo rg rg) <11= gpaco11 clo r rg.
Proof.
  intros. apply gpaco11_step_gen.
  eapply gf_mon. apply PR. intros.
  eapply gpaco11_mon. apply PR0. left; apply PR1. left; apply PR1.
Qed.

Lemma gpaco11_final clo r rg:
  (r \11/ paco11 gf rg) <11= gpaco11 clo r rg.
Proof.
  intros. destruct PR. apply gpaco11_base, H.
  econstructor. apply rclo11_base.
  left. eapply paco11_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo11_base. apply PR0.
  - intros. left. apply PR.
Qed.

Lemma gpaco11_unfold clo r rg:
  gpaco11 clo r rg <11= rclo11 clo (gf (gupaco11 clo (rg \11/ r)) \11/ r).
Proof.
  intros. destruct PR.
  eapply rclo11_mon. apply IN.
  intros. destruct PR; cycle 1. right; apply H.
  left. _punfold H; [|apply gpaco11_def_mon].
  eapply gf_mon. apply H.
  intros. econstructor.
  eapply rclo11_mon. apply PR.
  intros. destruct PR0; cycle 1. right. apply H0.
  left. eapply paco11_mon. apply H0.
  intros. left. apply PR0.
Qed.
  
Lemma gpaco11_cofix clo r rg 
      l (OBG: forall rr (INC: rg <11= rr) (CIH: l <11= rr), l <11= gpaco11 clo r rr):
  l <11= gpaco11 clo r rg.
Proof.
  assert (IN: l <11= gpaco11 clo r (rg \11/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo11_mon. apply IN0.
  clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply gpaco11_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo11_rclo. eapply rclo11_mon. apply PR.
  intros. destruct PR0.
  - apply rclo11_base. right. apply CIH. apply H.
  - destruct H; [destruct H|].
    + apply rclo11_base. right. apply CIH0. left. apply H.
    + apply IN in H. destruct H.
      eapply rclo11_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. right. apply H.
    + apply rclo11_base. right. apply CIH0. right. apply H.
Qed.

Lemma gpaco11_gupaco clo r rg:
  gupaco11 clo (gpaco11 clo r rg) <11= gpaco11 clo r rg.
Proof.
  eapply gpaco11_cofix.
  intros. destruct PR. econstructor.
  apply rclo11_rclo. eapply rclo11_mon. apply IN.
  intros. destruct PR.
  - apply rclo11_base. left.
    eapply paco11_mon. apply H.
    intros. left; apply CIH.
    econstructor. apply rclo11_base. right.
    destruct PR; apply H0.
  - destruct H. eapply rclo11_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco11_mon. apply H.
    intros. destruct PR.
    + left. apply INC. apply H0.
    + right. apply H0.
Qed.

Lemma gpaco11_uclo uclo clo r rg 
      (LEclo: uclo <12= gupaco11 clo) :
  uclo (gpaco11 clo r rg) <11= gpaco11 clo r rg.
Proof.
  intros. apply gpaco11_gupaco. apply LEclo, PR.
Qed.

Lemma gpaco11_weaken  clo r rg:
  gpaco11 (gupaco11 clo) r rg <11= gpaco11 clo r rg.
Proof.
  intros. apply gpaco11_unfold in PR.
  induction PR.
  - destruct IN; cycle 1. apply gpaco11_base, H.
    apply gpaco11_step_gen. eapply gf_mon. apply H.
    clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 H.
    eapply gpaco11_cofix. intros.
    apply gpaco11_unfold in PR.
    induction PR.
    + destruct IN; cycle 1. apply gpaco11_base, H.
      apply gpaco11_step. eapply gf_mon. apply H.
      intros. apply gpaco11_base. apply CIH.
      eapply gupaco11_mon. apply PR.
      intros. destruct PR0; apply H0.
    + apply gpaco11_gupaco.
      eapply gupaco11_mon. apply IN. apply H.
  - apply gpaco11_gupaco.
    eapply gupaco11_mon. apply IN. apply H.
Qed.

End Main.

Hint Resolve gpaco11_def_mon : paco.

Section GeneralMonotonicity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone11 gf.
  
Lemma gpaco11_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r r' rg rg'
      (IN: @gpaco11 gf clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (LEgf: gf <12= gf')
      (LEclo: clo <12= clo')
      (LEr: r <11= r')
      (LErg: rg <11= rg') :
  @gpaco11 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  eapply gpaco11_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo11_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco11_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply gf_mon. apply PR.
    intros. eapply rclo11_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma gpaco11_mon_bot (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r' rg'
      (IN: @gpaco11 gf clo bot11 bot11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (LEgf: gf <12= gf')
      (LEclo: clo <12= clo'):
  @gpaco11 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  eapply gpaco11_mon_gen. apply IN. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco11_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r r'
      (IN: @gupaco11 gf clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (LEgf: gf <12= gf')
      (LEclo: clo <12= clo')
      (LEr: r <11= r'):
  @gupaco11 gf' clo' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  eapply gpaco11_mon_gen. apply IN. apply LEgf. apply LEclo. apply LEr. apply LEr.
Qed.

End GeneralMonotonicity.

Section Compatibility.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone11 gf.

Structure compatible11 (clo: rel -> rel) : Prop :=
  compat11_intro {
      compat11_mon: monotone11 clo;
      compat11_compat : forall r,
          clo (gf r) <11= gf (clo r);
    }.

Structure wcompatible11 clo : Prop :=
  wcompat11_intro {
      wcompat11_mon: monotone11 clo;
      wcompat11_wcompat : forall r,
          clo (gf r) <11= gf (gupaco11 gf clo r);
    }.

Inductive cpn11 (r: rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Prop :=
| cpn11_intro
    clo
    (COM: compatible11 clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
.

Lemma rclo11_compat clo
      (COM: compatible11 clo):
  compatible11 (rclo11 clo).
Proof.
  econstructor.
  - apply rclo11_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo11_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo11_clo. apply PR.
Qed.

Lemma compat11_wcompat clo
      (CMP: compatible11 clo):
  wcompatible11 clo.
Proof.
  econstructor. apply CMP.
  intros. apply CMP in PR.
  eapply gf_mon. apply PR.
  intros. apply gpaco11_clo, PR0. 
Qed.

Lemma wcompat11_compat clo
      (WCMP: wcompatible11 clo) :
  compatible11 (gupaco11 gf clo).
Proof.
  econstructor.
  { red; intros. eapply gpaco11_mon. apply IN. apply LE. apply LE. }

  intros. apply gpaco11_unfold in PR; [|apply gf_mon].
  induction PR.
  - destruct IN; cycle 1.
    + eapply gf_mon. apply H.
      intros. apply gpaco11_base, PR.
    + eapply gf_mon. apply H.
      intros. apply gpaco11_gupaco. apply gf_mon.
      eapply gupaco11_mon. apply PR.
      intros. apply gpaco11_step. apply gf_mon.
      eapply gf_mon. destruct PR0 as [X|X]; apply X.
      intros. apply gpaco11_base, PR1.
  - eapply gf_mon, gpaco11_gupaco, gf_mon.
    apply WCMP. eapply WCMP. apply IN.
    intros. apply H, PR.
Qed.

Lemma wcompat11_union clo1 clo2
      (WCMP1: wcompatible11 clo1)
      (WCMP2: wcompatible11 clo2):
  wcompatible11 (clo1 \12/ clo2).
Proof.
  econstructor.
  - apply monotone11_union. apply WCMP1. apply WCMP2.
  - intros. destruct PR.
    + apply WCMP1 in H. eapply gf_mon. apply H.
      intros. eapply gupaco11_mon_gen. apply gf_mon. apply PR. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco11_mon_gen. apply gf_mon. apply PR.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
Qed.

Lemma cpn11_mon: monotone11 cpn11.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat11_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn11_greatest: forall clo (COM: compatible11 clo), clo <12= cpn11.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn11_compat: compatible11 cpn11.
Proof.
  econstructor; [apply cpn11_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat11_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn11_wcompat: wcompatible11 cpn11.
Proof. apply compat11_wcompat, cpn11_compat. Qed.

Lemma cpn11_uclo uclo
      (MON: monotone11 uclo)
      (WCOM: forall r, uclo (gf r) <11= gf (gupaco11 gf (uclo \12/ cpn11) r)):
  uclo <12= gupaco11 gf cpn11.
Proof.
  intros. apply gpaco11_clo.
  exists (gupaco11 gf (uclo \12/ cpn11)).
  - apply wcompat11_compat.
    econstructor.
    + apply monotone11_union. apply MON. apply cpn11_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat11_compat in H; [| apply cpn11_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco11_clo. right. apply PR0.
  - apply gpaco11_clo. left. apply PR.
Qed.

End Compatibility.

Section Soundness.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone11 gf.

Lemma gpaco11_compat_init clo
      (CMP: compatible11 gf clo):
  gpaco11 gf clo bot11 bot11 <11= paco11 gf bot11.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo11_rclo, PR]. 
  apply compat11_compat with (gf:=gf). apply rclo11_compat. apply gf_mon. apply CMP.
  eapply rclo11_mon. apply IN.
  intros. destruct PR; [|contradiction]. _punfold H; [..|apply gpaco11_def_mon, gf_mon].
  eapply gpaco11_def_mon. apply gf_mon. apply H.
  intros. destruct PR; [|destruct H0; contradiction]. left. apply H0.
Qed.

Lemma gpaco11_init clo
      (WCMP: wcompatible11 gf clo):
  gpaco11 gf clo bot11 bot11 <11= paco11 gf bot11.
Proof.
  intros. eapply gpaco11_compat_init.
  - apply wcompat11_compat, WCMP. apply gf_mon.
  - eapply gpaco11_mon_bot. apply gf_mon. apply PR. intros; apply PR0.
    intros. apply gpaco11_clo, PR0.
Qed.

Lemma gpaco11_unfold_bot clo
      (WCMP: wcompatible11 gf clo):
  gpaco11 gf clo bot11 bot11 <11= gf (gpaco11 gf clo bot11 bot11).
Proof.
  intros. apply gpaco11_init in PR; [|apply WCMP].
  _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. destruct PR0; [|contradiction]. apply gpaco11_final. apply gf_mon. right. apply H.
Qed.

End Soundness.

End GeneralizedPaco11.

Hint Resolve gpaco11_def_mon : paco.
Hint Resolve gpaco11_base : paco.
Hint Resolve gpaco11_step : paco.
Hint Resolve gpaco11_final : paco.
