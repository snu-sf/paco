Require Export Program.Basics. Open Scope program_scope.
Require Import paco8 pacotac.
Set Implicit Arguments.

Section GeneralizedPaco8.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.

Local Notation rel := (rel8 T0 T1 T2 T3 T4 T5 T6 T7).

Lemma monotone8_compose (clo1 clo2: rel -> rel)
      (MON1: monotone8 clo1)
      (MON2: monotone8 clo2):
  monotone8 (compose clo1 clo2).
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone8_union (clo1 clo2: rel -> rel)
      (MON1: monotone8 clo1)
      (MON2: monotone8 clo2):
  monotone8 (clo1 \9/ clo2).
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

Section RClo.

Inductive rclo8 (clo: rel->rel) (r: rel): rel :=
| rclo8_base
    x0 x1 x2 x3 x4 x5 x6 x7
    (IN: r x0 x1 x2 x3 x4 x5 x6 x7):
    @rclo8 clo r x0 x1 x2 x3 x4 x5 x6 x7
| rclo8_clo'
    r' x0 x1 x2 x3 x4 x5 x6 x7
    (LE: r' <8= rclo8 clo r)
    (IN: clo r' x0 x1 x2 x3 x4 x5 x6 x7):
    @rclo8 clo r x0 x1 x2 x3 x4 x5 x6 x7
.           

Lemma rclo8_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5 x6 x7
      (IN: @rclo8 clo r x0 x1 x2 x3 x4 x5 x6 x7)
      (LEclo: clo <9= clo')
      (LEr: r <8= r') :
  @rclo8 clo' r' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo8_mon clo:
  monotone8 (rclo8 clo).
Proof.
  repeat intro. eapply rclo8_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo8_clo clo r:
  clo (rclo8 clo r) <8= rclo8 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo8_rclo clo r:
  rclo8 clo (rclo8 clo r) <8= rclo8 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo8_compose clo r:
  rclo8 (rclo8 clo) r <8= rclo8 clo r.
Proof.
  intros. induction PR.
  - apply rclo8_base, IN.
  - apply rclo8_rclo.
    eapply rclo8_mon; [apply IN|apply H].
Qed.

End RClo.  

Section Main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone8 gf.

Variant gpaco8 clo r rg x0 x1 x2 x3 x4 x5 x6 x7 : Prop :=
| gpaco8_intro (IN: @rclo8 clo (paco8 (compose gf (rclo8 clo)) (rg \8/ r) \8/ r) x0 x1 x2 x3 x4 x5 x6 x7)
.

Definition gupaco8 clo r := gpaco8 clo r r.

Lemma gpaco8_def_mon clo : monotone8 (compose gf (rclo8 clo)).
Proof.
  eapply monotone8_compose. apply gf_mon. apply rclo8_mon.
Qed.

Hint Resolve gpaco8_def_mon : paco.

Lemma gpaco8_mon clo r r' rg rg' x0 x1 x2 x3 x4 x5 x6 x7
      (IN: @gpaco8 clo r rg x0 x1 x2 x3 x4 x5 x6 x7)
      (LEr: r <8= r')
      (LErg: rg <8= rg'):
  @gpaco8 clo r' rg' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  destruct IN. econstructor.
  eapply rclo8_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco8_mon. apply H.
  intros. destruct PR.
  - left. apply LErg, H0.
  - right. apply LEr, H0.
Qed.

Lemma gupaco8_mon clo r r' x0 x1 x2 x3 x4 x5 x6 x7
      (IN: @gupaco8 clo r x0 x1 x2 x3 x4 x5 x6 x7)
      (LEr: r <8= r'):
  @gupaco8 clo r' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply gpaco8_mon. apply IN. apply LEr. apply LEr.
Qed.

Lemma gpaco8_base clo r rg: r <8= gpaco8 clo r rg.
Proof.
  econstructor. apply rclo8_base. right. apply PR.
Qed.

Lemma gpaco8_rclo clo r:
  rclo8 clo r <8= gupaco8 clo r.
Proof.
  intros. econstructor.
  eapply rclo8_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco8_clo clo r:
  clo r <8= gupaco8 clo r.
Proof.
  intros. apply gpaco8_rclo. eapply rclo8_clo', PR.
  apply rclo8_base.
Qed.

Lemma gpaco8_step_gen clo r rg:
  gf (gpaco8 clo (rg \8/ r) (rg \8/ r)) <8= gpaco8 clo r rg.
Proof.
  intros. econstructor. apply rclo8_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo8_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco8_mon. apply H. intros. destruct PR0; apply H0.
  - right. apply H.
Qed.

Lemma gpaco8_step clo r rg:
  gf (gpaco8 clo rg rg) <8= gpaco8 clo r rg.
Proof.
  intros. apply gpaco8_step_gen.
  eapply gf_mon. apply PR. intros.
  eapply gpaco8_mon. apply PR0. left; apply PR1. left; apply PR1.
Qed.

Lemma gpaco8_final clo r rg:
  (r \8/ paco8 gf rg) <8= gpaco8 clo r rg.
Proof.
  intros. destruct PR. apply gpaco8_base, H.
  econstructor. apply rclo8_base.
  left. eapply paco8_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo8_base. apply PR0.
  - intros. left. apply PR.
Qed.

Lemma gpaco8_unfold clo r rg:
  gpaco8 clo r rg <8= rclo8 clo (gf (gupaco8 clo (rg \8/ r)) \8/ r).
Proof.
  intros. destruct PR.
  eapply rclo8_mon. apply IN.
  intros. destruct PR; cycle 1. right; apply H.
  left. _punfold H; [|apply gpaco8_def_mon].
  eapply gf_mon. apply H.
  intros. econstructor.
  eapply rclo8_mon. apply PR.
  intros. destruct PR0; cycle 1. right. apply H0.
  left. eapply paco8_mon. apply H0.
  intros. left. apply PR0.
Qed.
  
Lemma gpaco8_cofix clo r rg 
      l (OBG: forall rr (INC: rg <8= rr) (CIH: l <8= rr), l <8= gpaco8 clo r rr):
  l <8= gpaco8 clo r rg.
Proof.
  assert (IN: l <8= gpaco8 clo r (rg \8/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo8_mon. apply IN0.
  clear x0 x1 x2 x3 x4 x5 x6 x7 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 x7 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply gpaco8_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo8_rclo. eapply rclo8_mon. apply PR.
  intros. destruct PR0.
  - apply rclo8_base. right. apply CIH. apply H.
  - destruct H; [destruct H|].
    + apply rclo8_base. right. apply CIH0. left. apply H.
    + apply IN in H. destruct H.
      eapply rclo8_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. right. apply H.
    + apply rclo8_base. right. apply CIH0. right. apply H.
Qed.

Lemma gpaco8_gupaco clo r rg:
  gupaco8 clo (gpaco8 clo r rg) <8= gpaco8 clo r rg.
Proof.
  eapply gpaco8_cofix.
  intros. destruct PR. econstructor.
  apply rclo8_rclo. eapply rclo8_mon. apply IN.
  intros. destruct PR.
  - apply rclo8_base. left.
    eapply paco8_mon. apply H.
    intros. left; apply CIH.
    econstructor. apply rclo8_base. right.
    destruct PR; apply H0.
  - destruct H. eapply rclo8_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco8_mon. apply H.
    intros. destruct PR.
    + left. apply INC. apply H0.
    + right. apply H0.
Qed.

Lemma gpaco8_uclo uclo clo r rg 
      (LEclo: uclo <9= gupaco8 clo) :
  uclo (gpaco8 clo r rg) <8= gpaco8 clo r rg.
Proof.
  intros. apply gpaco8_gupaco. apply LEclo, PR.
Qed.

Lemma gpaco8_weaken  clo r rg:
  gpaco8 (gupaco8 clo) r rg <8= gpaco8 clo r rg.
Proof.
  intros. apply gpaco8_unfold in PR.
  induction PR.
  - destruct IN; cycle 1. apply gpaco8_base, H.
    apply gpaco8_step_gen. eapply gf_mon. apply H.
    clear x0 x1 x2 x3 x4 x5 x6 x7 H.
    eapply gpaco8_cofix. intros.
    apply gpaco8_unfold in PR.
    induction PR.
    + destruct IN; cycle 1. apply gpaco8_base, H.
      apply gpaco8_step. eapply gf_mon. apply H.
      intros. apply gpaco8_base. apply CIH.
      eapply gupaco8_mon. apply PR.
      intros. destruct PR0; apply H0.
    + apply gpaco8_gupaco.
      eapply gupaco8_mon. apply IN. apply H.
  - apply gpaco8_gupaco.
    eapply gupaco8_mon. apply IN. apply H.
Qed.

End Main.

Hint Resolve gpaco8_def_mon : paco.

Section GeneralMonotonicity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone8 gf.
  
Lemma gpaco8_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 r r' rg rg'
      (IN: @gpaco8 gf clo r rg x0 x1 x2 x3 x4 x5 x6 x7)
      (LEgf: gf <9= gf')
      (LEclo: clo <9= clo')
      (LEr: r <8= r')
      (LErg: rg <8= rg') :
  @gpaco8 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply gpaco8_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo8_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco8_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply gf_mon. apply PR.
    intros. eapply rclo8_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma gpaco8_mon_bot (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 r' rg'
      (IN: @gpaco8 gf clo bot8 bot8 x0 x1 x2 x3 x4 x5 x6 x7)
      (LEgf: gf <9= gf')
      (LEclo: clo <9= clo'):
  @gpaco8 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply gpaco8_mon_gen. apply IN. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco8_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 r r'
      (IN: @gupaco8 gf clo r x0 x1 x2 x3 x4 x5 x6 x7)
      (LEgf: gf <9= gf')
      (LEclo: clo <9= clo')
      (LEr: r <8= r'):
  @gupaco8 gf' clo' r' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply gpaco8_mon_gen. apply IN. apply LEgf. apply LEclo. apply LEr. apply LEr.
Qed.

End GeneralMonotonicity.

Section Compatibility.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone8 gf.

Structure compatible8 (clo: rel -> rel) : Prop :=
  compat8_intro {
      compat8_mon: monotone8 clo;
      compat8_compat : forall r,
          clo (gf r) <8= gf (clo r);
    }.

Structure wcompatible8 clo : Prop :=
  wcompat8_intro {
      wcompat8_mon: monotone8 clo;
      wcompat8_wcompat : forall r,
          clo (gf r) <8= gf (gupaco8 gf clo r);
    }.

Inductive cpn8 (r: rel) x0 x1 x2 x3 x4 x5 x6 x7 : Prop :=
| cpn8_intro
    clo
    (COM: compatible8 clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6 x7)
.

Lemma rclo8_compat clo
      (COM: compatible8 clo):
  compatible8 (rclo8 clo).
Proof.
  econstructor.
  - apply rclo8_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo8_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo8_clo. apply PR.
Qed.

Lemma compat8_wcompat clo
      (CMP: compatible8 clo):
  wcompatible8 clo.
Proof.
  econstructor. apply CMP.
  intros. apply CMP in PR.
  eapply gf_mon. apply PR.
  intros. apply gpaco8_clo, PR0. 
Qed.

Lemma wcompat8_compat clo
      (WCMP: wcompatible8 clo) :
  compatible8 (gupaco8 gf clo).
Proof.
  econstructor.
  { red; intros. eapply gpaco8_mon. apply IN. apply LE. apply LE. }

  intros. apply gpaco8_unfold in PR; [|apply gf_mon].
  induction PR.
  - destruct IN; cycle 1.
    + eapply gf_mon. apply H.
      intros. apply gpaco8_base, PR.
    + eapply gf_mon. apply H.
      intros. apply gpaco8_gupaco. apply gf_mon.
      eapply gupaco8_mon. apply PR.
      intros. apply gpaco8_step. apply gf_mon.
      eapply gf_mon. destruct PR0 as [X|X]; apply X.
      intros. apply gpaco8_base, PR1.
  - eapply gf_mon, gpaco8_gupaco, gf_mon.
    apply WCMP. eapply WCMP. apply IN.
    intros. apply H, PR.
Qed.

Lemma wcompat8_union clo1 clo2
      (WCMP1: wcompatible8 clo1)
      (WCMP2: wcompatible8 clo2):
  wcompatible8 (clo1 \9/ clo2).
Proof.
  econstructor.
  - apply monotone8_union. apply WCMP1. apply WCMP2.
  - intros. destruct PR.
    + apply WCMP1 in H. eapply gf_mon. apply H.
      intros. eapply gupaco8_mon_gen. apply gf_mon. apply PR. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco8_mon_gen. apply gf_mon. apply PR.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
Qed.

Lemma cpn8_mon: monotone8 cpn8.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat8_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn8_greatest: forall clo (COM: compatible8 clo), clo <9= cpn8.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn8_compat: compatible8 cpn8.
Proof.
  econstructor; [apply cpn8_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat8_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn8_wcompat: wcompatible8 cpn8.
Proof. apply compat8_wcompat, cpn8_compat. Qed.

Lemma cpn8_uclo uclo
      (MON: monotone8 uclo)
      (WCOM: forall r, uclo (gf r) <8= gf (gupaco8 gf (uclo \9/ cpn8) r)):
  uclo <9= gupaco8 gf cpn8.
Proof.
  intros. apply gpaco8_clo.
  exists (gupaco8 gf (uclo \9/ cpn8)).
  - apply wcompat8_compat.
    econstructor.
    + apply monotone8_union. apply MON. apply cpn8_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat8_compat in H; [| apply cpn8_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco8_clo. right. apply PR0.
  - apply gpaco8_clo. left. apply PR.
Qed.

End Compatibility.

Section Soundness.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone8 gf.

Lemma gpaco8_compat_init clo
      (CMP: compatible8 gf clo):
  gpaco8 gf clo bot8 bot8 <8= paco8 gf bot8.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 x5 x6 x7 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo8_rclo, PR]. 
  apply compat8_compat with (gf:=gf). apply rclo8_compat. apply gf_mon. apply CMP.
  eapply rclo8_mon. apply IN.
  intros. destruct PR; [|contradiction]. _punfold H; [..|apply gpaco8_def_mon, gf_mon].
  eapply gpaco8_def_mon. apply gf_mon. apply H.
  intros. destruct PR; [|destruct H0; contradiction]. left. apply H0.
Qed.

Lemma gpaco8_init clo
      (WCMP: wcompatible8 gf clo):
  gpaco8 gf clo bot8 bot8 <8= paco8 gf bot8.
Proof.
  intros. eapply gpaco8_compat_init.
  - apply wcompat8_compat, WCMP. apply gf_mon.
  - eapply gpaco8_mon_bot. apply gf_mon. apply PR. intros; apply PR0.
    intros. apply gpaco8_clo, PR0.
Qed.

Lemma gpaco8_unfold_bot clo
      (WCMP: wcompatible8 gf clo):
  gpaco8 gf clo bot8 bot8 <8= gf (gpaco8 gf clo bot8 bot8).
Proof.
  intros. apply gpaco8_init in PR; [|apply WCMP].
  _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. destruct PR0; [|contradiction]. apply gpaco8_final. apply gf_mon. right. apply H.
Qed.

End Soundness.

End GeneralizedPaco8.

Hint Resolve gpaco8_def_mon : paco.
Hint Resolve gpaco8_base : paco.
Hint Resolve gpaco8_step : paco.
Hint Resolve gpaco8_final : paco.
