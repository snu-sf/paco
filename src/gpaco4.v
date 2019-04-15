Require Export Program.Basics. Open Scope program_scope.
Require Import paco4 pacotac.
Set Implicit Arguments.

Section GeneralizedPaco4.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.

Local Notation rel := (rel4 T0 T1 T2 T3).

Lemma monotone4_compose (clo1 clo2: rel -> rel)
      (MON1: monotone4 clo1)
      (MON2: monotone4 clo2):
  monotone4 (compose clo1 clo2).
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone4_union (clo1 clo2: rel -> rel)
      (MON1: monotone4 clo1)
      (MON2: monotone4 clo2):
  monotone4 (clo1 \5/ clo2).
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

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

Hint Resolve gpaco4_def_mon : paco.

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

Lemma gpaco4_rclo clo r:
  rclo4 clo r <4= gupaco4 clo r.
Proof.
  intros. econstructor.
  eapply rclo4_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco4_clo clo r:
  clo r <4= gupaco4 clo r.
Proof.
  intros. apply gpaco4_rclo. eapply rclo4_clo', PR.
  apply rclo4_base.
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

Hint Resolve gpaco4_def_mon : paco.

Section GeneralMonotonicity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone4 gf.
  
Lemma gpaco4_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 r r' rg rg'
      (IN: @gpaco4 gf clo r rg x0 x1 x2 x3)
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
      (LEgf: gf <5= gf')
      (LEclo: clo <5= clo'):
  @gpaco4 gf' clo' r' rg' x0 x1 x2 x3.
Proof.
  eapply gpaco4_mon_gen. apply IN. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco4_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 r r'
      (IN: @gupaco4 gf clo r x0 x1 x2 x3)
      (LEgf: gf <5= gf')
      (LEclo: clo <5= clo')
      (LEr: r <4= r'):
  @gupaco4 gf' clo' r' x0 x1 x2 x3.
Proof.
  eapply gpaco4_mon_gen. apply IN. apply LEgf. apply LEclo. apply LEr. apply LEr.
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

Inductive cpn4 (r: rel) x0 x1 x2 x3 : Prop :=
| cpn4_intro
    clo
    (COM: compatible4 clo)
    (CLO: clo r x0 x1 x2 x3)
.

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
      intros. eapply gupaco4_mon_gen. apply gf_mon. apply PR. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco4_mon_gen. apply gf_mon. apply PR.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
Qed.

Lemma cpn4_mon: monotone4 cpn4.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat4_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn4_greatest: forall clo (COM: compatible4 clo), clo <5= cpn4.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn4_compat: compatible4 cpn4.
Proof.
  econstructor; [apply cpn4_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat4_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn4_wcompat: wcompatible4 cpn4.
Proof. apply compat4_wcompat, cpn4_compat. Qed.

Lemma cpn4_gupaco:
  gupaco4 gf cpn4 <5= cpn4.
Proof.
  intros. eapply cpn4_greatest, PR. apply wcompat4_compat. apply cpn4_wcompat.
Qed.

Lemma cpn4_uclo uclo
      (MON: monotone4 uclo)
      (WCOM: forall r, uclo (gf r) <4= gf (gupaco4 gf (uclo \5/ cpn4) r)):
  uclo <5= gupaco4 gf cpn4.
Proof.
  intros. apply gpaco4_clo.
  exists (gupaco4 gf (uclo \5/ cpn4)).
  - apply wcompat4_compat.
    econstructor.
    + apply monotone4_union. apply MON. apply cpn4_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat4_compat in H; [| apply cpn4_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco4_clo. right. apply PR0.
  - apply gpaco4_clo. left. apply PR.
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
  - eapply gpaco4_mon_bot. apply gf_mon. apply PR. intros; apply PR0.
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

End GeneralizedPaco4.

Hint Resolve gpaco4_def_mon : paco.
Hint Unfold gupaco4 : paco.
Hint Resolve gpaco4_base : paco.
Hint Resolve gpaco4_step : paco.
Hint Resolve gpaco4_final : paco.
