Require Export Program.Basics. Open Scope program_scope.
Require Import paco0 pacotac.
Set Implicit Arguments.

Section GeneralizedPaco0.


Local Notation rel := (rel0).

Section RClo.

Inductive rclo0 (clo: rel->rel) (r: rel): rel :=
| rclo0_base
   
    (IN: r):
    @rclo0 clo r
| rclo0_clo'
    r'
    (LE: r' <0= rclo0 clo r)
    (IN: clo r'):
    @rclo0 clo r
.           

Lemma rclo0_mon_gen clo clo' r r'
      (IN: @rclo0 clo r)
      (LEclo: clo <1= clo')
      (LEr: r <0= r') :
  @rclo0 clo' r'.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo0_mon clo:
  monotone0 (rclo0 clo).
Proof.
  repeat intro. eapply rclo0_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo0_clo clo r:
  clo (rclo0 clo r) <0= rclo0 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo0_rclo clo r:
  rclo0 clo (rclo0 clo r) <0= rclo0 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo0_compose clo r:
  rclo0 (rclo0 clo) r <0= rclo0 clo r.
Proof.
  intros. induction PR.
  - apply rclo0_base, IN.
  - apply rclo0_rclo.
    eapply rclo0_mon; [apply IN|apply H].
Qed.

End RClo.  

Section Main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone0 gf.

Variant gpaco0 clo r rg : Prop :=
| gpaco0_intro (IN: @rclo0 clo (paco0 (compose gf (rclo0 clo)) (rg \0/ r) \0/ r))
.

Definition gupaco0 clo r := gpaco0 clo r r.

Lemma gpaco0_def_mon clo : monotone0 (compose gf (rclo0 clo)).
Proof.
  eapply monotone0_compose. apply gf_mon. apply rclo0_mon.
Qed.

Hint Resolve gpaco0_def_mon : paco.

Lemma gpaco0_mon clo r r' rg rg'
      (IN: @gpaco0 clo r rg)
      (LEr: r <0= r')
      (LErg: rg <0= rg'):
  @gpaco0 clo r' rg'.
Proof.
  destruct IN. econstructor.
  eapply rclo0_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco0_mon. apply H.
  intros. destruct PR.
  - left. apply LErg, H0.
  - right. apply LEr, H0.
Qed.

Lemma gupaco0_mon clo r r'
      (IN: @gupaco0 clo r)
      (LEr: r <0= r'):
  @gupaco0 clo r'.
Proof.
  eapply gpaco0_mon. apply IN. apply LEr. apply LEr.
Qed.

Lemma gpaco0_base clo r rg: r <0= gpaco0 clo r rg.
Proof.
  econstructor. apply rclo0_base. right. apply PR.
Qed.

Lemma gpaco0_rclo clo r:
  rclo0 clo r <0= gupaco0 clo r.
Proof.
  intros. econstructor.
  eapply rclo0_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco0_clo clo r:
  clo r <0= gupaco0 clo r.
Proof.
  intros. apply gpaco0_rclo. eapply rclo0_clo', PR.
  apply rclo0_base.
Qed.

Lemma gpaco0_step_gen clo r rg:
  gf (gpaco0 clo (rg \0/ r) (rg \0/ r)) <0= gpaco0 clo r rg.
Proof.
  intros. econstructor. apply rclo0_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo0_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco0_mon. apply H. intros. destruct PR0; apply H0.
  - right. apply H.
Qed.

Lemma gpaco0_step clo r rg:
  gf (gpaco0 clo rg rg) <0= gpaco0 clo r rg.
Proof.
  intros. apply gpaco0_step_gen.
  eapply gf_mon. apply PR. intros.
  eapply gpaco0_mon. apply PR0. left; apply PR1. left; apply PR1.
Qed.

Lemma gpaco0_final clo r rg:
  (r \0/ paco0 gf rg) <0= gpaco0 clo r rg.
Proof.
  intros. destruct PR. apply gpaco0_base, H.
  econstructor. apply rclo0_base.
  left. eapply paco0_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo0_base. apply PR0.
  - intros. left. apply PR.
Qed.

Lemma gpaco0_unfold clo r rg:
  gpaco0 clo r rg <0= rclo0 clo (gf (gupaco0 clo (rg \0/ r)) \0/ r).
Proof.
  intros. destruct PR.
  eapply rclo0_mon. apply IN.
  intros. destruct PR; cycle 1. right; apply H.
  left. _punfold H; [|apply gpaco0_def_mon].
  eapply gf_mon. apply H.
  intros. econstructor.
  eapply rclo0_mon. apply PR.
  intros. destruct PR0; cycle 1. right. apply H0.
  left. eapply paco0_mon. apply H0.
  intros. left. apply PR0.
Qed.
  
Lemma gpaco0_cofix clo r rg 
      l (OBG: forall rr (INC: rg <0= rr) (CIH: l <0= rr), l <0= gpaco0 clo r rr):
  l <0= gpaco0 clo r rg.
Proof.
  assert (IN: l <0= gpaco0 clo r (rg \0/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo0_mon. apply IN0.
  clear IN0.
  intros. destruct PR; [|right; apply H].
  left. revert H.
  pcofix CIH. intros.
  _punfold H0; [..|apply gpaco0_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo0_rclo. eapply rclo0_mon. apply PR.
  intros. destruct PR0.
  - apply rclo0_base. right. apply CIH. apply H.
  - destruct H; [destruct H|].
    + apply rclo0_base. right. apply CIH0. left. apply H.
    + apply IN in H. destruct H.
      eapply rclo0_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. right. apply H.
    + apply rclo0_base. right. apply CIH0. right. apply H.
Qed.

Lemma gpaco0_gupaco clo r rg:
  gupaco0 clo (gpaco0 clo r rg) <0= gpaco0 clo r rg.
Proof.
  eapply gpaco0_cofix.
  intros. destruct PR. econstructor.
  apply rclo0_rclo. eapply rclo0_mon. apply IN.
  intros. destruct PR.
  - apply rclo0_base. left.
    eapply paco0_mon. apply H.
    intros. left; apply CIH.
    econstructor. apply rclo0_base. right.
    destruct PR; apply H0.
  - destruct H. eapply rclo0_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco0_mon. apply H.
    intros. destruct PR.
    + left. apply INC. apply H0.
    + right. apply H0.
Qed.

Lemma gpaco0_uclo uclo clo r rg 
      (LEclo: uclo <1= gupaco0 clo) :
  uclo (gpaco0 clo r rg) <0= gpaco0 clo r rg.
Proof.
  intros. apply gpaco0_gupaco. apply LEclo, PR.
Qed.

Lemma gpaco0_weaken  clo r rg:
  gpaco0 (gupaco0 clo) r rg <0= gpaco0 clo r rg.
Proof.
  intros. apply gpaco0_unfold in PR.
  induction PR.
  - destruct IN; cycle 1. apply gpaco0_base, H.
    apply gpaco0_step_gen. eapply gf_mon. apply H.
    clear H.
    eapply gpaco0_cofix. intros.
    apply gpaco0_unfold in PR.
    induction PR.
    + destruct IN; cycle 1. apply gpaco0_base, H.
      apply gpaco0_step. eapply gf_mon. apply H.
      intros. apply gpaco0_base. apply CIH.
      eapply gupaco0_mon. apply PR.
      intros. destruct PR0; apply H0.
    + apply gpaco0_gupaco.
      eapply gupaco0_mon. apply IN. apply H.
  - apply gpaco0_gupaco.
    eapply gupaco0_mon. apply IN. apply H.
Qed.

End Main.

Hint Resolve gpaco0_def_mon : paco.

Section GeneralMonotonicity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone0 gf.
  
Lemma gpaco0_mon_gen (gf' clo clo': rel -> rel) r r' rg rg'
      (IN: @gpaco0 gf clo r rg)
      (LEgf: gf <1= gf')
      (LEclo: clo <1= clo')
      (LEr: r <0= r')
      (LErg: rg <0= rg') :
  @gpaco0 gf' clo' r' rg'.
Proof.
  eapply gpaco0_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo0_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco0_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply gf_mon. apply PR.
    intros. eapply rclo0_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma gpaco0_mon_bot (gf' clo clo': rel -> rel) r' rg'
      (IN: @gpaco0 gf clo bot0 bot0)
      (LEgf: gf <1= gf')
      (LEclo: clo <1= clo'):
  @gpaco0 gf' clo' r' rg'.
Proof.
  eapply gpaco0_mon_gen. apply IN. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco0_mon_gen (gf' clo clo': rel -> rel) r r'
      (IN: @gupaco0 gf clo r)
      (LEgf: gf <1= gf')
      (LEclo: clo <1= clo')
      (LEr: r <0= r'):
  @gupaco0 gf' clo' r'.
Proof.
  eapply gpaco0_mon_gen. apply IN. apply LEgf. apply LEclo. apply LEr. apply LEr.
Qed.

End GeneralMonotonicity.

Section Compatibility.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone0 gf.

Structure compatible0 (clo: rel -> rel) : Prop :=
  compat0_intro {
      compat0_mon: monotone0 clo;
      compat0_compat : forall r,
          clo (gf r) <0= gf (clo r);
    }.

Structure wcompatible0 clo : Prop :=
  wcompat0_intro {
      wcompat0_mon: monotone0 clo;
      wcompat0_wcompat : forall r,
          clo (gf r) <0= gf (gupaco0 gf clo r);
    }.

Inductive cpn0 (r: rel) : Prop :=
| cpn0_intro
    clo
    (COM: compatible0 clo)
    (CLO: clo r)
.

Lemma rclo0_compat clo
      (COM: compatible0 clo):
  compatible0 (rclo0 clo).
Proof.
  econstructor.
  - apply rclo0_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo0_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo0_clo. apply PR.
Qed.

Lemma compat0_wcompat clo
      (CMP: compatible0 clo):
  wcompatible0 clo.
Proof.
  econstructor. apply CMP.
  intros. apply CMP in PR.
  eapply gf_mon. apply PR.
  intros. apply gpaco0_clo, PR0. 
Qed.

Lemma wcompat0_compat clo
      (WCMP: wcompatible0 clo) :
  compatible0 (gupaco0 gf clo).
Proof.
  econstructor.
  { red; intros. eapply gpaco0_mon. apply IN. apply LE. apply LE. }

  intros. apply gpaco0_unfold in PR; [|apply gf_mon].
  induction PR.
  - destruct IN; cycle 1.
    + eapply gf_mon. apply H.
      intros. apply gpaco0_base, PR.
    + eapply gf_mon. apply H.
      intros. apply gpaco0_gupaco. apply gf_mon.
      eapply gupaco0_mon. apply PR.
      intros. apply gpaco0_step. apply gf_mon.
      eapply gf_mon. destruct PR0 as [X|X]; apply X.
      intros. apply gpaco0_base, PR1.
  - eapply gf_mon, gpaco0_gupaco, gf_mon.
    apply WCMP. eapply WCMP. apply IN.
    intros. apply H, PR.
Qed.

Lemma wcompat0_union clo1 clo2
      (WCMP1: wcompatible0 clo1)
      (WCMP2: wcompatible0 clo2):
  wcompatible0 (clo1 \1/ clo2).
Proof.
  econstructor.
  - apply monotone0_union. apply WCMP1. apply WCMP2.
  - intros. destruct PR.
    + apply WCMP1 in H. eapply gf_mon. apply H.
      intros. eapply gupaco0_mon_gen. apply gf_mon. apply PR. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco0_mon_gen. apply gf_mon. apply PR.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
Qed.

Lemma cpn0_mon: monotone0 cpn0.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat0_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn0_greatest: forall clo (COM: compatible0 clo), clo <1= cpn0.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn0_compat: compatible0 cpn0.
Proof.
  econstructor; [apply cpn0_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat0_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn0_wcompat: wcompatible0 cpn0.
Proof. apply compat0_wcompat, cpn0_compat. Qed.

Lemma cpn0_gupaco:
  gupaco0 gf cpn0 <1= cpn0.
Proof.
  intros. eapply cpn0_greatest, PR. apply wcompat0_compat. apply cpn0_wcompat.
Qed.

Lemma cpn0_uclo uclo
      (MON: monotone0 uclo)
      (WCOM: forall r, uclo (gf r) <0= gf (gupaco0 gf (uclo \1/ cpn0) r)):
  uclo <1= gupaco0 gf cpn0.
Proof.
  intros. apply gpaco0_clo.
  exists (gupaco0 gf (uclo \1/ cpn0)).
  - apply wcompat0_compat.
    econstructor.
    + apply monotone0_union. apply MON. apply cpn0_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat0_compat in H; [| apply cpn0_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco0_clo. right. apply PR0.
  - apply gpaco0_clo. left. apply PR.
Qed.

End Compatibility.

Section Soundness.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone0 gf.

Lemma gpaco0_compat_init clo
      (CMP: compatible0 gf clo):
  gpaco0 gf clo bot0 bot0 <0= paco0 gf bot0.
Proof.
  intros. destruct PR. revert IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo0_rclo, PR]. 
  apply compat0_compat with (gf:=gf). apply rclo0_compat. apply gf_mon. apply CMP.
  eapply rclo0_mon. apply IN.
  intros. destruct PR; [|contradiction]. _punfold H; [..|apply gpaco0_def_mon, gf_mon].
  eapply gpaco0_def_mon. apply gf_mon. apply H.
  intros. destruct PR; [|destruct H0; contradiction]. left. apply H0.
Qed.

Lemma gpaco0_init clo
      (WCMP: wcompatible0 gf clo):
  gpaco0 gf clo bot0 bot0 <0= paco0 gf bot0.
Proof.
  intros. eapply gpaco0_compat_init.
  - apply wcompat0_compat, WCMP. apply gf_mon.
  - eapply gpaco0_mon_bot. apply gf_mon. apply PR. intros; apply PR0.
    intros. apply gpaco0_clo, PR0.
Qed.

Lemma gpaco0_unfold_bot clo
      (WCMP: wcompatible0 gf clo):
  gpaco0 gf clo bot0 bot0 <0= gf (gpaco0 gf clo bot0 bot0).
Proof.
  intros. apply gpaco0_init in PR; [|apply WCMP].
  _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. destruct PR0; [|contradiction]. apply gpaco0_final. apply gf_mon. right. apply H.
Qed.

End Soundness.

End GeneralizedPaco0.

Hint Resolve gpaco0_def_mon : paco.
Hint Unfold gupaco0 : paco.
Hint Resolve gpaco0_base : paco.
Hint Resolve gpaco0_step : paco.
Hint Resolve gpaco0_final : paco.
