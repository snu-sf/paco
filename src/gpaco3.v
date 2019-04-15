Require Export Program.Basics. Open Scope program_scope.
Require Import paco3 pacotac.
Set Implicit Arguments.

Section GeneralizedPaco3.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.

Local Notation rel := (rel3 T0 T1 T2).

Lemma monotone3_compose (clo1 clo2: rel -> rel)
      (MON1: monotone3 clo1)
      (MON2: monotone3 clo2):
  monotone3 (compose clo1 clo2).
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone3_union (clo1 clo2: rel -> rel)
      (MON1: monotone3 clo1)
      (MON2: monotone3 clo2):
  monotone3 (clo1 \4/ clo2).
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

Section RClo.

Inductive rclo3 (clo: rel->rel) (r: rel): rel :=
| rclo3_base
    x0 x1 x2
    (IN: r x0 x1 x2):
    @rclo3 clo r x0 x1 x2
| rclo3_clo'
    r' x0 x1 x2
    (LE: r' <3= rclo3 clo r)
    (IN: clo r' x0 x1 x2):
    @rclo3 clo r x0 x1 x2
.           

Lemma rclo3_mon_gen clo clo' r r' x0 x1 x2
      (IN: @rclo3 clo r x0 x1 x2)
      (LEclo: clo <4= clo')
      (LEr: r <3= r') :
  @rclo3 clo' r' x0 x1 x2.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo3_mon clo:
  monotone3 (rclo3 clo).
Proof.
  repeat intro. eapply rclo3_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo3_clo clo r:
  clo (rclo3 clo r) <3= rclo3 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo3_rclo clo r:
  rclo3 clo (rclo3 clo r) <3= rclo3 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo3_compose clo r:
  rclo3 (rclo3 clo) r <3= rclo3 clo r.
Proof.
  intros. induction PR.
  - apply rclo3_base, IN.
  - apply rclo3_rclo.
    eapply rclo3_mon; [apply IN|apply H].
Qed.

End RClo.  

Section Main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone3 gf.

Variant gpaco3 clo r rg x0 x1 x2 : Prop :=
| gpaco3_intro (IN: @rclo3 clo (paco3 (compose gf (rclo3 clo)) (rg \3/ r) \3/ r) x0 x1 x2)
.

Definition gupaco3 clo r := gpaco3 clo r r.

Lemma gpaco3_def_mon clo : monotone3 (compose gf (rclo3 clo)).
Proof.
  eapply monotone3_compose. apply gf_mon. apply rclo3_mon.
Qed.

Hint Resolve gpaco3_def_mon : paco.

Lemma gpaco3_mon clo r r' rg rg' x0 x1 x2
      (IN: @gpaco3 clo r rg x0 x1 x2)
      (LEr: r <3= r')
      (LErg: rg <3= rg'):
  @gpaco3 clo r' rg' x0 x1 x2.
Proof.
  destruct IN. econstructor.
  eapply rclo3_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco3_mon. apply H.
  intros. destruct PR.
  - left. apply LErg, H0.
  - right. apply LEr, H0.
Qed.

Lemma gupaco3_mon clo r r' x0 x1 x2
      (IN: @gupaco3 clo r x0 x1 x2)
      (LEr: r <3= r'):
  @gupaco3 clo r' x0 x1 x2.
Proof.
  eapply gpaco3_mon. apply IN. apply LEr. apply LEr.
Qed.

Lemma gpaco3_base clo r rg: r <3= gpaco3 clo r rg.
Proof.
  econstructor. apply rclo3_base. right. apply PR.
Qed.

Lemma gpaco3_rclo clo r:
  rclo3 clo r <3= gupaco3 clo r.
Proof.
  intros. econstructor.
  eapply rclo3_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco3_clo clo r:
  clo r <3= gupaco3 clo r.
Proof.
  intros. apply gpaco3_rclo. eapply rclo3_clo', PR.
  apply rclo3_base.
Qed.

Lemma gpaco3_step_gen clo r rg:
  gf (gpaco3 clo (rg \3/ r) (rg \3/ r)) <3= gpaco3 clo r rg.
Proof.
  intros. econstructor. apply rclo3_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo3_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco3_mon. apply H. intros. destruct PR0; apply H0.
  - right. apply H.
Qed.

Lemma gpaco3_step clo r rg:
  gf (gpaco3 clo rg rg) <3= gpaco3 clo r rg.
Proof.
  intros. apply gpaco3_step_gen.
  eapply gf_mon. apply PR. intros.
  eapply gpaco3_mon. apply PR0. left; apply PR1. left; apply PR1.
Qed.

Lemma gpaco3_final clo r rg:
  (r \3/ paco3 gf rg) <3= gpaco3 clo r rg.
Proof.
  intros. destruct PR. apply gpaco3_base, H.
  econstructor. apply rclo3_base.
  left. eapply paco3_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo3_base. apply PR0.
  - intros. left. apply PR.
Qed.

Lemma gpaco3_unfold clo r rg:
  gpaco3 clo r rg <3= rclo3 clo (gf (gupaco3 clo (rg \3/ r)) \3/ r).
Proof.
  intros. destruct PR.
  eapply rclo3_mon. apply IN.
  intros. destruct PR; cycle 1. right; apply H.
  left. _punfold H; [|apply gpaco3_def_mon].
  eapply gf_mon. apply H.
  intros. econstructor.
  eapply rclo3_mon. apply PR.
  intros. destruct PR0; cycle 1. right. apply H0.
  left. eapply paco3_mon. apply H0.
  intros. left. apply PR0.
Qed.
  
Lemma gpaco3_cofix clo r rg 
      l (OBG: forall rr (INC: rg <3= rr) (CIH: l <3= rr), l <3= gpaco3 clo r rr):
  l <3= gpaco3 clo r rg.
Proof.
  assert (IN: l <3= gpaco3 clo r (rg \3/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo3_mon. apply IN0.
  clear x0 x1 x2 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply gpaco3_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo3_rclo. eapply rclo3_mon. apply PR.
  intros. destruct PR0.
  - apply rclo3_base. right. apply CIH. apply H.
  - destruct H; [destruct H|].
    + apply rclo3_base. right. apply CIH0. left. apply H.
    + apply IN in H. destruct H.
      eapply rclo3_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. right. apply H.
    + apply rclo3_base. right. apply CIH0. right. apply H.
Qed.

Lemma gpaco3_gupaco clo r rg:
  gupaco3 clo (gpaco3 clo r rg) <3= gpaco3 clo r rg.
Proof.
  eapply gpaco3_cofix.
  intros. destruct PR. econstructor.
  apply rclo3_rclo. eapply rclo3_mon. apply IN.
  intros. destruct PR.
  - apply rclo3_base. left.
    eapply paco3_mon. apply H.
    intros. left; apply CIH.
    econstructor. apply rclo3_base. right.
    destruct PR; apply H0.
  - destruct H. eapply rclo3_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco3_mon. apply H.
    intros. destruct PR.
    + left. apply INC. apply H0.
    + right. apply H0.
Qed.

Lemma gpaco3_uclo uclo clo r rg 
      (LEclo: uclo <4= gupaco3 clo) :
  uclo (gpaco3 clo r rg) <3= gpaco3 clo r rg.
Proof.
  intros. apply gpaco3_gupaco. apply LEclo, PR.
Qed.

Lemma gpaco3_weaken  clo r rg:
  gpaco3 (gupaco3 clo) r rg <3= gpaco3 clo r rg.
Proof.
  intros. apply gpaco3_unfold in PR.
  induction PR.
  - destruct IN; cycle 1. apply gpaco3_base, H.
    apply gpaco3_step_gen. eapply gf_mon. apply H.
    clear x0 x1 x2 H.
    eapply gpaco3_cofix. intros.
    apply gpaco3_unfold in PR.
    induction PR.
    + destruct IN; cycle 1. apply gpaco3_base, H.
      apply gpaco3_step. eapply gf_mon. apply H.
      intros. apply gpaco3_base. apply CIH.
      eapply gupaco3_mon. apply PR.
      intros. destruct PR0; apply H0.
    + apply gpaco3_gupaco.
      eapply gupaco3_mon. apply IN. apply H.
  - apply gpaco3_gupaco.
    eapply gupaco3_mon. apply IN. apply H.
Qed.

End Main.

Hint Resolve gpaco3_def_mon : paco.

Section GeneralMonotonicity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone3 gf.
  
Lemma gpaco3_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 r r' rg rg'
      (IN: @gpaco3 gf clo r rg x0 x1 x2)
      (LEgf: gf <4= gf')
      (LEclo: clo <4= clo')
      (LEr: r <3= r')
      (LErg: rg <3= rg') :
  @gpaco3 gf' clo' r' rg' x0 x1 x2.
Proof.
  eapply gpaco3_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo3_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco3_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply gf_mon. apply PR.
    intros. eapply rclo3_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma gpaco3_mon_bot (gf' clo clo': rel -> rel) x0 x1 x2 r' rg'
      (IN: @gpaco3 gf clo bot3 bot3 x0 x1 x2)
      (LEgf: gf <4= gf')
      (LEclo: clo <4= clo'):
  @gpaco3 gf' clo' r' rg' x0 x1 x2.
Proof.
  eapply gpaco3_mon_gen. apply IN. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco3_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 r r'
      (IN: @gupaco3 gf clo r x0 x1 x2)
      (LEgf: gf <4= gf')
      (LEclo: clo <4= clo')
      (LEr: r <3= r'):
  @gupaco3 gf' clo' r' x0 x1 x2.
Proof.
  eapply gpaco3_mon_gen. apply IN. apply LEgf. apply LEclo. apply LEr. apply LEr.
Qed.

End GeneralMonotonicity.

Section Compatibility.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone3 gf.

Structure compatible3 (clo: rel -> rel) : Prop :=
  compat3_intro {
      compat3_mon: monotone3 clo;
      compat3_compat : forall r,
          clo (gf r) <3= gf (clo r);
    }.

Structure wcompatible3 clo : Prop :=
  wcompat3_intro {
      wcompat3_mon: monotone3 clo;
      wcompat3_wcompat : forall r,
          clo (gf r) <3= gf (gupaco3 gf clo r);
    }.

Inductive cpn3 (r: rel) x0 x1 x2 : Prop :=
| cpn3_intro
    clo
    (COM: compatible3 clo)
    (CLO: clo r x0 x1 x2)
.

Lemma rclo3_compat clo
      (COM: compatible3 clo):
  compatible3 (rclo3 clo).
Proof.
  econstructor.
  - apply rclo3_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo3_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo3_clo. apply PR.
Qed.

Lemma compat3_wcompat clo
      (CMP: compatible3 clo):
  wcompatible3 clo.
Proof.
  econstructor. apply CMP.
  intros. apply CMP in PR.
  eapply gf_mon. apply PR.
  intros. apply gpaco3_clo, PR0. 
Qed.

Lemma wcompat3_compat clo
      (WCMP: wcompatible3 clo) :
  compatible3 (gupaco3 gf clo).
Proof.
  econstructor.
  { red; intros. eapply gpaco3_mon. apply IN. apply LE. apply LE. }

  intros. apply gpaco3_unfold in PR; [|apply gf_mon].
  induction PR.
  - destruct IN; cycle 1.
    + eapply gf_mon. apply H.
      intros. apply gpaco3_base, PR.
    + eapply gf_mon. apply H.
      intros. apply gpaco3_gupaco. apply gf_mon.
      eapply gupaco3_mon. apply PR.
      intros. apply gpaco3_step. apply gf_mon.
      eapply gf_mon. destruct PR0 as [X|X]; apply X.
      intros. apply gpaco3_base, PR1.
  - eapply gf_mon, gpaco3_gupaco, gf_mon.
    apply WCMP. eapply WCMP. apply IN.
    intros. apply H, PR.
Qed.

Lemma wcompat3_union clo1 clo2
      (WCMP1: wcompatible3 clo1)
      (WCMP2: wcompatible3 clo2):
  wcompatible3 (clo1 \4/ clo2).
Proof.
  econstructor.
  - apply monotone3_union. apply WCMP1. apply WCMP2.
  - intros. destruct PR.
    + apply WCMP1 in H. eapply gf_mon. apply H.
      intros. eapply gupaco3_mon_gen. apply gf_mon. apply PR. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco3_mon_gen. apply gf_mon. apply PR.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
Qed.

Lemma cpn3_mon: monotone3 cpn3.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat3_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn3_greatest: forall clo (COM: compatible3 clo), clo <4= cpn3.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn3_compat: compatible3 cpn3.
Proof.
  econstructor; [apply cpn3_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat3_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn3_wcompat: wcompatible3 cpn3.
Proof. apply compat3_wcompat, cpn3_compat. Qed.

Lemma cpn3_uclo uclo
      (MON: monotone3 uclo)
      (WCOM: forall r, uclo (gf r) <3= gf (gupaco3 gf (uclo \4/ cpn3) r)):
  uclo <4= gupaco3 gf cpn3.
Proof.
  intros. apply gpaco3_clo.
  exists (gupaco3 gf (uclo \4/ cpn3)).
  - apply wcompat3_compat.
    econstructor.
    + apply monotone3_union. apply MON. apply cpn3_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat3_compat in H; [| apply cpn3_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco3_clo. right. apply PR0.
  - apply gpaco3_clo. left. apply PR.
Qed.

End Compatibility.

Section Soundness.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone3 gf.

Lemma gpaco3_compat_init clo
      (CMP: compatible3 gf clo):
  gpaco3 gf clo bot3 bot3 <3= paco3 gf bot3.
Proof.
  intros. destruct PR. revert x0 x1 x2 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo3_rclo, PR]. 
  apply compat3_compat with (gf:=gf). apply rclo3_compat. apply gf_mon. apply CMP.
  eapply rclo3_mon. apply IN.
  intros. destruct PR; [|contradiction]. _punfold H; [..|apply gpaco3_def_mon, gf_mon].
  eapply gpaco3_def_mon. apply gf_mon. apply H.
  intros. destruct PR; [|destruct H0; contradiction]. left. apply H0.
Qed.

Lemma gpaco3_init clo
      (WCMP: wcompatible3 gf clo):
  gpaco3 gf clo bot3 bot3 <3= paco3 gf bot3.
Proof.
  intros. eapply gpaco3_compat_init.
  - apply wcompat3_compat, WCMP. apply gf_mon.
  - eapply gpaco3_mon_bot. apply gf_mon. apply PR. intros; apply PR0.
    intros. apply gpaco3_clo, PR0.
Qed.

Lemma gpaco3_unfold_bot clo
      (WCMP: wcompatible3 gf clo):
  gpaco3 gf clo bot3 bot3 <3= gf (gpaco3 gf clo bot3 bot3).
Proof.
  intros. apply gpaco3_init in PR; [|apply WCMP].
  _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. destruct PR0; [|contradiction]. apply gpaco3_final. apply gf_mon. right. apply H.
Qed.

End Soundness.

End GeneralizedPaco3.

Hint Resolve gpaco3_def_mon : paco.
Hint Resolve gpaco3_base : paco.
Hint Resolve gpaco3_step : paco.
Hint Resolve gpaco3_final : paco.
