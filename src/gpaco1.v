Require Export Program.Basics. Open Scope program_scope.
Require Import paco1 pacotac.
Set Implicit Arguments.

Section GeneralizedPaco1.

Variable T0 : Type.

Local Notation rel := (rel1 T0).

Section RClo.

Inductive rclo1 (clo: rel->rel) (r: rel): rel :=
| rclo1_base
    x0
    (IN: r x0):
    @rclo1 clo r x0
| rclo1_clo'
    r' x0
    (LE: r' <1= rclo1 clo r)
    (IN: clo r' x0):
    @rclo1 clo r x0
.           

Lemma rclo1_mon_gen clo clo' r r' x0
      (IN: @rclo1 clo r x0)
      (LEclo: clo <2= clo')
      (LEr: r <1= r') :
  @rclo1 clo' r' x0.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo1_mon clo:
  monotone1 (rclo1 clo).
Proof.
  repeat intro. eapply rclo1_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo1_clo clo r:
  clo (rclo1 clo r) <1= rclo1 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo1_rclo clo r:
  rclo1 clo (rclo1 clo r) <1= rclo1 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo1_compose clo r:
  rclo1 (rclo1 clo) r <1= rclo1 clo r.
Proof.
  intros. induction PR.
  - apply rclo1_base, IN.
  - apply rclo1_rclo.
    eapply rclo1_mon; [apply IN|apply H].
Qed.

End RClo.  

Section Main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone1 gf.

Variant gpaco1 clo r rg x0 : Prop :=
| gpaco1_intro (IN: @rclo1 clo (paco1 (compose gf (rclo1 clo)) (rg \1/ r) \1/ r) x0)
.

Definition gupaco1 clo r := gpaco1 clo r r.

Lemma gpaco1_def_mon clo : monotone1 (compose gf (rclo1 clo)).
Proof.
  eapply monotone1_compose. apply gf_mon. apply rclo1_mon.
Qed.

Hint Resolve gpaco1_def_mon : paco.

Lemma gpaco1_mon clo r r' rg rg' x0
      (IN: @gpaco1 clo r rg x0)
      (LEr: r <1= r')
      (LErg: rg <1= rg'):
  @gpaco1 clo r' rg' x0.
Proof.
  destruct IN. econstructor.
  eapply rclo1_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco1_mon. apply H.
  intros. destruct PR.
  - left. apply LErg, H0.
  - right. apply LEr, H0.
Qed.

Lemma gupaco1_mon clo r r' x0
      (IN: @gupaco1 clo r x0)
      (LEr: r <1= r'):
  @gupaco1 clo r' x0.
Proof.
  eapply gpaco1_mon. apply IN. apply LEr. apply LEr.
Qed.

Lemma gpaco1_base clo r rg: r <1= gpaco1 clo r rg.
Proof.
  econstructor. apply rclo1_base. right. apply PR.
Qed.

Lemma gpaco1_rclo clo r:
  rclo1 clo r <1= gupaco1 clo r.
Proof.
  intros. econstructor.
  eapply rclo1_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco1_clo clo r:
  clo r <1= gupaco1 clo r.
Proof.
  intros. apply gpaco1_rclo. eapply rclo1_clo', PR.
  apply rclo1_base.
Qed.

Lemma gpaco1_step_gen clo r rg:
  gf (gpaco1 clo (rg \1/ r) (rg \1/ r)) <1= gpaco1 clo r rg.
Proof.
  intros. econstructor. apply rclo1_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo1_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco1_mon. apply H. intros. destruct PR0; apply H0.
  - right. apply H.
Qed.

Lemma gpaco1_step clo r rg:
  gf (gpaco1 clo rg rg) <1= gpaco1 clo r rg.
Proof.
  intros. apply gpaco1_step_gen.
  eapply gf_mon. apply PR. intros.
  eapply gpaco1_mon. apply PR0. left; apply PR1. left; apply PR1.
Qed.

Lemma gpaco1_final clo r rg:
  (r \1/ paco1 gf rg) <1= gpaco1 clo r rg.
Proof.
  intros. destruct PR. apply gpaco1_base, H.
  econstructor. apply rclo1_base.
  left. eapply paco1_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo1_base. apply PR0.
  - intros. left. apply PR.
Qed.

Lemma gpaco1_unfold clo r rg:
  gpaco1 clo r rg <1= rclo1 clo (gf (gupaco1 clo (rg \1/ r)) \1/ r).
Proof.
  intros. destruct PR.
  eapply rclo1_mon. apply IN.
  intros. destruct PR; cycle 1. right; apply H.
  left. _punfold H; [|apply gpaco1_def_mon].
  eapply gf_mon. apply H.
  intros. econstructor.
  eapply rclo1_mon. apply PR.
  intros. destruct PR0; cycle 1. right. apply H0.
  left. eapply paco1_mon. apply H0.
  intros. left. apply PR0.
Qed.
  
Lemma gpaco1_cofix clo r rg 
      l (OBG: forall rr (INC: rg <1= rr) (CIH: l <1= rr), l <1= gpaco1 clo r rr):
  l <1= gpaco1 clo r rg.
Proof.
  assert (IN: l <1= gpaco1 clo r (rg \1/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo1_mon. apply IN0.
  clear x0 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply gpaco1_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo1_rclo. eapply rclo1_mon. apply PR.
  intros. destruct PR0.
  - apply rclo1_base. right. apply CIH. apply H.
  - destruct H; [destruct H|].
    + apply rclo1_base. right. apply CIH0. left. apply H.
    + apply IN in H. destruct H.
      eapply rclo1_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. right. apply H.
    + apply rclo1_base. right. apply CIH0. right. apply H.
Qed.

Lemma gpaco1_gupaco clo r rg:
  gupaco1 clo (gpaco1 clo r rg) <1= gpaco1 clo r rg.
Proof.
  eapply gpaco1_cofix.
  intros. destruct PR. econstructor.
  apply rclo1_rclo. eapply rclo1_mon. apply IN.
  intros. destruct PR.
  - apply rclo1_base. left.
    eapply paco1_mon. apply H.
    intros. left; apply CIH.
    econstructor. apply rclo1_base. right.
    destruct PR; apply H0.
  - destruct H. eapply rclo1_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco1_mon. apply H.
    intros. destruct PR.
    + left. apply INC. apply H0.
    + right. apply H0.
Qed.

Lemma gpaco1_uclo uclo clo r rg 
      (LEclo: uclo <2= gupaco1 clo) :
  uclo (gpaco1 clo r rg) <1= gpaco1 clo r rg.
Proof.
  intros. apply gpaco1_gupaco. apply LEclo, PR.
Qed.

Lemma gpaco1_weaken  clo r rg:
  gpaco1 (gupaco1 clo) r rg <1= gpaco1 clo r rg.
Proof.
  intros. apply gpaco1_unfold in PR.
  induction PR.
  - destruct IN; cycle 1. apply gpaco1_base, H.
    apply gpaco1_step_gen. eapply gf_mon. apply H.
    clear x0 H.
    eapply gpaco1_cofix. intros.
    apply gpaco1_unfold in PR.
    induction PR.
    + destruct IN; cycle 1. apply gpaco1_base, H.
      apply gpaco1_step. eapply gf_mon. apply H.
      intros. apply gpaco1_base. apply CIH.
      eapply gupaco1_mon. apply PR.
      intros. destruct PR0; apply H0.
    + apply gpaco1_gupaco.
      eapply gupaco1_mon. apply IN. apply H.
  - apply gpaco1_gupaco.
    eapply gupaco1_mon. apply IN. apply H.
Qed.

End Main.

Hint Resolve gpaco1_def_mon : paco.

Section GeneralMonotonicity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone1 gf.
  
Lemma gpaco1_mon_gen (gf' clo clo': rel -> rel) x0 r r' rg rg'
      (IN: @gpaco1 gf clo r rg x0)
      (LEgf: gf <2= gf')
      (LEclo: clo <2= clo')
      (LEr: r <1= r')
      (LErg: rg <1= rg') :
  @gpaco1 gf' clo' r' rg' x0.
Proof.
  eapply gpaco1_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo1_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco1_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply gf_mon. apply PR.
    intros. eapply rclo1_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma gpaco1_mon_bot (gf' clo clo': rel -> rel) x0 r' rg'
      (IN: @gpaco1 gf clo bot1 bot1 x0)
      (LEgf: gf <2= gf')
      (LEclo: clo <2= clo'):
  @gpaco1 gf' clo' r' rg' x0.
Proof.
  eapply gpaco1_mon_gen. apply IN. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco1_mon_gen (gf' clo clo': rel -> rel) x0 r r'
      (IN: @gupaco1 gf clo r x0)
      (LEgf: gf <2= gf')
      (LEclo: clo <2= clo')
      (LEr: r <1= r'):
  @gupaco1 gf' clo' r' x0.
Proof.
  eapply gpaco1_mon_gen. apply IN. apply LEgf. apply LEclo. apply LEr. apply LEr.
Qed.

End GeneralMonotonicity.

Section Compatibility.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone1 gf.

Structure compatible1 (clo: rel -> rel) : Prop :=
  compat1_intro {
      compat1_mon: monotone1 clo;
      compat1_compat : forall r,
          clo (gf r) <1= gf (clo r);
    }.

Structure wcompatible1 clo : Prop :=
  wcompat1_intro {
      wcompat1_mon: monotone1 clo;
      wcompat1_wcompat : forall r,
          clo (gf r) <1= gf (gupaco1 gf clo r);
    }.

Inductive cpn1 (r: rel) x0 : Prop :=
| cpn1_intro
    clo
    (COM: compatible1 clo)
    (CLO: clo r x0)
.

Lemma rclo1_compat clo
      (COM: compatible1 clo):
  compatible1 (rclo1 clo).
Proof.
  econstructor.
  - apply rclo1_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo1_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo1_clo. apply PR.
Qed.

Lemma compat1_wcompat clo
      (CMP: compatible1 clo):
  wcompatible1 clo.
Proof.
  econstructor. apply CMP.
  intros. apply CMP in PR.
  eapply gf_mon. apply PR.
  intros. apply gpaco1_clo, PR0. 
Qed.

Lemma wcompat1_compat clo
      (WCMP: wcompatible1 clo) :
  compatible1 (gupaco1 gf clo).
Proof.
  econstructor.
  { red; intros. eapply gpaco1_mon. apply IN. apply LE. apply LE. }

  intros. apply gpaco1_unfold in PR; [|apply gf_mon].
  induction PR.
  - destruct IN; cycle 1.
    + eapply gf_mon. apply H.
      intros. apply gpaco1_base, PR.
    + eapply gf_mon. apply H.
      intros. apply gpaco1_gupaco. apply gf_mon.
      eapply gupaco1_mon. apply PR.
      intros. apply gpaco1_step. apply gf_mon.
      eapply gf_mon. destruct PR0 as [X|X]; apply X.
      intros. apply gpaco1_base, PR1.
  - eapply gf_mon, gpaco1_gupaco, gf_mon.
    apply WCMP. eapply WCMP. apply IN.
    intros. apply H, PR.
Qed.

Lemma wcompat1_union clo1 clo2
      (WCMP1: wcompatible1 clo1)
      (WCMP2: wcompatible1 clo2):
  wcompatible1 (clo1 \2/ clo2).
Proof.
  econstructor.
  - apply monotone1_union. apply WCMP1. apply WCMP2.
  - intros. destruct PR.
    + apply WCMP1 in H. eapply gf_mon. apply H.
      intros. eapply gupaco1_mon_gen. apply gf_mon. apply PR. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco1_mon_gen. apply gf_mon. apply PR.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
Qed.

Lemma cpn1_mon: monotone1 cpn1.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat1_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn1_greatest: forall clo (COM: compatible1 clo), clo <2= cpn1.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn1_compat: compatible1 cpn1.
Proof.
  econstructor; [apply cpn1_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat1_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn1_wcompat: wcompatible1 cpn1.
Proof. apply compat1_wcompat, cpn1_compat. Qed.

Lemma cpn1_gupaco:
  gupaco1 gf cpn1 <2= cpn1.
Proof.
  intros. eapply cpn1_greatest, PR. apply wcompat1_compat. apply cpn1_wcompat.
Qed.

Lemma cpn1_uclo uclo
      (MON: monotone1 uclo)
      (WCOM: forall r, uclo (gf r) <1= gf (gupaco1 gf (uclo \2/ cpn1) r)):
  uclo <2= gupaco1 gf cpn1.
Proof.
  intros. apply gpaco1_clo.
  exists (gupaco1 gf (uclo \2/ cpn1)).
  - apply wcompat1_compat.
    econstructor.
    + apply monotone1_union. apply MON. apply cpn1_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat1_compat in H; [| apply cpn1_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco1_clo. right. apply PR0.
  - apply gpaco1_clo. left. apply PR.
Qed.

End Compatibility.

Section Soundness.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone1 gf.

Lemma gpaco1_compat_init clo
      (CMP: compatible1 gf clo):
  gpaco1 gf clo bot1 bot1 <1= paco1 gf bot1.
Proof.
  intros. destruct PR. revert x0 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo1_rclo, PR]. 
  apply compat1_compat with (gf:=gf). apply rclo1_compat. apply gf_mon. apply CMP.
  eapply rclo1_mon. apply IN.
  intros. destruct PR; [|contradiction]. _punfold H; [..|apply gpaco1_def_mon, gf_mon].
  eapply gpaco1_def_mon. apply gf_mon. apply H.
  intros. destruct PR; [|destruct H0; contradiction]. left. apply H0.
Qed.

Lemma gpaco1_init clo
      (WCMP: wcompatible1 gf clo):
  gpaco1 gf clo bot1 bot1 <1= paco1 gf bot1.
Proof.
  intros. eapply gpaco1_compat_init.
  - apply wcompat1_compat, WCMP. apply gf_mon.
  - eapply gpaco1_mon_bot. apply gf_mon. apply PR. intros; apply PR0.
    intros. apply gpaco1_clo, PR0.
Qed.

Lemma gpaco1_unfold_bot clo
      (WCMP: wcompatible1 gf clo):
  gpaco1 gf clo bot1 bot1 <1= gf (gpaco1 gf clo bot1 bot1).
Proof.
  intros. apply gpaco1_init in PR; [|apply WCMP].
  _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. destruct PR0; [|contradiction]. apply gpaco1_final. apply gf_mon. right. apply H.
Qed.

End Soundness.

End GeneralizedPaco1.

Hint Resolve gpaco1_def_mon : paco.
Hint Unfold gupaco1 : paco.
Hint Resolve gpaco1_base : paco.
Hint Resolve gpaco1_step : paco.
Hint Resolve gpaco1_final : paco.
