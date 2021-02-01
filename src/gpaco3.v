Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco3 pacotac.
Set Implicit Arguments.

Section GeneralizedPaco3.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.

Local Notation rel := (rel3 T0 T1 T2).

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

Lemma rclo3_clo_base clo r:
  clo r <3= rclo3 clo r.
Proof.
  intros. eapply rclo3_clo', PR.
  intros. apply rclo3_base, PR0.
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

Lemma gpaco3_gen_guard  clo r rg:
  gpaco3 clo r (rg \3/ r) <3= gpaco3 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  eapply rclo3_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco3_mon_gen; intros. apply H. apply PR.
  destruct PR. apply H0. right. apply H0.
Qed.

Lemma gpaco3_rclo clo r rg:
  rclo3 clo r <3= gpaco3 clo r rg.
Proof.
  intros. econstructor.
  eapply rclo3_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco3_clo clo r rg:
  clo r <3= gpaco3 clo r rg.
Proof.
  intros. apply gpaco3_rclo. eapply rclo3_clo_base, PR.
Qed.

Lemma gpaco3_gen_rclo clo r rg:
  gpaco3 (rclo3 clo) r rg <3= gpaco3 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  apply rclo3_compose.
  eapply rclo3_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco3_mon_gen; intros; [apply H| |apply PR].
  eapply gf_mon, rclo3_compose. apply PR.
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

Lemma gpaco3_gpaco clo r rg:
  gpaco3 clo (gpaco3 clo r rg) (gupaco3 clo (rg \3/ r)) <3= gpaco3 clo r rg.
Proof.
  intros. apply gpaco3_unfold in PR.
  econstructor. apply rclo3_rclo. eapply rclo3_mon. apply PR. clear x0 x1 x2 PR. intros.
  destruct PR; [|destruct H; apply IN].
  apply rclo3_base. left. pstep.
  eapply gf_mon. apply H. clear x0 x1 x2 H. intros.
  cut (@gupaco3 clo (rg \3/ r) x0 x1 x2).
  { intros. destruct H. eapply rclo3_mon. apply IN. intros.
    destruct PR0; [|right; apply H].
    left. eapply paco3_mon. apply H. intros. destruct PR0; apply H0.
  }
  apply gpaco3_gupaco. eapply gupaco3_mon. apply PR. intros.
  destruct PR0; [apply H|].
  eapply gpaco3_mon; [apply H|right|left]; intros; apply PR0.
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
  
Lemma gpaco3_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 r r' rg rg'
      (IN: @gpaco3 gf clo r rg x0 x1 x2)
      (gf_mon: monotone3 gf)
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
      (gf_mon: monotone3 gf)
      (LEgf: gf <4= gf')
      (LEclo: clo <4= clo'):
  @gpaco3 gf' clo' r' rg' x0 x1 x2.
Proof.
  eapply gpaco3_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco3_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 r r'
      (IN: @gupaco3 gf clo r x0 x1 x2)
      (gf_mon: monotone3 gf)
      (LEgf: gf <4= gf')
      (LEclo: clo <4= clo')
      (LEr: r <3= r'):
  @gupaco3 gf' clo' r' x0 x1 x2.
Proof.
  eapply gpaco3_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. apply LEr. apply LEr.
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

Lemma rclo3_dist clo
      (MON: monotone3 clo)
      (DIST: forall r1 r2, clo (r1 \3/ r2) <3= (clo r1 \3/ clo r2)):
  forall r1 r2, rclo3 clo (r1 \3/ r2) <3= (rclo3 clo r1 \3/ rclo3 clo r2).
Proof.
  intros. induction PR.
  + destruct IN; [left|right]; apply rclo3_base, H.
  + assert (REL: clo (rclo3 clo r1 \3/ rclo3 clo r2) x0 x1 x2).
    { eapply MON. apply IN. apply H. }
    apply DIST in REL. destruct REL; [left|right]; apply rclo3_clo, H0.
Qed.

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

Lemma rclo3_wcompat clo
      (COM: wcompatible3 clo):
  wcompatible3 (rclo3 clo).
Proof.
  econstructor.
  - apply rclo3_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. apply gpaco3_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply gpaco3_gupaco. apply gf_mon.
        eapply gupaco3_mon_gen; intros; [apply PR|apply gf_mon|apply PR0| |apply PR0].
        apply rclo3_clo_base, PR0.
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
      intros. eapply gupaco3_mon_gen. apply PR. apply gf_mon. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco3_mon_gen. apply PR. apply gf_mon.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
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
  - eapply gpaco3_mon_bot. apply PR. apply gf_mon. intros; apply PR0.
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

Section Distributivity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone3 gf.

Lemma gpaco3_dist clo r rg
      (CMP: wcompatible3 gf clo)
      (DIST: forall r1 r2, clo (r1 \3/ r2) <3= (clo r1 \3/ clo r2)):
  gpaco3 gf clo r rg <3= (paco3 gf (rclo3 clo (rg \3/ r)) \3/ rclo3 clo r).
Proof.
  intros. apply gpaco3_unfold in PR; [|apply gf_mon].
  apply rclo3_dist in PR; [|apply CMP|apply DIST].
  destruct PR; [|right; apply H].
  left. revert x0 x1 x2 H.
  pcofix CIH; intros.
  apply rclo3_wcompat in H0; [|apply gf_mon|apply CMP].
  pstep. eapply gf_mon. apply H0. intros.
  apply gpaco3_unfold in PR; [|apply gf_mon].
  apply rclo3_compose in PR.
  apply rclo3_dist in PR; [|apply CMP|apply DIST].
  destruct PR.
  - right. apply CIH.
    eapply rclo3_mon. apply H. intros.
    eapply gf_mon. apply PR. intros.
    apply gpaco3_gupaco. apply gf_mon.
    apply gpaco3_gen_rclo. apply gf_mon.
    eapply gupaco3_mon. apply PR0. intros.
    destruct PR1; apply H1.
  - assert (REL: @rclo3 clo (rclo3 clo (gf (gupaco3 gf clo ((rg \3/ r) \3/ (rg \3/ r))) \3/ (rg \3/ r))) x0 x1 x2).
    { eapply rclo3_mon. apply H. intros. apply gpaco3_unfold in PR. apply PR. apply gf_mon. }
    apply rclo3_rclo in REL.
    apply rclo3_dist in REL; [|apply CMP|apply DIST].
    right. destruct REL; cycle 1.
    + apply CIH0, H1.
    + apply CIH.
      eapply rclo3_mon. apply H1. intros.
      eapply gf_mon. apply PR. intros.
      eapply gupaco3_mon. apply PR0. intros.
      destruct PR1; apply H2.
Qed.

Lemma gpaco3_dist_reverse clo r rg:
  (paco3 gf (rclo3 clo (rg \3/ r)) \3/ rclo3 clo r) <3= gpaco3 gf clo r rg.
Proof.
  intros. destruct PR; cycle 1.
  - eapply gpaco3_rclo. apply H.
  - econstructor. apply rclo3_base. left.
    revert x0 x1 x2 H. pcofix CIH; intros.
    _punfold H0; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H0. intros.
    destruct PR.
    + apply rclo3_base. right. apply CIH, H.
    + eapply rclo3_mon. apply H. intros.
      right. apply CIH0. apply PR.
Qed.

End Distributivity.

Section Companion.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone3 gf.

Inductive cpn3 (r: rel) x0 x1 x2 : Prop :=
| cpn3_intro
    clo
    (COM: compatible3 gf clo)
    (CLO: clo r x0 x1 x2)
.

Lemma cpn3_mon: monotone3 cpn3.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat3_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn3_greatest: forall clo (COM: compatible3 gf clo), clo <4= cpn3.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn3_compat: compatible3 gf cpn3.
Proof.
  econstructor; [apply cpn3_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat3_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn3_wcompat: wcompatible3 gf cpn3.
Proof. apply compat3_wcompat, cpn3_compat. apply gf_mon. Qed.

Lemma cpn3_gupaco:
  gupaco3 gf cpn3 <4= cpn3.
Proof.
  intros. eapply cpn3_greatest, PR. apply wcompat3_compat. apply gf_mon. apply cpn3_wcompat.
Qed.

Lemma cpn3_cpn r:
  cpn3 (cpn3 r) <3= cpn3 r.
Proof.
  intros. apply cpn3_gupaco, gpaco3_gupaco, gpaco3_clo. apply gf_mon.
  eapply cpn3_mon, gpaco3_clo. apply PR.
Qed.

Lemma cpn3_base r:
  r <3= cpn3 r.
Proof.
  intros. apply cpn3_gupaco. apply gpaco3_base, PR.
Qed.

Lemma cpn3_clo
      r clo (LE: clo <4= cpn3):
  clo (cpn3 r) <3= cpn3 r.
Proof.
  intros. apply cpn3_cpn, LE, PR.
Qed.

Lemma cpn3_step r:
  gf (cpn3 r) <3= cpn3 r.
Proof.
  intros. apply cpn3_gupaco. apply gpaco3_step. apply gf_mon.
  eapply gf_mon, gpaco3_clo. apply PR.
Qed.

Lemma cpn3_uclo uclo
      (MON: monotone3 uclo)
      (WCOM: forall r, uclo (gf r) <3= gf (gupaco3 gf (uclo \4/ cpn3) r)):
  uclo <4= gupaco3 gf cpn3.
Proof.
  intros. apply gpaco3_clo.
  exists (gupaco3 gf (uclo \4/ cpn3)).
  - apply wcompat3_compat. apply gf_mon.
    econstructor.
    + apply monotone3_union. apply MON. apply cpn3_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat3_compat with (gf:=gf) in H; [| apply cpn3_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco3_clo. right. apply PR0.
  - apply gpaco3_clo. left. apply PR.
Qed.

End Companion.

Section Respectful.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone3 gf.

Structure wrespectful3 (clo: rel -> rel) : Prop :=
  wrespect3_intro {
      wrespect3_mon: monotone3 clo;
      wrespect3_respect :
        forall l r
               (LE: l <3= r)
               (GF: l <3= gf r),
        clo l <3= gf (rclo3 clo r);
    }.

Structure prespectful3 (clo: rel -> rel) : Prop :=
  prespect3_intro {
      prespect3_mon: monotone3 clo;
      prespect3_respect :
        forall l r
               (LE: l <3= r)
               (GF: l <3= gf r),
        clo l <3= paco3 gf (r \3/ clo r);
    }.

Structure grespectful3 (clo: rel -> rel) : Prop :=
  grespect3_intro {
      grespect3_mon: monotone3 clo;
      grespect3_respect :
        forall l r
               (LE: l <3= r)
               (GF: l <3= gf r),
        clo l <3= rclo3 (cpn3 gf) (gf (rclo3 (clo \4/ gupaco3 gf (cpn3 gf)) r));
    }.

Definition gf'3 := id /4\ gf.

Definition compatible'3 := compatible3 gf'3.

Lemma wrespect3_compatible'
      clo (RES: wrespectful3 clo):
  compatible'3 (rclo3 clo).
Proof.
  intros. econstructor. apply rclo3_mon.
  intros. destruct RES. split.
  { eapply rclo3_mon. apply PR. intros. apply PR0. }
  induction PR; intros.
  - eapply gf_mon. apply IN.
    intros. apply rclo3_base, PR.
  - eapply gf_mon.
    + eapply wrespect3_respect0; [|apply H|apply IN].
      intros. eapply rclo3_mon; intros; [apply LE, PR|apply PR0].
    + intros. apply rclo3_rclo, PR.
Qed.

Lemma prespect3_compatible'
      clo (RES: prespectful3 clo):
  compatible'3 (fun r => upaco3 gf (r \3/ clo r)).
Proof.
  econstructor.
  { red; intros. eapply upaco3_mon. apply IN.
    intros. destruct PR.
    - left. apply LE, H.
    - right. eapply RES. apply H. intros. apply LE, PR. }

  intros r.
  assert (LEM: (gf'3 r \3/ clo (gf'3 r)) <3= (r \3/ clo r)).
  { intros. destruct PR.
    - left. apply H.
    - right. eapply RES. apply H. intros. apply PR.
  }

  intros. destruct PR.
  - split.
    + left. eapply paco3_mon. apply H. apply LEM.
    + apply paco3_unfold; [apply gf_mon|].
      eapply paco3_mon. apply H. apply LEM.
  - split.
    + right. apply LEM. apply H.
    + destruct H.
      * eapply gf_mon. apply H. intros. right. left. apply PR.
      * apply paco3_unfold; [apply gf_mon|].
        eapply RES, H; intros; apply PR.
Qed.

Lemma grespect3_compatible'
      clo (RES: grespectful3 clo):
  compatible'3 (rclo3 (clo \4/ cpn3 gf)).
Proof.
  apply wrespect3_compatible'.
  econstructor.
  { red; intros. destruct IN.
    - left. eapply RES; [apply H|]. apply LE.
    - right. eapply cpn3_mon; [apply H|]. apply LE. }
  intros. destruct PR.
  - eapply RES.(grespect3_respect) in H; [|apply LE|apply GF].
    apply (@compat3_compat gf (rclo3 (cpn3 gf))) in H.
    2: { apply rclo3_compat; [apply gf_mon|]. apply cpn3_compat. apply gf_mon. }
    eapply gf_mon; [apply H|].
    intros. apply rclo3_clo. right.
    exists (rclo3 (cpn3 gf)).
    { apply rclo3_compat; [apply gf_mon|]. apply cpn3_compat. apply gf_mon. }
    eapply rclo3_mon; [eapply PR|].
    intros. eapply rclo3_mon_gen; [eapply PR0|..].
    + intros. destruct PR1.
      * left. apply H0.
      * right. apply cpn3_gupaco; [apply gf_mon|apply H0].
    + intros. apply PR1.
  - eapply gf_mon.
    + apply (@compat3_compat gf (rclo3 (cpn3 gf))).
      { apply rclo3_compat; [apply gf_mon|]. apply cpn3_compat. apply gf_mon. }
      eapply rclo3_clo_base. eapply cpn3_mon; [apply H|apply GF].
    + intros. eapply rclo3_mon_gen; [eapply PR|..].
      * intros. right. apply PR0.
      * intros. apply PR0.
Qed.

Lemma compat3_compatible'
      clo (COM: compatible3 gf clo):
  compatible'3 clo.
Proof.
  destruct COM. econstructor; [apply compat3_mon0|].
  intros. split.
  - eapply compat3_mon0; intros; [apply PR| apply PR0].
  - apply compat3_compat0.
    eapply compat3_mon0; intros; [apply PR| apply PR0].
Qed.

Lemma compatible'3_companion
      clo (RES: compatible'3 clo):
  clo <4= cpn3 gf.
Proof.
  assert (MON: monotone3 gf'3).
  { econstructor. apply LE, IN.
    eapply gf_mon, LE. apply IN.
  }
  assert (CPN: clo <4= cpn3 gf'3).
  { intros. econstructor. apply RES. apply PR.
  }
  intros. apply CPN in PR.
  econstructor; [|apply PR].
  econstructor; [apply cpn3_mon|]; intros.
  assert (PR1: cpn3 gf'3 (gf r) <3= cpn3 gf'3 (gf'3 (cpn3 gf r))).
  { intros. eapply cpn3_mon. apply PR1.
    intros. assert (TMP: gf (cpn3 gf r) <3= (cpn3 gf r /3\ gf (cpn3 gf r))).
    { split; [apply cpn3_step; [apply gf_mon|]|]; assumption. }
    apply TMP.
    eapply gf_mon. apply PR2. intros. apply cpn3_base; assumption.
  }
  apply PR1 in PR0. clear PR1. 
  eapply compat3_compat with (gf:=gf'3) in PR0; [|apply cpn3_compat, MON].
  eapply gf_mon; [apply PR0|].
  intros. eapply cpn3_cpn; [apply MON|].
  eapply cpn3_mon; [apply PR1|].
  intros. econstructor; [|apply PR2].
  apply compat3_compatible', cpn3_compat, gf_mon.
Qed.

Lemma wrespect3_companion
      clo (RES: wrespectful3 clo):
  clo <4= cpn3 gf.
Proof.
  intros. eapply wrespect3_compatible' in RES.
  eapply (@compatible'3_companion (rclo3 clo)) in RES; [apply RES|].
  eapply rclo3_clo_base, PR.
Qed.

Lemma prespect3_companion
      clo (RES: prespectful3 clo):
  clo <4= cpn3 gf.
Proof.
  intros. eapply compatible'3_companion. apply prespect3_compatible'. apply RES.
  right. right. apply PR.
Qed.

Lemma grespect3_companion
      clo (RES: grespectful3 clo):
  clo <4= cpn3 gf.
Proof.
  intros. eapply grespect3_compatible' in RES.
  eapply (@compatible'3_companion (rclo3 (clo \4/ cpn3 gf))); [apply RES|].
  apply rclo3_clo_base. left. apply PR.
Qed.

Lemma wrespect3_uclo
      clo (RES: wrespectful3 clo):
  clo <4= gupaco3 gf (cpn3 gf).
Proof.
  intros. eapply gpaco3_clo, wrespect3_companion, PR. apply RES.
Qed.

Lemma prespect3_uclo
      clo (RES: prespectful3 clo):
  clo <4= gupaco3 gf (cpn3 gf).
Proof.
  intros. eapply gpaco3_clo, prespect3_companion, PR. apply RES.
Qed.

Lemma grespect3_uclo
      clo (RES: grespectful3 clo):
  clo <4= gupaco3 gf (cpn3 gf).
Proof.
  intros. eapply gpaco3_clo, grespect3_companion, PR. apply RES.
Qed.

End Respectful.

End GeneralizedPaco3.

Hint Resolve gpaco3_def_mon : paco.
Hint Unfold gupaco3 : paco.
Hint Resolve gpaco3_base : paco.
Hint Resolve gpaco3_step : paco.
Hint Resolve gpaco3_final : paco.
Hint Resolve rclo3_base : paco.
Hint Constructors gpaco3 : paco.
Hint Resolve wrespect3_uclo : paco.
Hint Resolve prespect3_uclo : paco.
