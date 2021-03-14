Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco2 pacotac.
Set Implicit Arguments.

Section GeneralizedPaco2.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.

Local Notation rel := (rel2 T0 T1).

Section RClo.

Inductive rclo2 (clo: rel->rel) (r: rel): rel :=
| rclo2_base
    x0 x1
    (IN: r x0 x1):
    @rclo2 clo r x0 x1
| rclo2_clo'
    r' x0 x1
    (LE: r' <2= rclo2 clo r)
    (IN: clo r' x0 x1):
    @rclo2 clo r x0 x1
.           

Lemma rclo2_mon_gen clo clo' r r' x0 x1
      (IN: @rclo2 clo r x0 x1)
      (LEclo: clo <3= clo')
      (LEr: r <2= r') :
  @rclo2 clo' r' x0 x1.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo2_mon clo:
  monotone2 (rclo2 clo).
Proof.
  repeat intro. eapply rclo2_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo2_clo clo r:
  clo (rclo2 clo r) <2= rclo2 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo2_clo_base clo r:
  clo r <2= rclo2 clo r.
Proof.
  intros. eapply rclo2_clo', PR.
  intros. apply rclo2_base, PR0.
Qed.

Lemma rclo2_rclo clo r:
  rclo2 clo (rclo2 clo r) <2= rclo2 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo2_compose clo r:
  rclo2 (rclo2 clo) r <2= rclo2 clo r.
Proof.
  intros. induction PR.
  - apply rclo2_base, IN.
  - apply rclo2_rclo.
    eapply rclo2_mon; [apply IN|apply H].
Qed.

End RClo.  

Section Main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone2 gf.

Variant gpaco2 clo r rg x0 x1 : Prop :=
| gpaco2_intro (IN: @rclo2 clo (paco2 (compose gf (rclo2 clo)) (rg \2/ r) \2/ r) x0 x1)
.

Definition gupaco2 clo r := gpaco2 clo r r.

Lemma gpaco2_def_mon clo : monotone2 (compose gf (rclo2 clo)).
Proof.
  eapply monotone2_compose. apply gf_mon. apply rclo2_mon.
Qed.

Hint Resolve gpaco2_def_mon : paco.

Lemma gpaco2_mon clo r r' rg rg' x0 x1
      (IN: @gpaco2 clo r rg x0 x1)
      (LEr: r <2= r')
      (LErg: rg <2= rg'):
  @gpaco2 clo r' rg' x0 x1.
Proof.
  destruct IN. econstructor.
  eapply rclo2_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco2_mon. apply H.
  intros. destruct PR.
  - left. apply LErg, H0.
  - right. apply LEr, H0.
Qed.

Lemma gupaco2_mon clo r r' x0 x1
      (IN: @gupaco2 clo r x0 x1)
      (LEr: r <2= r'):
  @gupaco2 clo r' x0 x1.
Proof.
  eapply gpaco2_mon. apply IN. apply LEr. apply LEr.
Qed.

Lemma gpaco2_base clo r rg: r <2= gpaco2 clo r rg.
Proof.
  econstructor. apply rclo2_base. right. apply PR.
Qed.

Lemma gpaco2_gen_guard  clo r rg:
  gpaco2 clo r (rg \2/ r) <2= gpaco2 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  eapply rclo2_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco2_mon_gen; intros. apply H. apply PR.
  destruct PR. apply H0. right. apply H0.
Qed.

Lemma gpaco2_rclo clo r rg:
  rclo2 clo r <2= gpaco2 clo r rg.
Proof.
  intros. econstructor.
  eapply rclo2_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco2_clo clo r rg:
  clo r <2= gpaco2 clo r rg.
Proof.
  intros. apply gpaco2_rclo. eapply rclo2_clo_base, PR.
Qed.

Lemma gpaco2_gen_rclo clo r rg:
  gpaco2 (rclo2 clo) r rg <2= gpaco2 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  apply rclo2_compose.
  eapply rclo2_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco2_mon_gen; intros; [apply H| |apply PR].
  eapply gf_mon, rclo2_compose. apply PR.
Qed.

Lemma gpaco2_step_gen clo r rg:
  gf (gpaco2 clo (rg \2/ r) (rg \2/ r)) <2= gpaco2 clo r rg.
Proof.
  intros. econstructor. apply rclo2_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo2_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco2_mon. apply H. intros. destruct PR0; apply H0.
  - right. apply H.
Qed.

Lemma gpaco2_step clo r rg:
  gf (gpaco2 clo rg rg) <2= gpaco2 clo r rg.
Proof.
  intros. apply gpaco2_step_gen.
  eapply gf_mon. apply PR. intros.
  eapply gpaco2_mon. apply PR0. left; apply PR1. left; apply PR1.
Qed.

Lemma gpaco2_final clo r rg:
  (r \2/ paco2 gf rg) <2= gpaco2 clo r rg.
Proof.
  intros. destruct PR. apply gpaco2_base, H.
  econstructor. apply rclo2_base.
  left. eapply paco2_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo2_base. apply PR0.
  - intros. left. apply PR.
Qed.

Lemma gpaco2_unfold clo r rg:
  gpaco2 clo r rg <2= rclo2 clo (gf (gupaco2 clo (rg \2/ r)) \2/ r).
Proof.
  intros. destruct PR.
  eapply rclo2_mon. apply IN.
  intros. destruct PR; cycle 1. right; apply H.
  left. _punfold H; [|apply gpaco2_def_mon].
  eapply gf_mon. apply H.
  intros. econstructor.
  eapply rclo2_mon. apply PR.
  intros. destruct PR0; cycle 1. right. apply H0.
  left. eapply paco2_mon. apply H0.
  intros. left. apply PR0.
Qed.
  
Lemma gpaco2_cofix clo r rg 
      l (OBG: forall rr (INC: rg <2= rr) (CIH: l <2= rr), l <2= gpaco2 clo r rr):
  l <2= gpaco2 clo r rg.
Proof.
  assert (IN: l <2= gpaco2 clo r (rg \2/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo2_mon. apply IN0.
  clear x0 x1 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply gpaco2_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo2_rclo. eapply rclo2_mon. apply PR.
  intros. destruct PR0.
  - apply rclo2_base. right. apply CIH. apply H.
  - destruct H; [destruct H|].
    + apply rclo2_base. right. apply CIH0. left. apply H.
    + apply IN in H. destruct H.
      eapply rclo2_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. right. apply H.
    + apply rclo2_base. right. apply CIH0. right. apply H.
Qed.

Lemma gpaco2_gupaco clo r rg:
  gupaco2 clo (gpaco2 clo r rg) <2= gpaco2 clo r rg.
Proof.
  eapply gpaco2_cofix.
  intros. destruct PR. econstructor.
  apply rclo2_rclo. eapply rclo2_mon. apply IN.
  intros. destruct PR.
  - apply rclo2_base. left.
    eapply paco2_mon. apply H.
    intros. left; apply CIH.
    econstructor. apply rclo2_base. right.
    destruct PR; apply H0.
  - destruct H. eapply rclo2_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco2_mon. apply H.
    intros. destruct PR.
    + left. apply INC. apply H0.
    + right. apply H0.
Qed.

Lemma gpaco2_gpaco clo r rg:
  gpaco2 clo (gpaco2 clo r rg) (gupaco2 clo (rg \2/ r)) <2= gpaco2 clo r rg.
Proof.
  intros. apply gpaco2_unfold in PR.
  econstructor. apply rclo2_rclo. eapply rclo2_mon. apply PR. clear x0 x1 PR. intros.
  destruct PR; [|destruct H; apply IN].
  apply rclo2_base. left. pstep.
  eapply gf_mon. apply H. clear x0 x1 H. intros.
  cut (@gupaco2 clo (rg \2/ r) x0 x1).
  { intros. destruct H. eapply rclo2_mon. apply IN. intros.
    destruct PR0; [|right; apply H].
    left. eapply paco2_mon. apply H. intros. destruct PR0; apply H0.
  }
  apply gpaco2_gupaco. eapply gupaco2_mon. apply PR. intros.
  destruct PR0; [apply H|].
  eapply gpaco2_mon; [apply H|right|left]; intros; apply PR0.
Qed.

Lemma gpaco2_uclo uclo clo r rg 
      (LEclo: uclo <3= gupaco2 clo) :
  uclo (gpaco2 clo r rg) <2= gpaco2 clo r rg.
Proof.
  intros. apply gpaco2_gupaco. apply LEclo, PR.
Qed.

Lemma gpaco2_weaken  clo r rg:
  gpaco2 (gupaco2 clo) r rg <2= gpaco2 clo r rg.
Proof.
  intros. apply gpaco2_unfold in PR.
  induction PR.
  - destruct IN; cycle 1. apply gpaco2_base, H.
    apply gpaco2_step_gen. eapply gf_mon. apply H.
    clear x0 x1 H.
    eapply gpaco2_cofix. intros.
    apply gpaco2_unfold in PR.
    induction PR.
    + destruct IN; cycle 1. apply gpaco2_base, H.
      apply gpaco2_step. eapply gf_mon. apply H.
      intros. apply gpaco2_base. apply CIH.
      eapply gupaco2_mon. apply PR.
      intros. destruct PR0; apply H0.
    + apply gpaco2_gupaco.
      eapply gupaco2_mon. apply IN. apply H.
  - apply gpaco2_gupaco.
    eapply gupaco2_mon. apply IN. apply H.
Qed.

End Main.

Hint Resolve gpaco2_def_mon : paco.

Section GeneralMonotonicity.

Variable gf: rel -> rel.
  
Lemma gpaco2_mon_gen (gf' clo clo': rel -> rel) x0 x1 r r' rg rg'
      (IN: @gpaco2 gf clo r rg x0 x1)
      (gf_mon: monotone2 gf)
      (LEgf: gf <3= gf')
      (LEclo: clo <3= clo')
      (LEr: r <2= r')
      (LErg: rg <2= rg') :
  @gpaco2 gf' clo' r' rg' x0 x1.
Proof.
  eapply gpaco2_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo2_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco2_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply gf_mon. apply PR.
    intros. eapply rclo2_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma gpaco2_mon_bot (gf' clo clo': rel -> rel) x0 x1 r' rg'
      (IN: @gpaco2 gf clo bot2 bot2 x0 x1)
      (gf_mon: monotone2 gf)
      (LEgf: gf <3= gf')
      (LEclo: clo <3= clo'):
  @gpaco2 gf' clo' r' rg' x0 x1.
Proof.
  eapply gpaco2_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco2_mon_gen (gf' clo clo': rel -> rel) x0 x1 r r'
      (IN: @gupaco2 gf clo r x0 x1)
      (gf_mon: monotone2 gf)
      (LEgf: gf <3= gf')
      (LEclo: clo <3= clo')
      (LEr: r <2= r'):
  @gupaco2 gf' clo' r' x0 x1.
Proof.
  eapply gpaco2_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. apply LEr. apply LEr.
Qed.

End GeneralMonotonicity.

Section Compatibility.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone2 gf.

Structure compatible2 (clo: rel -> rel) : Prop :=
  compat2_intro {
      compat2_mon: monotone2 clo;
      compat2_compat : forall r,
          clo (gf r) <2= gf (clo r);
    }.

Structure wcompatible2 clo : Prop :=
  wcompat2_intro {
      wcompat2_mon: monotone2 clo;
      wcompat2_wcompat : forall r,
          clo (gf r) <2= gf (gupaco2 gf clo r);
    }.

Lemma rclo2_dist clo
      (MON: monotone2 clo)
      (DIST: forall r1 r2, clo (r1 \2/ r2) <2= (clo r1 \2/ clo r2)):
  forall r1 r2, rclo2 clo (r1 \2/ r2) <2= (rclo2 clo r1 \2/ rclo2 clo r2).
Proof.
  intros. induction PR.
  + destruct IN; [left|right]; apply rclo2_base, H.
  + assert (REL: clo (rclo2 clo r1 \2/ rclo2 clo r2) x0 x1).
    { eapply MON. apply IN. apply H. }
    apply DIST in REL. destruct REL; [left|right]; apply rclo2_clo, H0.
Qed.

Lemma rclo2_compat clo
      (COM: compatible2 clo):
  compatible2 (rclo2 clo).
Proof.
  econstructor.
  - apply rclo2_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo2_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo2_clo. apply PR.
Qed.

Lemma rclo2_wcompat clo
      (COM: wcompatible2 clo):
  wcompatible2 (rclo2 clo).
Proof.
  econstructor.
  - apply rclo2_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. apply gpaco2_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply gpaco2_gupaco. apply gf_mon.
        eapply gupaco2_mon_gen; intros; [apply PR|apply gf_mon|apply PR0| |apply PR0].
        apply rclo2_clo_base, PR0.
Qed.

Lemma compat2_wcompat clo
      (CMP: compatible2 clo):
  wcompatible2 clo.
Proof.
  econstructor. apply CMP.
  intros. apply CMP in PR.
  eapply gf_mon. apply PR.
  intros. apply gpaco2_clo, PR0. 
Qed.

Lemma wcompat2_compat clo
      (WCMP: wcompatible2 clo) :
  compatible2 (gupaco2 gf clo).
Proof.
  econstructor.
  { red; intros. eapply gpaco2_mon. apply IN. apply LE. apply LE. }

  intros. apply gpaco2_unfold in PR; [|apply gf_mon].
  induction PR.
  - destruct IN; cycle 1.
    + eapply gf_mon. apply H.
      intros. apply gpaco2_base, PR.
    + eapply gf_mon. apply H.
      intros. apply gpaco2_gupaco. apply gf_mon.
      eapply gupaco2_mon. apply PR.
      intros. apply gpaco2_step. apply gf_mon.
      eapply gf_mon. destruct PR0 as [X|X]; apply X.
      intros. apply gpaco2_base, PR1.
  - eapply gf_mon, gpaco2_gupaco, gf_mon.
    apply WCMP. eapply WCMP. apply IN.
    intros. apply H, PR.
Qed.

Lemma wcompat2_union clo1 clo2
      (WCMP1: wcompatible2 clo1)
      (WCMP2: wcompatible2 clo2):
  wcompatible2 (clo1 \3/ clo2).
Proof.
  econstructor.
  - apply monotone2_union. apply WCMP1. apply WCMP2.
  - intros. destruct PR.
    + apply WCMP1 in H. eapply gf_mon. apply H.
      intros. eapply gupaco2_mon_gen. apply PR. apply gf_mon. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco2_mon_gen. apply PR. apply gf_mon.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
Qed.

End Compatibility.

Section Soundness.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone2 gf.

Lemma gpaco2_compat_init clo
      (CMP: compatible2 gf clo):
  gpaco2 gf clo bot2 bot2 <2= paco2 gf bot2.
Proof.
  intros. destruct PR. revert x0 x1 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo2_rclo, PR]. 
  apply compat2_compat with (gf:=gf). apply rclo2_compat. apply gf_mon. apply CMP.
  eapply rclo2_mon. apply IN.
  intros. destruct PR; [|contradiction]. _punfold H; [..|apply gpaco2_def_mon, gf_mon].
  eapply gpaco2_def_mon. apply gf_mon. apply H.
  intros. destruct PR; [|destruct H0; contradiction]. left. apply H0.
Qed.

Lemma gpaco2_init clo
      (WCMP: wcompatible2 gf clo):
  gpaco2 gf clo bot2 bot2 <2= paco2 gf bot2.
Proof.
  intros. eapply gpaco2_compat_init.
  - apply wcompat2_compat, WCMP. apply gf_mon.
  - eapply gpaco2_mon_bot. apply PR. apply gf_mon. intros; apply PR0.
    intros. apply gpaco2_clo, PR0.
Qed.

Lemma gpaco2_unfold_bot clo
      (WCMP: wcompatible2 gf clo):
  gpaco2 gf clo bot2 bot2 <2= gf (gpaco2 gf clo bot2 bot2).
Proof.
  intros. apply gpaco2_init in PR; [|apply WCMP].
  _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. destruct PR0; [|contradiction]. apply gpaco2_final. apply gf_mon. right. apply H.
Qed.

End Soundness.

Section Distributivity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone2 gf.

Lemma gpaco2_dist clo r rg
      (CMP: wcompatible2 gf clo)
      (DIST: forall r1 r2, clo (r1 \2/ r2) <2= (clo r1 \2/ clo r2)):
  gpaco2 gf clo r rg <2= (paco2 gf (rclo2 clo (rg \2/ r)) \2/ rclo2 clo r).
Proof.
  intros. apply gpaco2_unfold in PR; [|apply gf_mon].
  apply rclo2_dist in PR; [|apply CMP|apply DIST].
  destruct PR; [|right; apply H].
  left. revert x0 x1 H.
  pcofix CIH; intros.
  apply rclo2_wcompat in H0; [|apply gf_mon|apply CMP].
  pstep. eapply gf_mon. apply H0. intros.
  apply gpaco2_unfold in PR; [|apply gf_mon].
  apply rclo2_compose in PR.
  apply rclo2_dist in PR; [|apply CMP|apply DIST].
  destruct PR.
  - right. apply CIH.
    eapply rclo2_mon. apply H. intros.
    eapply gf_mon. apply PR. intros.
    apply gpaco2_gupaco. apply gf_mon.
    apply gpaco2_gen_rclo. apply gf_mon.
    eapply gupaco2_mon. apply PR0. intros.
    destruct PR1; apply H1.
  - assert (REL: @rclo2 clo (rclo2 clo (gf (gupaco2 gf clo ((rg \2/ r) \2/ (rg \2/ r))) \2/ (rg \2/ r))) x0 x1).
    { eapply rclo2_mon. apply H. intros. apply gpaco2_unfold in PR. apply PR. apply gf_mon. }
    apply rclo2_rclo in REL.
    apply rclo2_dist in REL; [|apply CMP|apply DIST].
    right. destruct REL; cycle 1.
    + apply CIH0, H1.
    + apply CIH.
      eapply rclo2_mon. apply H1. intros.
      eapply gf_mon. apply PR. intros.
      eapply gupaco2_mon. apply PR0. intros.
      destruct PR1; apply H2.
Qed.

Lemma gpaco2_dist_reverse clo r rg:
  (paco2 gf (rclo2 clo (rg \2/ r)) \2/ rclo2 clo r) <2= gpaco2 gf clo r rg.
Proof.
  intros. destruct PR; cycle 1.
  - eapply gpaco2_rclo. apply H.
  - econstructor. apply rclo2_base. left.
    revert x0 x1 H. pcofix CIH; intros.
    _punfold H0; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H0. intros.
    destruct PR.
    + apply rclo2_base. right. apply CIH, H.
    + eapply rclo2_mon. apply H. intros.
      right. apply CIH0. apply PR.
Qed.

End Distributivity.

Section Companion.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone2 gf.

Inductive cpn2 (r: rel) x0 x1 : Prop :=
| cpn2_intro
    clo
    (COM: compatible2 gf clo)
    (CLO: clo r x0 x1)
.

Lemma cpn2_mon: monotone2 cpn2.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat2_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn2_greatest: forall clo (COM: compatible2 gf clo), clo <3= cpn2.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn2_compat: compatible2 gf cpn2.
Proof.
  econstructor; [apply cpn2_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat2_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn2_wcompat: wcompatible2 gf cpn2.
Proof. apply compat2_wcompat, cpn2_compat. apply gf_mon. Qed.

Lemma cpn2_gupaco:
  gupaco2 gf cpn2 <3= cpn2.
Proof.
  intros. eapply cpn2_greatest, PR. apply wcompat2_compat. apply gf_mon. apply cpn2_wcompat.
Qed.

Lemma cpn2_cpn r:
  cpn2 (cpn2 r) <2= cpn2 r.
Proof.
  intros. apply cpn2_gupaco, gpaco2_gupaco, gpaco2_clo. apply gf_mon.
  eapply cpn2_mon, gpaco2_clo. apply PR.
Qed.

Lemma cpn2_base r:
  r <2= cpn2 r.
Proof.
  intros. apply cpn2_gupaco. apply gpaco2_base, PR.
Qed.

Lemma cpn2_clo
      r clo (LE: clo <3= cpn2):
  clo (cpn2 r) <2= cpn2 r.
Proof.
  intros. apply cpn2_cpn, LE, PR.
Qed.

Lemma cpn2_step r:
  gf (cpn2 r) <2= cpn2 r.
Proof.
  intros. apply cpn2_gupaco. apply gpaco2_step. apply gf_mon.
  eapply gf_mon, gpaco2_clo. apply PR.
Qed.

Lemma cpn2_uclo uclo
      (MON: monotone2 uclo)
      (WCOM: forall r, uclo (gf r) <2= gf (gupaco2 gf (uclo \3/ cpn2) r)):
  uclo <3= gupaco2 gf cpn2.
Proof.
  intros. apply gpaco2_clo.
  exists (gupaco2 gf (uclo \3/ cpn2)).
  - apply wcompat2_compat. apply gf_mon.
    econstructor.
    + apply monotone2_union. apply MON. apply cpn2_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat2_compat with (gf:=gf) in H; [| apply cpn2_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco2_clo. right. apply PR0.
  - apply gpaco2_clo. left. apply PR.
Qed.

End Companion.

Section Respectful.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone2 gf.

Structure wrespectful2 (clo: rel -> rel) : Prop :=
  wrespect2_intro {
      wrespect2_mon: monotone2 clo;
      wrespect2_respect :
        forall l r
               (LE: l <2= r)
               (GF: l <2= gf r),
        clo l <2= gf (rclo2 clo r);
    }.

Structure prespectful2 (clo: rel -> rel) : Prop :=
  prespect2_intro {
      prespect2_mon: monotone2 clo;
      prespect2_respect :
        forall l r
               (LE: l <2= r)
               (GF: l <2= gf r),
        clo l <2= paco2 gf (r \2/ clo r);
    }.

Structure grespectful2 (clo: rel -> rel) : Prop :=
  grespect2_intro {
      grespect2_mon: monotone2 clo;
      grespect2_respect :
        forall l r
               (LE: l <2= r)
               (GF: l <2= gf r),
        clo l <2= rclo2 (cpn2 gf) (gf (rclo2 (clo \3/ gupaco2 gf (cpn2 gf)) r));
    }.

Definition gf'2 := id /3\ gf.

Definition compatible'2 := compatible2 gf'2.

Lemma wrespect2_compatible'
      clo (RES: wrespectful2 clo):
  compatible'2 (rclo2 clo).
Proof.
  intros. econstructor. apply rclo2_mon.
  intros. destruct RES. split.
  { eapply rclo2_mon. apply PR. intros. apply PR0. }
  induction PR; intros.
  - eapply gf_mon. apply IN.
    intros. apply rclo2_base, PR.
  - eapply gf_mon.
    + eapply wrespect2_respect0; [|apply H|apply IN].
      intros. eapply rclo2_mon; intros; [apply LE, PR|apply PR0].
    + intros. apply rclo2_rclo, PR.
Qed.

Lemma prespect2_compatible'
      clo (RES: prespectful2 clo):
  compatible'2 (fun r => upaco2 gf (r \2/ clo r)).
Proof.
  econstructor.
  { red; intros. eapply upaco2_mon. apply IN.
    intros. destruct PR.
    - left. apply LE, H.
    - right. eapply RES. apply H. intros. apply LE, PR. }

  intros r.
  assert (LEM: (gf'2 r \2/ clo (gf'2 r)) <2= (r \2/ clo r)).
  { intros. destruct PR.
    - left. apply H.
    - right. eapply RES. apply H. intros. apply PR.
  }

  intros. destruct PR.
  - split.
    + left. eapply paco2_mon. apply H. apply LEM.
    + apply paco2_unfold; [apply gf_mon|].
      eapply paco2_mon. apply H. apply LEM.
  - split.
    + right. apply LEM. apply H.
    + destruct H.
      * eapply gf_mon. apply H. intros. right. left. apply PR.
      * apply paco2_unfold; [apply gf_mon|].
        eapply RES, H; intros; apply PR.
Qed.

Lemma grespect2_compatible'
      clo (RES: grespectful2 clo):
  compatible'2 (rclo2 (clo \3/ cpn2 gf)).
Proof.
  apply wrespect2_compatible'.
  econstructor.
  { red; intros. destruct IN.
    - left. eapply RES; [apply H|]. apply LE.
    - right. eapply cpn2_mon; [apply H|]. apply LE. }
  intros. destruct PR.
  - eapply RES.(grespect2_respect) in H; [|apply LE|apply GF].
    apply (@compat2_compat gf (rclo2 (cpn2 gf))) in H.
    2: { apply rclo2_compat; [apply gf_mon|]. apply cpn2_compat. apply gf_mon. }
    eapply gf_mon; [apply H|].
    intros. apply rclo2_clo. right.
    exists (rclo2 (cpn2 gf)).
    { apply rclo2_compat; [apply gf_mon|]. apply cpn2_compat. apply gf_mon. }
    eapply rclo2_mon; [eapply PR|].
    intros. eapply rclo2_mon_gen; [eapply PR0|..].
    + intros. destruct PR1.
      * left. apply H0.
      * right. apply cpn2_gupaco; [apply gf_mon|apply H0].
    + intros. apply PR1.
  - eapply gf_mon.
    + apply (@compat2_compat gf (rclo2 (cpn2 gf))).
      { apply rclo2_compat; [apply gf_mon|]. apply cpn2_compat. apply gf_mon. }
      eapply rclo2_clo_base. eapply cpn2_mon; [apply H|apply GF].
    + intros. eapply rclo2_mon_gen; [eapply PR|..].
      * intros. right. apply PR0.
      * intros. apply PR0.
Qed.

Lemma compat2_compatible'
      clo (COM: compatible2 gf clo):
  compatible'2 clo.
Proof.
  destruct COM. econstructor; [apply compat2_mon0|].
  intros. split.
  - eapply compat2_mon0; intros; [apply PR| apply PR0].
  - apply compat2_compat0.
    eapply compat2_mon0; intros; [apply PR| apply PR0].
Qed.

Lemma compatible'2_companion
      clo (RES: compatible'2 clo):
  clo <3= cpn2 gf.
Proof.
  assert (MON: monotone2 gf'2).
  { econstructor. apply LE, IN.
    eapply gf_mon, LE. apply IN.
  }
  assert (CPN: clo <3= cpn2 gf'2).
  { intros. econstructor. apply RES. apply PR.
  }
  intros. apply CPN in PR.
  econstructor; [|apply PR].
  econstructor; [apply cpn2_mon|]; intros.
  assert (PR1: cpn2 gf'2 (gf r) <2= cpn2 gf'2 (gf'2 (cpn2 gf r))).
  { intros. eapply cpn2_mon. apply PR1.
    intros. assert (TMP: gf (cpn2 gf r) <2= (cpn2 gf r /2\ gf (cpn2 gf r))).
    { split; [apply cpn2_step; [apply gf_mon|]|]; assumption. }
    apply TMP.
    eapply gf_mon. apply PR2. intros. apply cpn2_base; assumption.
  }
  apply PR1 in PR0. clear PR1. 
  eapply compat2_compat with (gf:=gf'2) in PR0; [|apply cpn2_compat, MON].
  eapply gf_mon; [apply PR0|].
  intros. eapply cpn2_cpn; [apply MON|].
  eapply cpn2_mon; [apply PR1|].
  intros. econstructor; [|apply PR2].
  apply compat2_compatible', cpn2_compat, gf_mon.
Qed.

Lemma wrespect2_companion
      clo (RES: wrespectful2 clo):
  clo <3= cpn2 gf.
Proof.
  intros. eapply wrespect2_compatible' in RES.
  eapply (@compatible'2_companion (rclo2 clo)) in RES; [apply RES|].
  eapply rclo2_clo_base, PR.
Qed.

Lemma prespect2_companion
      clo (RES: prespectful2 clo):
  clo <3= cpn2 gf.
Proof.
  intros. eapply compatible'2_companion. apply prespect2_compatible'. apply RES.
  right. right. apply PR.
Qed.

Lemma grespect2_companion
      clo (RES: grespectful2 clo):
  clo <3= cpn2 gf.
Proof.
  intros. eapply grespect2_compatible' in RES.
  eapply (@compatible'2_companion (rclo2 (clo \3/ cpn2 gf))); [apply RES|].
  apply rclo2_clo_base. left. apply PR.
Qed.

Lemma wrespect2_uclo
      clo (RES: wrespectful2 clo):
  clo <3= gupaco2 gf (cpn2 gf).
Proof.
  intros. eapply gpaco2_clo, wrespect2_companion, PR. apply RES.
Qed.

Lemma prespect2_uclo
      clo (RES: prespectful2 clo):
  clo <3= gupaco2 gf (cpn2 gf).
Proof.
  intros. eapply gpaco2_clo, prespect2_companion, PR. apply RES.
Qed.

Lemma grespect2_uclo
      clo (RES: grespectful2 clo):
  clo <3= gupaco2 gf (cpn2 gf).
Proof.
  intros. eapply gpaco2_clo, grespect2_companion, PR. apply RES.
Qed.

End Respectful.

End GeneralizedPaco2.

Hint Resolve gpaco2_def_mon : paco.
Hint Unfold gupaco2 : paco.
Hint Resolve gpaco2_base : paco.
Hint Resolve gpaco2_step : paco.
Hint Resolve gpaco2_final : paco.
Hint Resolve rclo2_base : paco.
Hint Constructors gpaco2 : paco.
Hint Resolve wrespect2_uclo : paco.
Hint Resolve prespect2_uclo : paco.
