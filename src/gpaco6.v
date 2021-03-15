Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco6 pacotac.
Set Implicit Arguments.

Section GeneralizedPaco6.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.

Local Notation rel := (rel6 T0 T1 T2 T3 T4 T5).

Section RClo.

Inductive rclo6 (clo: rel->rel) (r: rel): rel :=
| rclo6_base
    x0 x1 x2 x3 x4 x5
    (IN: r x0 x1 x2 x3 x4 x5):
    @rclo6 clo r x0 x1 x2 x3 x4 x5
| rclo6_clo'
    r' x0 x1 x2 x3 x4 x5
    (LE: r' <6= rclo6 clo r)
    (IN: clo r' x0 x1 x2 x3 x4 x5):
    @rclo6 clo r x0 x1 x2 x3 x4 x5
.           

Lemma rclo6_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5
      (IN: @rclo6 clo r x0 x1 x2 x3 x4 x5)
      (LEclo: clo <7= clo')
      (LEr: r <6= r') :
  @rclo6 clo' r' x0 x1 x2 x3 x4 x5.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo6_mon clo:
  monotone6 (rclo6 clo).
Proof.
  repeat intro. eapply rclo6_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo6_clo clo r:
  clo (rclo6 clo r) <6= rclo6 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo6_clo_base clo r:
  clo r <6= rclo6 clo r.
Proof.
  intros. eapply rclo6_clo', PR.
  intros. apply rclo6_base, PR0.
Qed.

Lemma rclo6_rclo clo r:
  rclo6 clo (rclo6 clo r) <6= rclo6 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo6_compose clo r:
  rclo6 (rclo6 clo) r <6= rclo6 clo r.
Proof.
  intros. induction PR.
  - apply rclo6_base, IN.
  - apply rclo6_rclo.
    eapply rclo6_mon; [apply IN|apply H].
Qed.

End RClo.  

Section Main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone6 gf.

Variant gpaco6 clo r rg x0 x1 x2 x3 x4 x5 : Prop :=
| gpaco6_intro (IN: @rclo6 clo (paco6 (compose gf (rclo6 clo)) (rg \6/ r) \6/ r) x0 x1 x2 x3 x4 x5)
.

Definition gupaco6 clo r := gpaco6 clo r r.

Lemma gpaco6_def_mon clo : monotone6 (compose gf (rclo6 clo)).
Proof.
  eapply monotone6_compose. apply gf_mon. apply rclo6_mon.
Qed.

Hint Resolve gpaco6_def_mon : paco.

Lemma gpaco6_mon clo r r' rg rg' x0 x1 x2 x3 x4 x5
      (IN: @gpaco6 clo r rg x0 x1 x2 x3 x4 x5)
      (LEr: r <6= r')
      (LErg: rg <6= rg'):
  @gpaco6 clo r' rg' x0 x1 x2 x3 x4 x5.
Proof.
  destruct IN. econstructor.
  eapply rclo6_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco6_mon. apply H.
  intros. destruct PR.
  - left. apply LErg, H0.
  - right. apply LEr, H0.
Qed.

Lemma gupaco6_mon clo r r' x0 x1 x2 x3 x4 x5
      (IN: @gupaco6 clo r x0 x1 x2 x3 x4 x5)
      (LEr: r <6= r'):
  @gupaco6 clo r' x0 x1 x2 x3 x4 x5.
Proof.
  eapply gpaco6_mon. apply IN. apply LEr. apply LEr.
Qed.

Lemma gpaco6_base clo r rg: r <6= gpaco6 clo r rg.
Proof.
  econstructor. apply rclo6_base. right. apply PR.
Qed.

Lemma gpaco6_gen_guard  clo r rg:
  gpaco6 clo r (rg \6/ r) <6= gpaco6 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  eapply rclo6_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco6_mon_gen; intros. apply H. apply PR.
  destruct PR. apply H0. right. apply H0.
Qed.

Lemma gpaco6_rclo clo r rg:
  rclo6 clo r <6= gpaco6 clo r rg.
Proof.
  intros. econstructor.
  eapply rclo6_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco6_clo clo r rg:
  clo r <6= gpaco6 clo r rg.
Proof.
  intros. apply gpaco6_rclo. eapply rclo6_clo_base, PR.
Qed.

Lemma gpaco6_gen_rclo clo r rg:
  gpaco6 (rclo6 clo) r rg <6= gpaco6 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  apply rclo6_compose.
  eapply rclo6_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco6_mon_gen; intros; [apply H| |apply PR].
  eapply gf_mon, rclo6_compose. apply PR.
Qed.

Lemma gpaco6_step_gen clo r rg:
  gf (gpaco6 clo (rg \6/ r) (rg \6/ r)) <6= gpaco6 clo r rg.
Proof.
  intros. econstructor. apply rclo6_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo6_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco6_mon. apply H. intros. destruct PR0; apply H0.
  - right. apply H.
Qed.

Lemma gpaco6_step clo r rg:
  gf (gpaco6 clo rg rg) <6= gpaco6 clo r rg.
Proof.
  intros. apply gpaco6_step_gen.
  eapply gf_mon. apply PR. intros.
  eapply gpaco6_mon. apply PR0. left; apply PR1. left; apply PR1.
Qed.

Lemma gpaco6_final clo r rg:
  (r \6/ paco6 gf rg) <6= gpaco6 clo r rg.
Proof.
  intros. destruct PR. apply gpaco6_base, H.
  econstructor. apply rclo6_base.
  left. eapply paco6_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo6_base. apply PR0.
  - intros. left. apply PR.
Qed.

Lemma gpaco6_unfold clo r rg:
  gpaco6 clo r rg <6= rclo6 clo (gf (gupaco6 clo (rg \6/ r)) \6/ r).
Proof.
  intros. destruct PR.
  eapply rclo6_mon. apply IN.
  intros. destruct PR; cycle 1. right; apply H.
  left. _punfold H; [|apply gpaco6_def_mon].
  eapply gf_mon. apply H.
  intros. econstructor.
  eapply rclo6_mon. apply PR.
  intros. destruct PR0; cycle 1. right. apply H0.
  left. eapply paco6_mon. apply H0.
  intros. left. apply PR0.
Qed.
  
Lemma gpaco6_cofix clo r rg 
      l (OBG: forall rr (INC: rg <6= rr) (CIH: l <6= rr), l <6= gpaco6 clo r rr):
  l <6= gpaco6 clo r rg.
Proof.
  assert (IN: l <6= gpaco6 clo r (rg \6/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo6_mon. apply IN0.
  clear x0 x1 x2 x3 x4 x5 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply gpaco6_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo6_rclo. eapply rclo6_mon. apply PR.
  intros. destruct PR0.
  - apply rclo6_base. right. apply CIH. apply H.
  - destruct H; [destruct H|].
    + apply rclo6_base. right. apply CIH0. left. apply H.
    + apply IN in H. destruct H.
      eapply rclo6_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. right. apply H.
    + apply rclo6_base. right. apply CIH0. right. apply H.
Qed.

Lemma gpaco6_gupaco clo r rg:
  gupaco6 clo (gpaco6 clo r rg) <6= gpaco6 clo r rg.
Proof.
  eapply gpaco6_cofix.
  intros. destruct PR. econstructor.
  apply rclo6_rclo. eapply rclo6_mon. apply IN.
  intros. destruct PR.
  - apply rclo6_base. left.
    eapply paco6_mon. apply H.
    intros. left; apply CIH.
    econstructor. apply rclo6_base. right.
    destruct PR; apply H0.
  - destruct H. eapply rclo6_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco6_mon. apply H.
    intros. destruct PR.
    + left. apply INC. apply H0.
    + right. apply H0.
Qed.

Lemma gpaco6_gpaco clo r rg:
  gpaco6 clo (gpaco6 clo r rg) (gupaco6 clo (rg \6/ r)) <6= gpaco6 clo r rg.
Proof.
  intros. apply gpaco6_unfold in PR.
  econstructor. apply rclo6_rclo. eapply rclo6_mon. apply PR. clear x0 x1 x2 x3 x4 x5 PR. intros.
  destruct PR; [|destruct H; apply IN].
  apply rclo6_base. left. pstep.
  eapply gf_mon. apply H. clear x0 x1 x2 x3 x4 x5 H. intros.
  cut (@gupaco6 clo (rg \6/ r) x0 x1 x2 x3 x4 x5).
  { intros. destruct H. eapply rclo6_mon. apply IN. intros.
    destruct PR0; [|right; apply H].
    left. eapply paco6_mon. apply H. intros. destruct PR0; apply H0.
  }
  apply gpaco6_gupaco. eapply gupaco6_mon. apply PR. intros.
  destruct PR0; [apply H|].
  eapply gpaco6_mon; [apply H|right|left]; intros; apply PR0.
Qed.

Lemma gpaco6_uclo uclo clo r rg 
      (LEclo: uclo <7= gupaco6 clo) :
  uclo (gpaco6 clo r rg) <6= gpaco6 clo r rg.
Proof.
  intros. apply gpaco6_gupaco. apply LEclo, PR.
Qed.

Lemma gpaco6_weaken  clo r rg:
  gpaco6 (gupaco6 clo) r rg <6= gpaco6 clo r rg.
Proof.
  intros. apply gpaco6_unfold in PR.
  induction PR.
  - destruct IN; cycle 1. apply gpaco6_base, H.
    apply gpaco6_step_gen. eapply gf_mon. apply H.
    clear x0 x1 x2 x3 x4 x5 H.
    eapply gpaco6_cofix. intros.
    apply gpaco6_unfold in PR.
    induction PR.
    + destruct IN; cycle 1. apply gpaco6_base, H.
      apply gpaco6_step. eapply gf_mon. apply H.
      intros. apply gpaco6_base. apply CIH.
      eapply gupaco6_mon. apply PR.
      intros. destruct PR0; apply H0.
    + apply gpaco6_gupaco.
      eapply gupaco6_mon. apply IN. apply H.
  - apply gpaco6_gupaco.
    eapply gupaco6_mon. apply IN. apply H.
Qed.

End Main.

Hint Resolve gpaco6_def_mon : paco.

Section GeneralMonotonicity.

Variable gf: rel -> rel.
  
Lemma gpaco6_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 r r' rg rg'
      (IN: @gpaco6 gf clo r rg x0 x1 x2 x3 x4 x5)
      (gf_mon: monotone6 gf)
      (LEgf: gf <7= gf')
      (LEclo: clo <7= clo')
      (LEr: r <6= r')
      (LErg: rg <6= rg') :
  @gpaco6 gf' clo' r' rg' x0 x1 x2 x3 x4 x5.
Proof.
  eapply gpaco6_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo6_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco6_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply gf_mon. apply PR.
    intros. eapply rclo6_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma gpaco6_mon_bot (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 r' rg'
      (IN: @gpaco6 gf clo bot6 bot6 x0 x1 x2 x3 x4 x5)
      (gf_mon: monotone6 gf)
      (LEgf: gf <7= gf')
      (LEclo: clo <7= clo'):
  @gpaco6 gf' clo' r' rg' x0 x1 x2 x3 x4 x5.
Proof.
  eapply gpaco6_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco6_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 r r'
      (IN: @gupaco6 gf clo r x0 x1 x2 x3 x4 x5)
      (gf_mon: monotone6 gf)
      (LEgf: gf <7= gf')
      (LEclo: clo <7= clo')
      (LEr: r <6= r'):
  @gupaco6 gf' clo' r' x0 x1 x2 x3 x4 x5.
Proof.
  eapply gpaco6_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. apply LEr. apply LEr.
Qed.

End GeneralMonotonicity.

Section Compatibility.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone6 gf.

Structure compatible6 (clo: rel -> rel) : Prop :=
  compat6_intro {
      compat6_mon: monotone6 clo;
      compat6_compat : forall r,
          clo (gf r) <6= gf (clo r);
    }.

Structure wcompatible6 clo : Prop :=
  wcompat6_intro {
      wcompat6_mon: monotone6 clo;
      wcompat6_wcompat : forall r,
          clo (gf r) <6= gf (gupaco6 gf clo r);
    }.

Lemma rclo6_dist clo
      (MON: monotone6 clo)
      (DIST: forall r1 r2, clo (r1 \6/ r2) <6= (clo r1 \6/ clo r2)):
  forall r1 r2, rclo6 clo (r1 \6/ r2) <6= (rclo6 clo r1 \6/ rclo6 clo r2).
Proof.
  intros. induction PR.
  + destruct IN; [left|right]; apply rclo6_base, H.
  + assert (REL: clo (rclo6 clo r1 \6/ rclo6 clo r2) x0 x1 x2 x3 x4 x5).
    { eapply MON. apply IN. apply H. }
    apply DIST in REL. destruct REL; [left|right]; apply rclo6_clo, H0.
Qed.

Lemma rclo6_compat clo
      (COM: compatible6 clo):
  compatible6 (rclo6 clo).
Proof.
  econstructor.
  - apply rclo6_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo6_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo6_clo. apply PR.
Qed.

Lemma rclo6_wcompat clo
      (COM: wcompatible6 clo):
  wcompatible6 (rclo6 clo).
Proof.
  econstructor.
  - apply rclo6_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. apply gpaco6_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply gpaco6_gupaco. apply gf_mon.
        eapply gupaco6_mon_gen; intros; [apply PR|apply gf_mon|apply PR0| |apply PR0].
        apply rclo6_clo_base, PR0.
Qed.

Lemma compat6_wcompat clo
      (CMP: compatible6 clo):
  wcompatible6 clo.
Proof.
  econstructor. apply CMP.
  intros. apply CMP in PR.
  eapply gf_mon. apply PR.
  intros. apply gpaco6_clo, PR0. 
Qed.

Lemma wcompat6_compat clo
      (WCMP: wcompatible6 clo) :
  compatible6 (gupaco6 gf clo).
Proof.
  econstructor.
  { red; intros. eapply gpaco6_mon. apply IN. apply LE. apply LE. }

  intros. apply gpaco6_unfold in PR; [|apply gf_mon].
  induction PR.
  - destruct IN; cycle 1.
    + eapply gf_mon. apply H.
      intros. apply gpaco6_base, PR.
    + eapply gf_mon. apply H.
      intros. apply gpaco6_gupaco. apply gf_mon.
      eapply gupaco6_mon. apply PR.
      intros. apply gpaco6_step. apply gf_mon.
      eapply gf_mon. destruct PR0 as [X|X]; apply X.
      intros. apply gpaco6_base, PR1.
  - eapply gf_mon, gpaco6_gupaco, gf_mon.
    apply WCMP. eapply WCMP. apply IN.
    intros. apply H, PR.
Qed.

Lemma wcompat6_union clo1 clo2
      (WCMP1: wcompatible6 clo1)
      (WCMP2: wcompatible6 clo2):
  wcompatible6 (clo1 \7/ clo2).
Proof.
  econstructor.
  - apply monotone6_union. apply WCMP1. apply WCMP2.
  - intros. destruct PR.
    + apply WCMP1 in H. eapply gf_mon. apply H.
      intros. eapply gupaco6_mon_gen. apply PR. apply gf_mon. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco6_mon_gen. apply PR. apply gf_mon.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
Qed.

End Compatibility.

Section Soundness.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone6 gf.

Lemma gpaco6_compat_init clo
      (CMP: compatible6 gf clo):
  gpaco6 gf clo bot6 bot6 <6= paco6 gf bot6.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 x5 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo6_rclo, PR]. 
  apply compat6_compat with (gf:=gf). apply rclo6_compat. apply gf_mon. apply CMP.
  eapply rclo6_mon. apply IN.
  intros. destruct PR; [|contradiction]. _punfold H; [..|apply gpaco6_def_mon, gf_mon].
  eapply gpaco6_def_mon. apply gf_mon. apply H.
  intros. destruct PR; [|destruct H0; contradiction]. left. apply H0.
Qed.

Lemma gpaco6_init clo
      (WCMP: wcompatible6 gf clo):
  gpaco6 gf clo bot6 bot6 <6= paco6 gf bot6.
Proof.
  intros. eapply gpaco6_compat_init.
  - apply wcompat6_compat, WCMP. apply gf_mon.
  - eapply gpaco6_mon_bot. apply PR. apply gf_mon. intros; apply PR0.
    intros. apply gpaco6_clo, PR0.
Qed.

Lemma gpaco6_unfold_bot clo
      (WCMP: wcompatible6 gf clo):
  gpaco6 gf clo bot6 bot6 <6= gf (gpaco6 gf clo bot6 bot6).
Proof.
  intros. apply gpaco6_init in PR; [|apply WCMP].
  _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. destruct PR0; [|contradiction]. apply gpaco6_final. apply gf_mon. right. apply H.
Qed.

End Soundness.

Section Distributivity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone6 gf.

Lemma gpaco6_dist clo r rg
      (CMP: wcompatible6 gf clo)
      (DIST: forall r1 r2, clo (r1 \6/ r2) <6= (clo r1 \6/ clo r2)):
  gpaco6 gf clo r rg <6= (paco6 gf (rclo6 clo (rg \6/ r)) \6/ rclo6 clo r).
Proof.
  intros. apply gpaco6_unfold in PR; [|apply gf_mon].
  apply rclo6_dist in PR; [|apply CMP|apply DIST].
  destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 H.
  pcofix CIH; intros.
  apply rclo6_wcompat in H0; [|apply gf_mon|apply CMP].
  pstep. eapply gf_mon. apply H0. intros.
  apply gpaco6_unfold in PR; [|apply gf_mon].
  apply rclo6_compose in PR.
  apply rclo6_dist in PR; [|apply CMP|apply DIST].
  destruct PR.
  - right. apply CIH.
    eapply rclo6_mon. apply H. intros.
    eapply gf_mon. apply PR. intros.
    apply gpaco6_gupaco. apply gf_mon.
    apply gpaco6_gen_rclo. apply gf_mon.
    eapply gupaco6_mon. apply PR0. intros.
    destruct PR1; apply H1.
  - assert (REL: @rclo6 clo (rclo6 clo (gf (gupaco6 gf clo ((rg \6/ r) \6/ (rg \6/ r))) \6/ (rg \6/ r))) x0 x1 x2 x3 x4 x5).
    { eapply rclo6_mon. apply H. intros. apply gpaco6_unfold in PR. apply PR. apply gf_mon. }
    apply rclo6_rclo in REL.
    apply rclo6_dist in REL; [|apply CMP|apply DIST].
    right. destruct REL; cycle 1.
    + apply CIH0, H1.
    + apply CIH.
      eapply rclo6_mon. apply H1. intros.
      eapply gf_mon. apply PR. intros.
      eapply gupaco6_mon. apply PR0. intros.
      destruct PR1; apply H2.
Qed.

Lemma gpaco6_dist_reverse clo r rg:
  (paco6 gf (rclo6 clo (rg \6/ r)) \6/ rclo6 clo r) <6= gpaco6 gf clo r rg.
Proof.
  intros. destruct PR; cycle 1.
  - eapply gpaco6_rclo. apply H.
  - econstructor. apply rclo6_base. left.
    revert x0 x1 x2 x3 x4 x5 H. pcofix CIH; intros.
    _punfold H0; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H0. intros.
    destruct PR.
    + apply rclo6_base. right. apply CIH, H.
    + eapply rclo6_mon. apply H. intros.
      right. apply CIH0. apply PR.
Qed.

End Distributivity.

Section Companion.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone6 gf.

Inductive cpn6 (r: rel) x0 x1 x2 x3 x4 x5 : Prop :=
| cpn6_intro
    clo
    (COM: compatible6 gf clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5)
.

Lemma cpn6_mon: monotone6 cpn6.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat6_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn6_greatest: forall clo (COM: compatible6 gf clo), clo <7= cpn6.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn6_compat: compatible6 gf cpn6.
Proof.
  econstructor; [apply cpn6_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat6_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn6_wcompat: wcompatible6 gf cpn6.
Proof. apply compat6_wcompat, cpn6_compat. apply gf_mon. Qed.

Lemma cpn6_gupaco:
  gupaco6 gf cpn6 <7= cpn6.
Proof.
  intros. eapply cpn6_greatest, PR. apply wcompat6_compat. apply gf_mon. apply cpn6_wcompat.
Qed.

Lemma cpn6_cpn r:
  cpn6 (cpn6 r) <6= cpn6 r.
Proof.
  intros. apply cpn6_gupaco, gpaco6_gupaco, gpaco6_clo. apply gf_mon.
  eapply cpn6_mon, gpaco6_clo. apply PR.
Qed.

Lemma cpn6_base r:
  r <6= cpn6 r.
Proof.
  intros. apply cpn6_gupaco. apply gpaco6_base, PR.
Qed.

Lemma cpn6_clo
      r clo (LE: clo <7= cpn6):
  clo (cpn6 r) <6= cpn6 r.
Proof.
  intros. apply cpn6_cpn, LE, PR.
Qed.

Lemma cpn6_step r:
  gf (cpn6 r) <6= cpn6 r.
Proof.
  intros. apply cpn6_gupaco. apply gpaco6_step. apply gf_mon.
  eapply gf_mon, gpaco6_clo. apply PR.
Qed.

Lemma cpn6_uclo uclo
      (MON: monotone6 uclo)
      (WCOM: forall r, uclo (gf r) <6= gf (gupaco6 gf (uclo \7/ cpn6) r)):
  uclo <7= gupaco6 gf cpn6.
Proof.
  intros. apply gpaco6_clo.
  exists (gupaco6 gf (uclo \7/ cpn6)).
  - apply wcompat6_compat. apply gf_mon.
    econstructor.
    + apply monotone6_union. apply MON. apply cpn6_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat6_compat with (gf:=gf) in H; [| apply cpn6_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco6_clo. right. apply PR0.
  - apply gpaco6_clo. left. apply PR.
Qed.

End Companion.

Section Respectful.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone6 gf.

Structure wrespectful6 (clo: rel -> rel) : Prop :=
  wrespect6_intro {
      wrespect6_mon: monotone6 clo;
      wrespect6_respect :
        forall l r
               (LE: l <6= r)
               (GF: l <6= gf r),
        clo l <6= gf (rclo6 clo r);
    }.

Structure prespectful6 (clo: rel -> rel) : Prop :=
  prespect6_intro {
      prespect6_mon: monotone6 clo;
      prespect6_respect :
        forall l r
               (LE: l <6= r)
               (GF: l <6= gf r),
        clo l <6= paco6 gf (r \6/ clo r);
    }.

Structure grespectful6 (clo: rel -> rel) : Prop :=
  grespect6_intro {
      grespect6_mon: monotone6 clo;
      grespect6_respect :
        forall l r
               (LE: l <6= r)
               (GF: l <6= gf r),
        clo l <6= rclo6 (cpn6 gf) (gf (rclo6 (clo \7/ gupaco6 gf (cpn6 gf)) r));
    }.

Definition gf'6 := id /7\ gf.

Definition compatible'6 := compatible6 gf'6.

Lemma wrespect6_compatible'
      clo (RES: wrespectful6 clo):
  compatible'6 (rclo6 clo).
Proof.
  intros. econstructor. apply rclo6_mon.
  intros. destruct RES. split.
  { eapply rclo6_mon. apply PR. intros. apply PR0. }
  induction PR; intros.
  - eapply gf_mon. apply IN.
    intros. apply rclo6_base, PR.
  - eapply gf_mon.
    + eapply wrespect6_respect0; [|apply H|apply IN].
      intros. eapply rclo6_mon; intros; [apply LE, PR|apply PR0].
    + intros. apply rclo6_rclo, PR.
Qed.

Lemma prespect6_compatible'
      clo (RES: prespectful6 clo):
  compatible'6 (fun r => upaco6 gf (r \6/ clo r)).
Proof.
  econstructor.
  { red; intros. eapply upaco6_mon. apply IN.
    intros. destruct PR.
    - left. apply LE, H.
    - right. eapply RES. apply H. intros. apply LE, PR. }

  intros r.
  assert (LEM: (gf'6 r \6/ clo (gf'6 r)) <6= (r \6/ clo r)).
  { intros. destruct PR.
    - left. apply H.
    - right. eapply RES. apply H. intros. apply PR.
  }

  intros. destruct PR.
  - split.
    + left. eapply paco6_mon. apply H. apply LEM.
    + apply paco6_unfold; [apply gf_mon|].
      eapply paco6_mon. apply H. apply LEM.
  - split.
    + right. apply LEM. apply H.
    + destruct H.
      * eapply gf_mon. apply H. intros. right. left. apply PR.
      * apply paco6_unfold; [apply gf_mon|].
        eapply RES, H; intros; apply PR.
Qed.

Lemma grespect6_compatible'
      clo (RES: grespectful6 clo):
  compatible'6 (rclo6 (clo \7/ cpn6 gf)).
Proof.
  apply wrespect6_compatible'.
  econstructor.
  { red; intros. destruct IN.
    - left. eapply RES; [apply H|]. apply LE.
    - right. eapply cpn6_mon; [apply H|]. apply LE. }
  intros. destruct PR.
  - eapply RES.(grespect6_respect) in H; [|apply LE|apply GF].
    apply (@compat6_compat gf (rclo6 (cpn6 gf))) in H.
    2: { apply rclo6_compat; [apply gf_mon|]. apply cpn6_compat. apply gf_mon. }
    eapply gf_mon; [apply H|].
    intros. apply rclo6_clo. right.
    exists (rclo6 (cpn6 gf)).
    { apply rclo6_compat; [apply gf_mon|]. apply cpn6_compat. apply gf_mon. }
    eapply rclo6_mon; [eapply PR|].
    intros. eapply rclo6_mon_gen; [eapply PR0|..].
    + intros. destruct PR1.
      * left. apply H0.
      * right. apply cpn6_gupaco; [apply gf_mon|apply H0].
    + intros. apply PR1.
  - eapply gf_mon.
    + apply (@compat6_compat gf (rclo6 (cpn6 gf))).
      { apply rclo6_compat; [apply gf_mon|]. apply cpn6_compat. apply gf_mon. }
      eapply rclo6_clo_base. eapply cpn6_mon; [apply H|apply GF].
    + intros. eapply rclo6_mon_gen; [eapply PR|..].
      * intros. right. apply PR0.
      * intros. apply PR0.
Qed.

Lemma compat6_compatible'
      clo (COM: compatible6 gf clo):
  compatible'6 clo.
Proof.
  destruct COM. econstructor; [apply compat6_mon0|].
  intros. split.
  - eapply compat6_mon0; intros; [apply PR| apply PR0].
  - apply compat6_compat0.
    eapply compat6_mon0; intros; [apply PR| apply PR0].
Qed.

Lemma compatible'6_companion
      clo (RES: compatible'6 clo):
  clo <7= cpn6 gf.
Proof.
  assert (MON: monotone6 gf'6).
  { econstructor. apply LE, IN.
    eapply gf_mon, LE. apply IN.
  }
  assert (CPN: clo <7= cpn6 gf'6).
  { intros. econstructor. apply RES. apply PR.
  }
  intros. apply CPN in PR.
  econstructor; [|apply PR].
  econstructor; [apply cpn6_mon|]; intros.
  assert (PR1: cpn6 gf'6 (gf r) <6= cpn6 gf'6 (gf'6 (cpn6 gf r))).
  { intros. eapply cpn6_mon. apply PR1.
    intros. assert (TMP: gf (cpn6 gf r) <6= (cpn6 gf r /6\ gf (cpn6 gf r))).
    { split; [apply cpn6_step; [apply gf_mon|]|]; assumption. }
    apply TMP.
    eapply gf_mon. apply PR2. intros. apply cpn6_base; assumption.
  }
  apply PR1 in PR0. clear PR1. 
  eapply compat6_compat with (gf:=gf'6) in PR0; [|apply cpn6_compat, MON].
  eapply gf_mon; [apply PR0|].
  intros. eapply cpn6_cpn; [apply MON|].
  eapply cpn6_mon; [apply PR1|].
  intros. econstructor; [|apply PR2].
  apply compat6_compatible', cpn6_compat, gf_mon.
Qed.

Lemma wrespect6_companion
      clo (RES: wrespectful6 clo):
  clo <7= cpn6 gf.
Proof.
  intros. eapply wrespect6_compatible' in RES.
  eapply (@compatible'6_companion (rclo6 clo)) in RES; [apply RES|].
  eapply rclo6_clo_base, PR.
Qed.

Lemma prespect6_companion
      clo (RES: prespectful6 clo):
  clo <7= cpn6 gf.
Proof.
  intros. eapply compatible'6_companion. apply prespect6_compatible'. apply RES.
  right. right. apply PR.
Qed.

Lemma grespect6_companion
      clo (RES: grespectful6 clo):
  clo <7= cpn6 gf.
Proof.
  intros. eapply grespect6_compatible' in RES.
  eapply (@compatible'6_companion (rclo6 (clo \7/ cpn6 gf))); [apply RES|].
  apply rclo6_clo_base. left. apply PR.
Qed.

Lemma wrespect6_uclo
      clo (RES: wrespectful6 clo):
  clo <7= gupaco6 gf (cpn6 gf).
Proof.
  intros. eapply gpaco6_clo, wrespect6_companion, PR. apply RES.
Qed.

Lemma prespect6_uclo
      clo (RES: prespectful6 clo):
  clo <7= gupaco6 gf (cpn6 gf).
Proof.
  intros. eapply gpaco6_clo, prespect6_companion, PR. apply RES.
Qed.

Lemma grespect6_uclo
      clo (RES: grespectful6 clo):
  clo <7= gupaco6 gf (cpn6 gf).
Proof.
  intros. eapply gpaco6_clo, grespect6_companion, PR. apply RES.
Qed.

End Respectful.

End GeneralizedPaco6.

Hint Resolve gpaco6_def_mon : paco.
Hint Unfold gupaco6 : paco.
Hint Resolve gpaco6_base : paco.
Hint Resolve gpaco6_step : paco.
Hint Resolve gpaco6_final : paco.
Hint Resolve rclo6_base : paco.
Hint Constructors gpaco6 : paco.
Hint Resolve wrespect6_uclo : paco.
Hint Resolve prespect6_uclo : paco.
