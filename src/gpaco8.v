Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paco8 pacotac.
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

Lemma rclo8_clo_base clo r:
  clo r <8= rclo8 clo r.
Proof.
  intros. eapply rclo8_clo', PR.
  intros. apply rclo8_base, PR0.
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

Lemma gpaco8_gen_guard  clo r rg:
  gpaco8 clo r (rg \8/ r) <8= gpaco8 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  eapply rclo8_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco8_mon_gen; intros. apply H. apply PR.
  destruct PR. apply H0. right. apply H0.
Qed.

Lemma gpaco8_rclo clo r rg:
  rclo8 clo r <8= gpaco8 clo r rg.
Proof.
  intros. econstructor.
  eapply rclo8_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco8_clo clo r rg:
  clo r <8= gpaco8 clo r rg.
Proof.
  intros. apply gpaco8_rclo. eapply rclo8_clo_base, PR.
Qed.

Lemma gpaco8_gen_rclo clo r rg:
  gpaco8 (rclo8 clo) r rg <8= gpaco8 clo r rg.
Proof.
  intros. destruct PR. econstructor.
  apply rclo8_compose.
  eapply rclo8_mon. apply IN. intros.
  destruct PR; [|right; apply H].
  left. eapply paco8_mon_gen; intros; [apply H| |apply PR].
  eapply gf_mon, rclo8_compose. apply PR.
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

Lemma gpaco8_gpaco clo r rg:
  gpaco8 clo (gpaco8 clo r rg) (gupaco8 clo (rg \8/ r)) <8= gpaco8 clo r rg.
Proof.
  intros. apply gpaco8_unfold in PR.
  econstructor. apply rclo8_rclo. eapply rclo8_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 x7 PR. intros.
  destruct PR; [|destruct H; apply IN].
  apply rclo8_base. left. pstep.
  eapply gf_mon. apply H. clear x0 x1 x2 x3 x4 x5 x6 x7 H. intros.
  cut (@gupaco8 clo (rg \8/ r) x0 x1 x2 x3 x4 x5 x6 x7).
  { intros. destruct H. eapply rclo8_mon. apply IN. intros.
    destruct PR0; [|right; apply H].
    left. eapply paco8_mon. apply H. intros. destruct PR0; apply H0.
  }
  apply gpaco8_gupaco. eapply gupaco8_mon. apply PR. intros.
  destruct PR0; [apply H|].
  eapply gpaco8_mon; [apply H|right|left]; intros; apply PR0.
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
  
Lemma gpaco8_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 r r' rg rg'
      (IN: @gpaco8 gf clo r rg x0 x1 x2 x3 x4 x5 x6 x7)
      (gf_mon: monotone8 gf)
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
      (gf_mon: monotone8 gf)
      (LEgf: gf <9= gf')
      (LEclo: clo <9= clo'):
  @gpaco8 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply gpaco8_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco8_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 r r'
      (IN: @gupaco8 gf clo r x0 x1 x2 x3 x4 x5 x6 x7)
      (gf_mon: monotone8 gf)
      (LEgf: gf <9= gf')
      (LEclo: clo <9= clo')
      (LEr: r <8= r'):
  @gupaco8 gf' clo' r' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply gpaco8_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. apply LEr. apply LEr.
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

Lemma rclo8_dist clo
      (MON: monotone8 clo)
      (DIST: forall r1 r2, clo (r1 \8/ r2) <8= (clo r1 \8/ clo r2)):
  forall r1 r2, rclo8 clo (r1 \8/ r2) <8= (rclo8 clo r1 \8/ rclo8 clo r2).
Proof.
  intros. induction PR.
  + destruct IN; [left|right]; apply rclo8_base, H.
  + assert (REL: clo (rclo8 clo r1 \8/ rclo8 clo r2) x0 x1 x2 x3 x4 x5 x6 x7).
    { eapply MON. apply IN. apply H. }
    apply DIST in REL. destruct REL; [left|right]; apply rclo8_clo, H0.
Qed.

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

Lemma rclo8_wcompat clo
      (COM: wcompatible8 clo):
  wcompatible8 (rclo8 clo).
Proof.
  econstructor.
  - apply rclo8_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. apply gpaco8_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply gpaco8_gupaco. apply gf_mon.
        eapply gupaco8_mon_gen; intros; [apply PR|apply gf_mon|apply PR0| |apply PR0].
        apply rclo8_clo_base, PR0.
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
      intros. eapply gupaco8_mon_gen. apply PR. apply gf_mon. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco8_mon_gen. apply PR. apply gf_mon.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
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
  - eapply gpaco8_mon_bot. apply PR. apply gf_mon. intros; apply PR0.
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

Section Distributivity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone8 gf.

Lemma gpaco8_dist clo r rg
      (CMP: wcompatible8 gf clo)
      (DIST: forall r1 r2, clo (r1 \8/ r2) <8= (clo r1 \8/ clo r2)):
  gpaco8 gf clo r rg <8= (paco8 gf (rclo8 clo (rg \8/ r)) \8/ rclo8 clo r).
Proof.
  intros. apply gpaco8_unfold in PR; [|apply gf_mon].
  apply rclo8_dist in PR; [|apply CMP|apply DIST].
  destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 x7 H.
  pcofix CIH; intros.
  apply rclo8_wcompat in H0; [|apply gf_mon|apply CMP].
  pstep. eapply gf_mon. apply H0. intros.
  apply gpaco8_unfold in PR; [|apply gf_mon].
  apply rclo8_compose in PR.
  apply rclo8_dist in PR; [|apply CMP|apply DIST].
  destruct PR.
  - right. apply CIH.
    eapply rclo8_mon. apply H. intros.
    eapply gf_mon. apply PR. intros.
    apply gpaco8_gupaco. apply gf_mon.
    apply gpaco8_gen_rclo. apply gf_mon.
    eapply gupaco8_mon. apply PR0. intros.
    destruct PR1; apply H1.
  - assert (REL: @rclo8 clo (rclo8 clo (gf (gupaco8 gf clo ((rg \8/ r) \8/ (rg \8/ r))) \8/ (rg \8/ r))) x0 x1 x2 x3 x4 x5 x6 x7).
    { eapply rclo8_mon. apply H. intros. apply gpaco8_unfold in PR. apply PR. apply gf_mon. }
    apply rclo8_rclo in REL.
    apply rclo8_dist in REL; [|apply CMP|apply DIST].
    right. destruct REL; cycle 1.
    + apply CIH0, H1.
    + apply CIH.
      eapply rclo8_mon. apply H1. intros.
      eapply gf_mon. apply PR. intros.
      eapply gupaco8_mon. apply PR0. intros.
      destruct PR1; apply H2.
Qed.

Lemma gpaco8_dist_reverse clo r rg:
  (paco8 gf (rclo8 clo (rg \8/ r)) \8/ rclo8 clo r) <8= gpaco8 gf clo r rg.
Proof.
  intros. destruct PR; cycle 1.
  - eapply gpaco8_rclo. apply H.
  - econstructor. apply rclo8_base. left.
    revert x0 x1 x2 x3 x4 x5 x6 x7 H. pcofix CIH; intros.
    _punfold H0; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H0. intros.
    destruct PR.
    + apply rclo8_base. right. apply CIH, H.
    + eapply rclo8_mon. apply H. intros.
      right. apply CIH0. apply PR.
Qed.

End Distributivity.

Section Companion.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone8 gf.

Inductive cpn8 (r: rel) x0 x1 x2 x3 x4 x5 x6 x7 : Prop :=
| cpn8_intro
    clo
    (COM: compatible8 gf clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6 x7)
.

Lemma cpn8_mon: monotone8 cpn8.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat8_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn8_greatest: forall clo (COM: compatible8 gf clo), clo <9= cpn8.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn8_compat: compatible8 gf cpn8.
Proof.
  econstructor; [apply cpn8_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat8_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn8_wcompat: wcompatible8 gf cpn8.
Proof. apply compat8_wcompat, cpn8_compat. apply gf_mon. Qed.

Lemma cpn8_gupaco:
  gupaco8 gf cpn8 <9= cpn8.
Proof.
  intros. eapply cpn8_greatest, PR. apply wcompat8_compat. apply gf_mon. apply cpn8_wcompat.
Qed.

Lemma cpn8_cpn r:
  cpn8 (cpn8 r) <8= cpn8 r.
Proof.
  intros. apply cpn8_gupaco, gpaco8_gupaco, gpaco8_clo. apply gf_mon.
  eapply cpn8_mon, gpaco8_clo. apply PR.
Qed.

Lemma cpn8_base r:
  r <8= cpn8 r.
Proof.
  intros. apply cpn8_gupaco. apply gpaco8_base, PR.
Qed.

Lemma cpn8_clo
      r clo (LE: clo <9= cpn8):
  clo (cpn8 r) <8= cpn8 r.
Proof.
  intros. apply cpn8_cpn, LE, PR.
Qed.

Lemma cpn8_step r:
  gf (cpn8 r) <8= cpn8 r.
Proof.
  intros. apply cpn8_gupaco. apply gpaco8_step. apply gf_mon.
  eapply gf_mon, gpaco8_clo. apply PR.
Qed.

Lemma cpn8_uclo uclo
      (MON: monotone8 uclo)
      (WCOM: forall r, uclo (gf r) <8= gf (gupaco8 gf (uclo \9/ cpn8) r)):
  uclo <9= gupaco8 gf cpn8.
Proof.
  intros. apply gpaco8_clo.
  exists (gupaco8 gf (uclo \9/ cpn8)).
  - apply wcompat8_compat. apply gf_mon.
    econstructor.
    + apply monotone8_union. apply MON. apply cpn8_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat8_compat with (gf:=gf) in H; [| apply cpn8_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco8_clo. right. apply PR0.
  - apply gpaco8_clo. left. apply PR.
Qed.

End Companion.

Section Respectful.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone8 gf.

Structure wrespectful8 (clo: rel -> rel) : Prop :=
  wrespect8_intro {
      wrespect8_mon: monotone8 clo;
      wrespect8_respect :
        forall l r
               (LE: l <8= r)
               (GF: l <8= gf r),
        clo l <8= gf (rclo8 clo r);
    }.

Structure prespectful8 (clo: rel -> rel) : Prop :=
  prespect8_intro {
      prespect8_mon: monotone8 clo;
      prespect8_respect :
        forall l r
               (LE: l <8= r)
               (GF: l <8= gf r),
        clo l <8= paco8 gf (r \8/ clo r);
    }.

Structure grespectful8 (clo: rel -> rel) : Prop :=
  grespect8_intro {
      grespect8_mon: monotone8 clo;
      grespect8_respect :
        forall l r
               (LE: l <8= r)
               (GF: l <8= gf r),
        clo l <8= rclo8 (cpn8 gf) (gf (rclo8 (clo \9/ gupaco8 gf (cpn8 gf)) r));
    }.

Definition gf'8 := id /9\ gf.

Definition compatible'8 := compatible8 gf'8.

Lemma wrespect8_compatible'
      clo (RES: wrespectful8 clo):
  compatible'8 (rclo8 clo).
Proof.
  intros. econstructor. apply rclo8_mon.
  intros. destruct RES. split.
  { eapply rclo8_mon. apply PR. intros. apply PR0. }
  induction PR; intros.
  - eapply gf_mon. apply IN.
    intros. apply rclo8_base, PR.
  - eapply gf_mon.
    + eapply wrespect8_respect0; [|apply H|apply IN].
      intros. eapply rclo8_mon; intros; [apply LE, PR|apply PR0].
    + intros. apply rclo8_rclo, PR.
Qed.

Lemma prespect8_compatible'
      clo (RES: prespectful8 clo):
  compatible'8 (fun r => upaco8 gf (r \8/ clo r)).
Proof.
  econstructor.
  { red; intros. eapply upaco8_mon. apply IN.
    intros. destruct PR.
    - left. apply LE, H.
    - right. eapply RES. apply H. intros. apply LE, PR. }

  intros r.
  assert (LEM: (gf'8 r \8/ clo (gf'8 r)) <8= (r \8/ clo r)).
  { intros. destruct PR.
    - left. apply H.
    - right. eapply RES. apply H. intros. apply PR.
  }

  intros. destruct PR.
  - split.
    + left. eapply paco8_mon. apply H. apply LEM.
    + apply paco8_unfold; [apply gf_mon|].
      eapply paco8_mon. apply H. apply LEM.
  - split.
    + right. apply LEM. apply H.
    + destruct H.
      * eapply gf_mon. apply H. intros. right. left. apply PR.
      * apply paco8_unfold; [apply gf_mon|].
        eapply RES, H; intros; apply PR.
Qed.

Lemma grespect8_compatible'
      clo (RES: grespectful8 clo):
  compatible'8 (rclo8 (clo \9/ cpn8 gf)).
Proof.
  apply wrespect8_compatible'.
  econstructor.
  { red; intros. destruct IN.
    - left. eapply RES; [apply H|]. apply LE.
    - right. eapply cpn8_mon; [apply H|]. apply LE. }
  intros. destruct PR.
  - eapply RES.(grespect8_respect) in H; [|apply LE|apply GF].
    apply (@compat8_compat gf (rclo8 (cpn8 gf))) in H.
    2: { apply rclo8_compat; [apply gf_mon|]. apply cpn8_compat. apply gf_mon. }
    eapply gf_mon; [apply H|].
    intros. apply rclo8_clo. right.
    exists (rclo8 (cpn8 gf)).
    { apply rclo8_compat; [apply gf_mon|]. apply cpn8_compat. apply gf_mon. }
    eapply rclo8_mon; [eapply PR|].
    intros. eapply rclo8_mon_gen; [eapply PR0|..].
    + intros. destruct PR1.
      * left. apply H0.
      * right. apply cpn8_gupaco; [apply gf_mon|apply H0].
    + intros. apply PR1.
  - eapply gf_mon.
    + apply (@compat8_compat gf (rclo8 (cpn8 gf))).
      { apply rclo8_compat; [apply gf_mon|]. apply cpn8_compat. apply gf_mon. }
      eapply rclo8_clo_base. eapply cpn8_mon; [apply H|apply GF].
    + intros. eapply rclo8_mon_gen; [eapply PR|..].
      * intros. right. apply PR0.
      * intros. apply PR0.
Qed.

Lemma compat8_compatible'
      clo (COM: compatible8 gf clo):
  compatible'8 clo.
Proof.
  destruct COM. econstructor; [apply compat8_mon0|].
  intros. split.
  - eapply compat8_mon0; intros; [apply PR| apply PR0].
  - apply compat8_compat0.
    eapply compat8_mon0; intros; [apply PR| apply PR0].
Qed.

Lemma compatible'8_companion
      clo (RES: compatible'8 clo):
  clo <9= cpn8 gf.
Proof.
  assert (MON: monotone8 gf'8).
  { econstructor. apply LE, IN.
    eapply gf_mon, LE. apply IN.
  }
  assert (CPN: clo <9= cpn8 gf'8).
  { intros. econstructor. apply RES. apply PR.
  }
  intros. apply CPN in PR.
  econstructor; [|apply PR].
  econstructor; [apply cpn8_mon|]; intros.
  assert (PR1: cpn8 gf'8 (gf r) <8= cpn8 gf'8 (gf'8 (cpn8 gf r))).
  { intros. eapply cpn8_mon. apply PR1.
    intros. assert (TMP: gf (cpn8 gf r) <8= (cpn8 gf r /8\ gf (cpn8 gf r))).
    { split; [apply cpn8_step; [apply gf_mon|]|]; assumption. }
    apply TMP.
    eapply gf_mon. apply PR2. intros. apply cpn8_base; assumption.
  }
  apply PR1 in PR0. clear PR1. 
  eapply compat8_compat with (gf:=gf'8) in PR0; [|apply cpn8_compat, MON].
  eapply gf_mon; [apply PR0|].
  intros. eapply cpn8_cpn; [apply MON|].
  eapply cpn8_mon; [apply PR1|].
  intros. econstructor; [|apply PR2].
  apply compat8_compatible', cpn8_compat, gf_mon.
Qed.

Lemma wrespect8_companion
      clo (RES: wrespectful8 clo):
  clo <9= cpn8 gf.
Proof.
  intros. eapply wrespect8_compatible' in RES.
  eapply (@compatible'8_companion (rclo8 clo)) in RES; [apply RES|].
  eapply rclo8_clo_base, PR.
Qed.

Lemma prespect8_companion
      clo (RES: prespectful8 clo):
  clo <9= cpn8 gf.
Proof.
  intros. eapply compatible'8_companion. apply prespect8_compatible'. apply RES.
  right. right. apply PR.
Qed.

Lemma grespect8_companion
      clo (RES: grespectful8 clo):
  clo <9= cpn8 gf.
Proof.
  intros. eapply grespect8_compatible' in RES.
  eapply (@compatible'8_companion (rclo8 (clo \9/ cpn8 gf))); [apply RES|].
  apply rclo8_clo_base. left. apply PR.
Qed.

Lemma wrespect8_uclo
      clo (RES: wrespectful8 clo):
  clo <9= gupaco8 gf (cpn8 gf).
Proof.
  intros. eapply gpaco8_clo, wrespect8_companion, PR. apply RES.
Qed.

Lemma prespect8_uclo
      clo (RES: prespectful8 clo):
  clo <9= gupaco8 gf (cpn8 gf).
Proof.
  intros. eapply gpaco8_clo, prespect8_companion, PR. apply RES.
Qed.

Lemma grespect8_uclo
      clo (RES: grespectful8 clo):
  clo <9= gupaco8 gf (cpn8 gf).
Proof.
  intros. eapply gpaco8_clo, grespect8_companion, PR. apply RES.
Qed.

End Respectful.

End GeneralizedPaco8.

Hint Resolve gpaco8_def_mon : paco.
Hint Unfold gupaco8 : paco.
Hint Resolve gpaco8_base : paco.
Hint Resolve gpaco8_step : paco.
Hint Resolve gpaco8_final : paco.
Hint Resolve rclo8_base : paco.
Hint Constructors gpaco8 : paco.
Hint Resolve wrespect8_uclo : paco.
Hint Resolve prespect8_uclo : paco.
