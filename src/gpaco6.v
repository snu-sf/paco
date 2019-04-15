Require Export Program.Basics. Open Scope program_scope.
Require Import paco6 pacotac.
Set Implicit Arguments.

Section GeneralizedPaco6.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.

Local Notation rel := (rel6 T0 T1 T2 T3 T4 T5).

Lemma monotone6_compose (clo1 clo2: rel -> rel)
      (MON1: monotone6 clo1)
      (MON2: monotone6 clo2):
  monotone6 (compose clo1 clo2).
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone6_union (clo1 clo2: rel -> rel)
      (MON1: monotone6 clo1)
      (MON2: monotone6 clo2):
  monotone6 (clo1 \7/ clo2).
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

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

Lemma gpaco6_rclo clo r:
  rclo6 clo r <6= gupaco6 clo r.
Proof.
  intros. econstructor.
  eapply rclo6_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma gpaco6_clo clo r:
  clo r <6= gupaco6 clo r.
Proof.
  intros. apply gpaco6_rclo. eapply rclo6_clo', PR.
  apply rclo6_base.
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
Hypothesis gf_mon: monotone6 gf.
  
Lemma gpaco6_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 r r' rg rg'
      (IN: @gpaco6 gf clo r rg x0 x1 x2 x3 x4 x5)
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
      (LEgf: gf <7= gf')
      (LEclo: clo <7= clo'):
  @gpaco6 gf' clo' r' rg' x0 x1 x2 x3 x4 x5.
Proof.
  eapply gpaco6_mon_gen. apply IN. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco6_mon_gen (gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 r r'
      (IN: @gupaco6 gf clo r x0 x1 x2 x3 x4 x5)
      (LEgf: gf <7= gf')
      (LEclo: clo <7= clo')
      (LEr: r <6= r'):
  @gupaco6 gf' clo' r' x0 x1 x2 x3 x4 x5.
Proof.
  eapply gpaco6_mon_gen. apply IN. apply LEgf. apply LEclo. apply LEr. apply LEr.
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

Inductive cpn6 (r: rel) x0 x1 x2 x3 x4 x5 : Prop :=
| cpn6_intro
    clo
    (COM: compatible6 clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5)
.

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
      intros. eapply gupaco6_mon_gen. apply gf_mon. apply PR. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon. apply H.
      intros. eapply gupaco6_mon_gen. apply gf_mon. apply PR.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
Qed.

Lemma cpn6_mon: monotone6 cpn6.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat6_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn6_greatest: forall clo (COM: compatible6 clo), clo <7= cpn6.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn6_compat: compatible6 cpn6.
Proof.
  econstructor; [apply cpn6_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat6_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn6_wcompat: wcompatible6 cpn6.
Proof. apply compat6_wcompat, cpn6_compat. Qed.

Lemma cpn6_uclo uclo
      (MON: monotone6 uclo)
      (WCOM: forall r, uclo (gf r) <6= gf (gupaco6 gf (uclo \7/ cpn6) r)):
  uclo <7= gupaco6 gf cpn6.
Proof.
  intros. apply gpaco6_clo.
  exists (gupaco6 gf (uclo \7/ cpn6)).
  - apply wcompat6_compat.
    econstructor.
    + apply monotone6_union. apply MON. apply cpn6_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat6_compat in H; [| apply cpn6_compat].
        eapply gf_mon. apply H. intros.
        apply gpaco6_clo. right. apply PR0.
  - apply gpaco6_clo. left. apply PR.
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
  - eapply gpaco6_mon_bot. apply gf_mon. apply PR. intros; apply PR0.
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

End GeneralizedPaco6.

Hint Resolve gpaco6_def_mon : paco.
Hint Resolve gpaco6_base : paco.
Hint Resolve gpaco6_step : paco.
Hint Resolve gpaco6_final : paco.
