Require Export Program.Basics. Open Scope program_scope.
Require Import paco12 pacotac.
Set Implicit Arguments.

Section Companion12.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.

Local Notation rel := (rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11).

Section Companion12_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone12 gf.

(** 
  Compatibility, Companion & Guarded Companion
*)

Structure compatible12 (clo: rel -> rel) : Prop :=
  compat12_intro {
      compat12_mon: monotone12 clo;
      compat12_compat : forall r,
          clo (gf r) <12= gf (clo r);
    }.

Inductive cpn12 (r: rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Prop :=
| cpn12_intro
    clo
    (COM: compatible12 clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
.

Definition fcpn12 := compose gf cpn12.

Lemma cpn12_mon: monotone12 cpn12.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat12_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn12_compat: compatible12 cpn12.
Proof.
  econstructor; [apply cpn12_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat12_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn12_greatest: forall clo (COM: compatible12 clo), clo <13= cpn12.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn12_cpn: forall r,
    cpn12 (cpn12 r) <12= cpn12 r.
Proof.
  intros. exists (compose cpn12 cpn12); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn12_mon; [apply IN|].
    intros. eapply cpn12_mon; [apply PR0|apply LE].
  - intros. eapply (compat12_compat cpn12_compat).
    eapply cpn12_mon; [apply PR0|].
    intros. eapply (compat12_compat cpn12_compat), PR1. 
Qed.

Lemma fcpn12_mon: monotone12 fcpn12.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn12_mon; [apply PR|apply LE].
Qed.

Lemma fcpn12_sound:
  paco12 fcpn12 bot12 <12= paco12 gf bot12.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \12/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn12 n (paco12 fcpn12 bot12) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn12 n (paco12 fcpn12 bot12) <12= gf (rclo cpn12 (S n) (paco12 fcpn12 bot12))).
  { intro X. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply fcpn12_mon].
    + intros. right. eapply cpn12_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat12_compat cpn12_compat).
        eapply (compat12_mon cpn12_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo12 (clo: rel->rel) (r: rel): rel :=
| rclo12_base
    x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    (IN: r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11):
    @rclo12 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
| rclo12_clo'
    r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    (LE: r' <12= rclo12 clo r)
    (IN: clo r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11):
    @rclo12 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
.           

Structure wcompatible12 (clo: rel -> rel) : Prop :=
  wcompat12_intro {
      wcompat12_mon: monotone12 clo;
      wcompat12_wcompat : forall r,
          clo (gf r) <12= gf (rclo12 (clo \13/ cpn12) r);
    }.


Lemma rclo12_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
      (IN: @rclo12 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (LEclo: clo <13= clo')
      (LEr: r <12= r') :
  @rclo12 clo' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo12_mon clo:
  monotone12 (rclo12 clo).
Proof.
  repeat intro. eapply rclo12_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo12_clo clo r:
  clo (rclo12 clo r) <12= rclo12 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo12_rclo clo r:
  rclo12 clo (rclo12 clo r) <12= rclo12 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo12_compose clo r:
  rclo12 (rclo12 clo) r <12= rclo12 clo r.
Proof.
  intros. induction PR.
  - apply rclo12_base, IN.
  - apply rclo12_rclo.
    eapply rclo12_mon; [apply IN|apply H].
Qed.

Lemma rclo12_compat clo
      (COM: compatible12 clo):
  compatible12 (rclo12 clo).
Proof.
  econstructor.
  - apply rclo12_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo12_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo12_clo. apply PR.
Qed.

Lemma wcompat12_compat  clo
      (WCOM: wcompatible12 clo):
  compatible12 (rclo12 (clo \13/ cpn12)).
Proof.
  econstructor; [eapply rclo12_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply IN|]. intros.
    apply rclo12_base. apply PR.
  - destruct IN as [IN|IN].
    + eapply gf_mon.
      * eapply WCOM. eapply WCOM; [apply IN|apply H].
      * intros. apply rclo12_rclo, PR.
    + eapply gf_mon; [|intros; apply rclo12_clo; right; apply PR].
      apply (compat12_compat cpn12_compat).
      eapply cpn12_mon; [apply IN|apply H].
Qed.

Lemma wcompat12_sound clo
      (WCOM: wcompatible12 clo):
  clo <13= cpn12.
Proof.
  intros. exists (rclo12 (clo \13/ cpn12)).
  - apply wcompat12_compat, WCOM.
  - apply rclo12_clo.
    left. eapply WCOM. apply PR.
    intros. apply rclo12_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn12_base: forall r, r <12= cpn12 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
  - apply PR.
Qed.

Lemma cpn12_step r:
  fcpn12 r <12= cpn12 r.
Proof.
  intros. eapply cpn12_cpn. exists gf.
  - econstructor. apply gf_mon. intros; apply PR0.
  - apply PR.
Qed.

Lemma cpn12_from_upaco r:
  upaco12 fcpn12 r <12= cpn12 r.
Proof.
  eapply wcompat12_sound.
  econstructor; [apply upaco12_mon|].
  intros. destruct PR as [PR|PR].
  - _punfold PR; [|apply fcpn12_mon]. 
    eapply gf_mon; [apply PR|].
    intros. apply rclo12_clo; right.
    eapply cpn12_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo12_clo; left.
      left. eapply paco12_mon; [apply H|].
      intros. apply rclo12_clo; right. apply cpn12_step.
      eapply gf_mon; [apply PR1|].
      intros. apply cpn12_base, rclo12_base, PR2.
    + apply rclo12_clo; right. apply cpn12_step.
      eapply gf_mon; [apply H|].
      intros. apply cpn12_base, rclo12_base, PR1.
  - eapply gf_mon. apply PR.
    intros. apply rclo12_base, PR0. 
Qed.

Lemma cpn12_from_paco r:
  paco12 fcpn12 r <12= cpn12 r.
Proof. intros. apply cpn12_from_upaco. left. apply PR. Qed.

Lemma fcpn12_from_paco r:
  paco12 fcpn12 r <12= fcpn12 r.
Proof.
  intros. _punfold PR; [|apply fcpn12_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn12_cpn.
  eapply cpn12_mon; [apply PR0|].
  apply cpn12_from_upaco.
Qed.

Lemma fcpn12_to_paco r:
  fcpn12 r <12= paco12 fcpn12 r.
Proof.
  intros. pfold. eapply fcpn12_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn12_complete:
  paco12 gf bot12 <12= cpn12 bot12.
Proof.
  intros. apply cpn12_from_paco.
  eapply paco12_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn12_base].
  - intros. apply PR0.
Qed.

Lemma cpn12_init:
  cpn12 bot12 <12= paco12 gf bot12.
Proof.
  intros. apply fcpn12_sound, fcpn12_to_paco, (compat12_compat cpn12_compat).
  eapply cpn12_mon; [apply PR|contradiction].
Qed.

Lemma cpn12_clo
      r clo (LE: clo <13= cpn12):
  clo (cpn12 r) <12= cpn12 r.
Proof.
  intros. apply cpn12_cpn, LE, PR.
Qed.

Lemma cpn12_unfold:
  cpn12 bot12 <12= fcpn12 bot12.
Proof.
  intros. apply cpn12_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn12_complete, PR0.
Qed.

Lemma fcpn12_clo
      r clo (LE: clo <13= cpn12):
  clo (fcpn12 r) <12= fcpn12 r.
Proof.
  intros. apply LE, (compat12_compat cpn12_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn12_cpn, PR0.
Qed.

Lemma cpn12_final: forall r, upaco12 gf r <12= cpn12 r.
Proof.
  intros. eapply cpn12_from_upaco.
  intros. eapply upaco12_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn12_base, PR1.
Qed.

Lemma fcpn12_final: forall r, paco12 gf r <12= fcpn12 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn12_final].
Qed.

Lemma cpn12_algebra r :
  r <12= gf r -> r <12= cpn12 bot12.
Proof.
  intros. apply cpn12_final. left.
  revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion12_main.

Lemma cpn12_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r
      (IN: @cpn12 gf bot12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (MONgf: monotone12 gf)
      (MONgf': monotone12 gf')
      (LE: gf <13= gf'):
  @cpn12 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  apply cpn12_init in IN; [|apply MONgf].
  apply cpn12_final; [apply MONgf'|].
  left. eapply paco12_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn12_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r
      (IN: @fcpn12 gf bot12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (MONgf: monotone12 gf)
      (MONgf': monotone12 gf')
      (LE: gf <13= gf'):
  @fcpn12 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  apply LE. eapply MONgf. apply IN.
  intros. eapply cpn12_mon_bot; eassumption.
Qed.

End Companion12.

Hint Unfold fcpn12 : paco.

Hint Resolve cpn12_base : paco.
Hint Resolve cpn12_step : paco.
Hint Constructors rclo12 : paco.
Hint Resolve rclo12_clo : paco.
