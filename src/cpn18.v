Require Export Program.Basics. Open Scope program_scope.
Require Import paco18 pacotac.
Set Implicit Arguments.

Section Companion18.

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
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.
Variable T14 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12), Type.
Variable T15 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (x14: @T14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13), Type.
Variable T16 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (x14: @T14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) (x15: @T15 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14), Type.
Variable T17 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (x14: @T14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) (x15: @T15 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) (x16: @T16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15), Type.

Local Notation rel := (rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone18 gf.

(** 
  Compatibility, Companion & Guarded Companion
*)

Structure compatible18 (clo: rel -> rel) : Prop :=
  compat18_intro {
      compat18_mon: monotone18 clo;
      compat18_compat : forall r,
          clo (gf r) <18= gf (clo r);
    }.

Inductive cpn18 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 : Prop :=
| cpn18_intro
    clo
    (COM: compatible18 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17)
.

Definition gcpn18 := compose gf cpn18.

Lemma cpn18_mon: monotone18 cpn18.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat18_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn18_compat: compatible18 cpn18.
Proof.
  econstructor; [apply cpn18_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat18_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn18_greatest: forall clo (COM: compatible18 clo), clo <19= cpn18.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn18_comp: forall r,
    cpn18 (cpn18 r) <18= cpn18 r.
Proof.
  intros. exists (compose cpn18 cpn18); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn18_mon; [apply IN|].
    intros. eapply cpn18_mon; [apply PR0|apply LE].
  - intros. eapply (compat18_compat cpn18_compat).
    eapply cpn18_mon; [apply PR0|].
    intros. eapply (compat18_compat cpn18_compat), PR1. 
Qed.

Lemma gcpn18_mon: monotone18 gcpn18.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn18_mon; [apply PR|apply LE].
Qed.

Lemma gcpn18_sound:
  paco18 gcpn18 bot18 <18= paco18 gf bot18.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \18/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn18 n (paco18 gcpn18 bot18) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn18 n (paco18 gcpn18 bot18) <18= gf (rclo cpn18 (S n) (paco18 gcpn18 bot18))).
  { intro X. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply gcpn18_mon].
    + intros. right. eapply cpn18_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat18_compat cpn18_compat).
        eapply (compat18_mon cpn18_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo18 (clo: rel->rel) (r: rel): rel :=
| rclo18_base
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17):
    @rclo18 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
| rclo18_clo'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
    (R': r' <18= rclo18 clo r)
    (CLOR': clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17):
    @rclo18 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
| rclo18_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
    (R': r' <18= rclo18 clo r)
    (CLOR': @gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17):
    @rclo18 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
| rclo18_cpn'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
    (R': r' <18= rclo18 clo r)
    (CLOR': @cpn18 r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17):
    @rclo18 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
.

Structure wcompatible18 (clo: rel -> rel) : Prop :=
  wcompat18_intro {
      wcompat18_mon: monotone18 clo;
      wcompat18_wcompat: forall r,
          clo (gf r) <18= gf (rclo18 clo r);
    }.

Lemma rclo18_mon_gen clo clo' r r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
      (IN: @rclo18 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17)
      (LEclo: clo <19= clo')
      (LEr: r <18= r') :
  @rclo18 clo' r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn18_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo18_mon clo:
  monotone18 (rclo18 clo).
Proof.
  repeat intro. eapply rclo18_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo18_clo clo r:
  clo (rclo18 clo r) <18= rclo18 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo18_step clo r:
  gf (rclo18 clo r) <18= rclo18 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo18_cpn clo r:
  cpn18 (rclo18 clo r) <18= rclo18 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo18_mult clo r:
  rclo18 clo (rclo18 clo r) <18= rclo18 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo18_compose clo r:
  rclo18 (rclo18 clo) r <18= rclo18 clo r.
Proof.
  intros. induction PR.
  - apply rclo18_base, R.
  - apply rclo18_mult.
    eapply rclo18_mon; [apply CLOR'|apply H].
  - apply rclo18_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo18_cpn.
    eapply cpn18_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat18_compat
      clo (WCOM: wcompatible18 clo):
  compatible18 (rclo18 clo).
Proof.
  econstructor; [eapply rclo18_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply R|]. intros.
    apply rclo18_base. apply PR.
  - eapply gf_mon.
    + eapply (wcompat18_wcompat WCOM).
      eapply (wcompat18_mon WCOM); [apply CLOR'|apply H].
    + intros. apply rclo18_mult, PR.
  - eapply gf_mon; [apply CLOR'|].
    intros. apply H in PR. apply rclo18_step, PR.
  - eapply gf_mon; [|intros; apply rclo18_cpn, PR].
    apply (compat18_compat cpn18_compat).
    eapply cpn18_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat18_sound clo (WCOM: wcompatible18 clo):
  clo <19= cpn18.
Proof.
  intros. exists (rclo18 clo).
  - apply wcompat18_compat, WCOM.
  - apply rclo18_clo.
    eapply (wcompat18_mon WCOM); [apply PR|].
    intros. apply rclo18_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn18_base: forall r, r <18= cpn18 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
  - apply PR.
Qed.

Lemma cpn18_from_upaco r:
  upaco18 gcpn18 r <18= cpn18 r.
Proof.
  intros. destruct PR; [| apply cpn18_base, H].
  exists (rclo18 (paco18 gcpn18)).
  - apply wcompat18_compat.
    econstructor; [apply paco18_mon|].
    intros. _punfold PR; [|apply gcpn18_mon].
    eapply gf_mon; [apply PR|].
    intros. apply rclo18_cpn.
    eapply cpn18_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo18_clo.
      eapply paco18_mon; [apply H0|].
      intros. apply rclo18_step.
      eapply gf_mon; [apply PR1|].
      intros. apply rclo18_base, PR2.
    + apply rclo18_step.
      eapply gf_mon; [apply H0|].
      intros. apply rclo18_base, PR1.
  - apply rclo18_clo.
    eapply paco18_mon; [apply H|].
    intros. apply rclo18_base, PR.
Qed.

Lemma cpn18_from_paco r:
  paco18 gcpn18 r <18= cpn18 r.
Proof. intros. apply cpn18_from_upaco. left. apply PR. Qed.

Lemma gcpn18_from_paco r:
  paco18 gcpn18 r <18= gcpn18 r.
Proof.
  intros. _punfold PR; [|apply gcpn18_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn18_comp.
  eapply cpn18_mon; [apply PR0|].
  apply cpn18_from_upaco.
Qed.

Lemma gcpn18_to_paco r:
  gcpn18 r <18= paco18 gcpn18 r.
Proof.
  intros. pfold. eapply gcpn18_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn18_init:
  cpn18 bot18 <18= paco18 gf bot18.
Proof.
  intros. apply gcpn18_sound, gcpn18_to_paco, (compat18_compat cpn18_compat).
  eapply cpn18_mon; [apply PR|contradiction].
Qed.

Lemma cpn18_clo
      r clo (LE: clo <19= cpn18):
  clo (cpn18 r) <18= cpn18 r.
Proof.
  intros. apply cpn18_comp, LE, PR.
Qed.

Lemma gcpn18_clo
      r clo (LE: clo <19= cpn18):
  clo (gcpn18 r) <18= gcpn18 r.
Proof.
  intros. apply LE, (compat18_compat cpn18_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn18_comp, PR0.
Qed.

Lemma cpn18_step r:
  gcpn18 r <18= cpn18 r.
Proof.
  intros. eapply cpn18_clo, PR.
  intros. eapply wcompat18_sound, PR0.
  econstructor; [apply gf_mon|].
  intros. eapply gf_mon; [apply PR1|].
  intros. apply rclo18_step.
  eapply gf_mon; [apply PR2|].
  intros. apply rclo18_base, PR3.
Qed.

Lemma cpn18_final: forall r, upaco18 gf r <18= cpn18 r.
Proof.
  intros. eapply cpn18_from_upaco.
  intros. eapply upaco18_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn18_base, PR1.
Qed.

Lemma gcpn18_final: forall r, paco18 gf r <18= gcpn18 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn18_final].
Qed.

Lemma cpn18_complete:
  paco18 gf bot18 <18= cpn18 bot18.
Proof.
  intros. apply cpn18_from_paco.
  eapply paco18_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn18_base].
  - intros. apply PR0.
Qed.

End Companion18.

Hint Resolve cpn18_base : paco.
Hint Resolve cpn18_mon : paco.
Hint Resolve gcpn18_mon : paco.
Hint Resolve rclo18_mon : paco.
Hint Resolve cpn18_final gcpn18_final : paco.

Hint Constructors cpn18 compatible18 wcompatible18.

Hint Constructors rclo18 : rclo.
Hint Resolve rclo18_clo rclo18_step rclo18_cpn : rclo.

