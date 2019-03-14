Require Export Program.Basics. Open Scope program_scope.
Require Import paco17.
Set Implicit Arguments.

Section Companion17.

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

Local Notation rel := (rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone17 gf.

(** 
  Compatibility, Companion & Guarded Companion
*)

Structure compatible17 (clo: rel -> rel) : Prop :=
  compat17_intro {
      compat17_mon: monotone17 clo;
      compat17_compat : forall r,
          clo (gf r) <17= gf (clo r);
    }.

Inductive cpn17 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 : Prop :=
| cpn17_intro
    clo
    (COM: compatible17 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16)
.

Definition gcpn17 := compose gf cpn17.

Lemma cpn17_mon: monotone17 cpn17.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat17_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn17_compat: compatible17 cpn17.
Proof.
  econstructor; [apply cpn17_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat17_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn17_greatest: forall clo (COM: compatible17 clo), clo <18= cpn17.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn17_id: forall r, r <17= cpn17 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
  - apply PR.
Qed.

Lemma cpn17_comp: forall r,
    cpn17 (cpn17 r) <17= cpn17 r.
Proof.
  intros. exists (compose cpn17 cpn17); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn17_mon; [apply IN|].
    intros. eapply cpn17_mon; [apply PR0|apply LE].
  - intros. eapply (compat17_compat cpn17_compat).
    eapply cpn17_mon; [apply PR0|].
    intros. eapply (compat17_compat cpn17_compat), PR1. 
Qed.

Lemma gcpn17_mon: monotone17 gcpn17.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn17_mon; [apply PR|apply LE].
Qed.

Lemma gcpn17_sound:
  paco17 gcpn17 bot17 <17= paco17 gf bot17.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \17/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn17 n (paco17 gcpn17 bot17) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn17 n (paco17 gcpn17 bot17) <17= gf (rclo cpn17 (S n) (paco17 gcpn17 bot17))).
  { intro X. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply gcpn17_mon].
    + intros. right. eapply cpn17_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat17_compat cpn17_compat).
        eapply (compat17_mon cpn17_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo17 (clo: rel->rel) (r: rel): rel :=
| rclo17_id
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16):
    @rclo17 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16
| rclo17_clo'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16
    (R': r' <17= rclo17 clo r)
    (CLOR': clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16):
    @rclo17 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16
| rclo17_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16
    (R': r' <17= rclo17 clo r)
    (CLOR': @gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16):
    @rclo17 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16
| rclo17_cpn'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16
    (R': r' <17= rclo17 clo r)
    (CLOR': @cpn17 r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16):
    @rclo17 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16
.

Structure wcompatible17 (clo: rel -> rel) : Prop :=
  wcompat17_intro {
      wcompat17_mon: monotone17 clo;
      wcompat17_wcompat: forall r,
          clo (gf r) <17= gf (rclo17 clo r);
    }.

Lemma rclo17_mon_gen clo clo' r r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16
      (IN: @rclo17 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16)
      (LEclo: clo <18= clo')
      (LEr: r <17= r') :
  @rclo17 clo' r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn17_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo17_mon clo:
  monotone17 (rclo17 clo).
Proof.
  repeat intro. eapply rclo17_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo17_clo clo r:
  clo (rclo17 clo r) <17= rclo17 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo17_step clo r:
  gf (rclo17 clo r) <17= rclo17 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo17_cpn clo r:
  cpn17 (rclo17 clo r) <17= rclo17 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo17_mult clo r:
  rclo17 clo (rclo17 clo r) <17= rclo17 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo17_compose clo r:
  rclo17 (rclo17 clo) r <17= rclo17 clo r.
Proof.
  intros. induction PR.
  - apply rclo17_id, R.
  - apply rclo17_mult.
    eapply rclo17_mon; [apply CLOR'|apply H].
  - apply rclo17_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo17_cpn.
    eapply cpn17_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat17_compat
      clo (WCOM: wcompatible17 clo):
  compatible17 (rclo17 clo).
Proof.
  econstructor; [eapply rclo17_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply R|]. intros.
    apply rclo17_id. apply PR.
  - eapply gf_mon.
    + eapply (wcompat17_wcompat WCOM).
      eapply (wcompat17_mon WCOM); [apply CLOR'|apply H].
    + intros. apply rclo17_mult, PR.
  - eapply gf_mon; [apply CLOR'|].
    intros. apply H in PR. apply rclo17_step, PR.
  - eapply gf_mon; [|intros; apply rclo17_cpn, PR].
    apply (compat17_compat cpn17_compat).
    eapply cpn17_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat17_sound clo (WCOM: wcompatible17 clo):
  clo <18= cpn17.
Proof.
  intros. exists (rclo17 clo).
  - apply wcompat17_compat, WCOM.
  - apply rclo17_clo.
    eapply (wcompat17_mon WCOM); [apply PR|].
    intros. apply rclo17_id, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn17_from_upaco r:
  upaco17 gcpn17 r <17= cpn17 r.
Proof.
  intros. destruct PR; [| apply cpn17_id, H].
  exists (rclo17 (paco17 gcpn17)).
  - apply wcompat17_compat.
    econstructor; [apply paco17_mon|].
    intros. _punfold PR; [|apply gcpn17_mon].
    eapply gf_mon; [apply PR|].
    intros. apply rclo17_cpn.
    eapply cpn17_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo17_clo.
      eapply paco17_mon; [apply H0|].
      intros. apply rclo17_step.
      eapply gf_mon; [apply PR1|].
      intros. apply rclo17_id, PR2.
    + apply rclo17_step.
      eapply gf_mon; [apply H0|].
      intros. apply rclo17_id, PR1.
  - apply rclo17_clo.
    eapply paco17_mon; [apply H|].
    intros. apply rclo17_id, PR.
Qed.

Lemma cpn17_from_paco r:
  paco17 gcpn17 r <17= cpn17 r.
Proof. intros. apply cpn17_from_upaco. left. apply PR. Qed.

Lemma gcpn17_from_paco r:
  paco17 gcpn17 r <17= gcpn17 r.
Proof.
  intros. _punfold PR; [|apply gcpn17_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn17_comp.
  eapply cpn17_mon; [apply PR0|].
  apply cpn17_from_upaco.
Qed.

Lemma gcpn17_to_paco r:
  gcpn17 r <17= paco17 gcpn17 r.
Proof.
  intros. pfold. eapply gcpn17_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn17_init:
  cpn17 bot17 <17= paco17 gf bot17.
Proof.
  intros. apply gcpn17_sound, gcpn17_to_paco, (compat17_compat cpn17_compat).
  eapply cpn17_mon; [apply PR|contradiction].
Qed.

Lemma cpn17_clo
      r clo (LE: clo <18= cpn17):
  clo (cpn17 r) <17= cpn17 r.
Proof.
  intros. apply cpn17_comp, LE, PR.
Qed.

Lemma gcpn17_clo
      r clo (LE: clo <18= cpn17):
  clo (gcpn17 r) <17= gcpn17 r.
Proof.
  intros. apply LE, (compat17_compat cpn17_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn17_comp, PR0.
Qed.

Lemma cpn17_step r:
  gcpn17 r <17= cpn17 r.
Proof.
  intros. eapply cpn17_clo, PR.
  intros. eapply wcompat17_sound, PR0.
  econstructor; [apply gf_mon|].
  intros. eapply gf_mon; [apply PR1|].
  intros. apply rclo17_step.
  eapply gf_mon; [apply PR2|].
  intros. apply rclo17_id, PR3.
Qed.

Lemma cpn17_final: forall r, upaco17 gf r <17= cpn17 r.
Proof.
  intros. eapply cpn17_from_upaco.
  intros. eapply upaco17_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn17_id, PR1.
Qed.

Lemma gcpn17_final: forall r, paco17 gf r <17= gcpn17 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn17_final].
Qed.

Lemma cpn17_complete:
  paco17 gf bot17 <17= cpn17 bot17.
Proof.
  intros. apply cpn17_from_paco.
  eapply paco17_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn17_id].
  - intros. apply PR0.
Qed.

End Companion17.

Hint Resolve cpn17_mon : paco.
Hint Resolve gcpn17_mon : paco.
Hint Resolve rclo17_mon : paco.
Hint Resolve cpn17_final gcpn17_final : paco.

Hint Constructors cpn17 compatible17 wcompatible17.

Hint Constructors rclo17 : rclo.
Hint Resolve rclo17_clo rclo17_step rclo17_cpn : rclo.

