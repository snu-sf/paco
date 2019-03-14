Require Export Program.Basics. Open Scope program_scope.
Require Import paco16.
Set Implicit Arguments.

Section Companion16.

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

Local Notation rel := (rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone16 gf.

(** 
  Compatibility, Companion & Guarded Companion
*)

Structure compatible16 (clo: rel -> rel) : Prop :=
  compat16_intro {
      compat16_mon: monotone16 clo;
      compat16_compat : forall r,
          clo (gf r) <16= gf (clo r);
    }.

Inductive cpn16 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 : Prop :=
| cpn16_intro
    clo
    (COM: compatible16 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15)
.

Definition gcpn16 := compose gf cpn16.

Lemma cpn16_mon: monotone16 cpn16.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat16_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn16_compat: compatible16 cpn16.
Proof.
  econstructor; [apply cpn16_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat16_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn16_greatest: forall clo (COM: compatible16 clo), clo <17= cpn16.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn16_id: forall r, r <16= cpn16 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
  - apply PR.
Qed.

Lemma cpn16_comp: forall r,
    cpn16 (cpn16 r) <16= cpn16 r.
Proof.
  intros. exists (compose cpn16 cpn16); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn16_mon; [apply IN|].
    intros. eapply cpn16_mon; [apply PR0|apply LE].
  - intros. eapply (compat16_compat cpn16_compat).
    eapply cpn16_mon; [apply PR0|].
    intros. eapply (compat16_compat cpn16_compat), PR1. 
Qed.

Lemma gcpn16_mon: monotone16 gcpn16.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn16_mon; [apply PR|apply LE].
Qed.

Lemma gcpn16_sound:
  paco16 gcpn16 bot16 <16= paco16 gf bot16.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \16/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn16 n (paco16 gcpn16 bot16) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn16 n (paco16 gcpn16 bot16) <16= gf (rclo cpn16 (S n) (paco16 gcpn16 bot16))).
  { intro X. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply gcpn16_mon].
    + intros. right. eapply cpn16_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat16_compat cpn16_compat).
        eapply (compat16_mon cpn16_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo16 (clo: rel->rel) (r: rel): rel :=
| rclo16_id
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15):
    @rclo16 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
| rclo16_clo'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
    (R': r' <16= rclo16 clo r)
    (CLOR': clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15):
    @rclo16 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
| rclo16_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
    (R': r' <16= rclo16 clo r)
    (CLOR': @gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15):
    @rclo16 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
| rclo16_cpn'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
    (R': r' <16= rclo16 clo r)
    (CLOR': @cpn16 r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15):
    @rclo16 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
.

Structure wcompatible16 (clo: rel -> rel) : Prop :=
  wcompat16_intro {
      wcompat16_mon: monotone16 clo;
      wcompat16_wcompat: forall r,
          clo (gf r) <16= gf (rclo16 clo r);
    }.

Lemma rclo16_mon_gen clo clo' r r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
      (IN: @rclo16 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15)
      (LEclo: clo <17= clo')
      (LEr: r <16= r') :
  @rclo16 clo' r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn16_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo16_mon clo:
  monotone16 (rclo16 clo).
Proof.
  repeat intro. eapply rclo16_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo16_clo clo r:
  clo (rclo16 clo r) <16= rclo16 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo16_step clo r:
  gf (rclo16 clo r) <16= rclo16 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo16_cpn clo r:
  cpn16 (rclo16 clo r) <16= rclo16 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo16_mult clo r:
  rclo16 clo (rclo16 clo r) <16= rclo16 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo16_compose clo r:
  rclo16 (rclo16 clo) r <16= rclo16 clo r.
Proof.
  intros. induction PR.
  - apply rclo16_id, R.
  - apply rclo16_mult.
    eapply rclo16_mon; [apply CLOR'|apply H].
  - apply rclo16_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo16_cpn.
    eapply cpn16_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat16_compat
      clo (WCOM: wcompatible16 clo):
  compatible16 (rclo16 clo).
Proof.
  econstructor; [eapply rclo16_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply R|]. intros.
    apply rclo16_id. apply PR.
  - eapply gf_mon.
    + eapply (wcompat16_wcompat WCOM).
      eapply (wcompat16_mon WCOM); [apply CLOR'|apply H].
    + intros. apply rclo16_mult, PR.
  - eapply gf_mon; [apply CLOR'|].
    intros. apply H in PR. apply rclo16_step, PR.
  - eapply gf_mon; [|intros; apply rclo16_cpn, PR].
    apply (compat16_compat cpn16_compat).
    eapply cpn16_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat16_sound clo (WCOM: wcompatible16 clo):
  clo <17= cpn16.
Proof.
  intros. exists (rclo16 clo).
  - apply wcompat16_compat, WCOM.
  - apply rclo16_clo.
    eapply (wcompat16_mon WCOM); [apply PR|].
    intros. apply rclo16_id, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn16_from_upaco r:
  upaco16 gcpn16 r <16= cpn16 r.
Proof.
  intros. destruct PR; [| apply cpn16_id, H].
  exists (rclo16 (paco16 gcpn16)).
  - apply wcompat16_compat.
    econstructor; [apply paco16_mon|].
    intros. _punfold PR; [|apply gcpn16_mon].
    eapply gf_mon; [apply PR|].
    intros. apply rclo16_cpn.
    eapply cpn16_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo16_clo.
      eapply paco16_mon; [apply H0|].
      intros. apply rclo16_step.
      eapply gf_mon; [apply PR1|].
      intros. apply rclo16_id, PR2.
    + apply rclo16_step.
      eapply gf_mon; [apply H0|].
      intros. apply rclo16_id, PR1.
  - apply rclo16_clo.
    eapply paco16_mon; [apply H|].
    intros. apply rclo16_id, PR.
Qed.

Lemma cpn16_from_paco r:
  paco16 gcpn16 r <16= cpn16 r.
Proof. intros. apply cpn16_from_upaco. left. apply PR. Qed.

Lemma gcpn16_from_paco r:
  paco16 gcpn16 r <16= gcpn16 r.
Proof.
  intros. _punfold PR; [|apply gcpn16_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn16_comp.
  eapply cpn16_mon; [apply PR0|].
  apply cpn16_from_upaco.
Qed.

Lemma gcpn16_to_paco r:
  gcpn16 r <16= paco16 gcpn16 r.
Proof.
  intros. pfold. eapply gcpn16_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn16_init:
  cpn16 bot16 <16= paco16 gf bot16.
Proof.
  intros. apply gcpn16_sound, gcpn16_to_paco, (compat16_compat cpn16_compat).
  eapply cpn16_mon; [apply PR|contradiction].
Qed.

Lemma cpn16_clo
      r clo (LE: clo <17= cpn16):
  clo (cpn16 r) <16= cpn16 r.
Proof.
  intros. apply cpn16_comp, LE, PR.
Qed.

Lemma gcpn16_clo
      r clo (LE: clo <17= cpn16):
  clo (gcpn16 r) <16= gcpn16 r.
Proof.
  intros. apply LE, (compat16_compat cpn16_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn16_comp, PR0.
Qed.

Lemma cpn16_step r:
  gcpn16 r <16= cpn16 r.
Proof.
  intros. eapply cpn16_clo, PR.
  intros. eapply wcompat16_sound, PR0.
  econstructor; [apply gf_mon|].
  intros. eapply gf_mon; [apply PR1|].
  intros. apply rclo16_step.
  eapply gf_mon; [apply PR2|].
  intros. apply rclo16_id, PR3.
Qed.

Lemma cpn16_final: forall r, upaco16 gf r <16= cpn16 r.
Proof.
  intros. eapply cpn16_from_upaco.
  intros. eapply upaco16_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn16_id, PR1.
Qed.

Lemma gcpn16_final: forall r, paco16 gf r <16= gcpn16 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn16_final].
Qed.

Lemma cpn16_complete:
  paco16 gf bot16 <16= cpn16 bot16.
Proof.
  intros. apply cpn16_from_paco.
  eapply paco16_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn16_id].
  - intros. apply PR0.
Qed.

End Companion16.

Hint Resolve cpn16_mon : paco.
Hint Resolve gcpn16_mon : paco.
Hint Resolve rclo16_mon : paco.
Hint Resolve cpn16_final gcpn16_final : paco.

Hint Constructors cpn16 compatible16 wcompatible16.

Hint Constructors rclo16 : rclo.
Hint Resolve rclo16_clo rclo16_step rclo16_cpn : rclo.

