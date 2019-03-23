Require Export Program.Basics. Open Scope program_scope.
Require Import paco13 pacotac.
Set Implicit Arguments.

Section Companion13.

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

Local Notation rel := (rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12).

Section Companion13_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone13 gf.

(** 
  Compatibility, Companion & Guarded Companion
*)

Structure compatible13 (clo: rel -> rel) : Prop :=
  compat13_intro {
      compat13_mon: monotone13 clo;
      compat13_compat : forall r,
          clo (gf r) <13= gf (clo r);
    }.

Inductive cpn13 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 : Prop :=
| cpn13_intro
    clo
    (COM: compatible13 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12)
.

Definition gcpn13 := compose gf cpn13.

Lemma cpn13_mon: monotone13 cpn13.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat13_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn13_compat: compatible13 cpn13.
Proof.
  econstructor; [apply cpn13_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat13_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn13_greatest: forall clo (COM: compatible13 clo), clo <14= cpn13.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn13_cpn: forall r,
    cpn13 (cpn13 r) <13= cpn13 r.
Proof.
  intros. exists (compose cpn13 cpn13); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn13_mon; [apply IN|].
    intros. eapply cpn13_mon; [apply PR0|apply LE].
  - intros. eapply (compat13_compat cpn13_compat).
    eapply cpn13_mon; [apply PR0|].
    intros. eapply (compat13_compat cpn13_compat), PR1. 
Qed.

Lemma gcpn13_mon: monotone13 gcpn13.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn13_mon; [apply PR|apply LE].
Qed.

Lemma gcpn13_sound:
  paco13 gcpn13 bot13 <13= paco13 gf bot13.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \13/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn13 n (paco13 gcpn13 bot13) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn13 n (paco13 gcpn13 bot13) <13= gf (rclo cpn13 (S n) (paco13 gcpn13 bot13))).
  { intro X. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply gcpn13_mon].
    + intros. right. eapply cpn13_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat13_compat cpn13_compat).
        eapply (compat13_mon cpn13_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo13 (clo: rel->rel) (r: rel): rel :=
| rclo13_base
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12):
    @rclo13 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
| rclo13_clo'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
    (R': r' <13= rclo13 clo r)
    (CLOR': clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12):
    @rclo13 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
| rclo13_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
    (R': r' <13= rclo13 clo r)
    (CLOR': @gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12):
    @rclo13 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
| rclo13_cpn'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
    (R': r' <13= rclo13 clo r)
    (CLOR': @cpn13 r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12):
    @rclo13 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
.

Structure wcompatible13 (clo: rel -> rel) : Prop :=
  wcompat13_intro {
      wcompat13_mon: monotone13 clo;
      wcompat13_wcompat: forall r,
          clo (gf r) <13= gf (rclo13 clo r);
    }.

Lemma rclo13_mon_gen clo clo' r r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
      (IN: @rclo13 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12)
      (LEclo: clo <14= clo')
      (LEr: r <13= r') :
  @rclo13 clo' r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn13_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo13_mon clo:
  monotone13 (rclo13 clo).
Proof.
  repeat intro. eapply rclo13_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo13_clo clo r:
  clo (rclo13 clo r) <13= rclo13 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo13_step clo r:
  gf (rclo13 clo r) <13= rclo13 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo13_cpn clo r:
  cpn13 (rclo13 clo r) <13= rclo13 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo13_mult clo r:
  rclo13 clo (rclo13 clo r) <13= rclo13 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo13_compose clo r:
  rclo13 (rclo13 clo) r <13= rclo13 clo r.
Proof.
  intros. induction PR.
  - apply rclo13_base, R.
  - apply rclo13_mult.
    eapply rclo13_mon; [apply CLOR'|apply H].
  - apply rclo13_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo13_cpn.
    eapply cpn13_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat13_compat
      clo (WCOM: wcompatible13 clo):
  compatible13 (rclo13 clo).
Proof.
  econstructor; [eapply rclo13_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply R|]. intros.
    apply rclo13_base. apply PR.
  - eapply gf_mon.
    + eapply (wcompat13_wcompat WCOM).
      eapply (wcompat13_mon WCOM); [apply CLOR'|apply H].
    + intros. apply rclo13_mult, PR.
  - eapply gf_mon; [apply CLOR'|].
    intros. apply H in PR. apply rclo13_step, PR.
  - eapply gf_mon; [|intros; apply rclo13_cpn, PR].
    apply (compat13_compat cpn13_compat).
    eapply cpn13_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat13_sound clo (WCOM: wcompatible13 clo):
  clo <14= cpn13.
Proof.
  intros. exists (rclo13 clo).
  - apply wcompat13_compat, WCOM.
  - apply rclo13_clo.
    eapply (wcompat13_mon WCOM); [apply PR|].
    intros. apply rclo13_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn13_base: forall r, r <13= cpn13 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
  - apply PR.
Qed.

Lemma cpn13_from_upaco r:
  upaco13 gcpn13 r <13= cpn13 r.
Proof.
  intros. destruct PR; [| apply cpn13_base, H].
  exists (rclo13 (paco13 gcpn13)).
  - apply wcompat13_compat.
    econstructor; [apply paco13_mon|].
    intros. _punfold PR; [|apply gcpn13_mon].
    eapply gf_mon; [apply PR|].
    intros. apply rclo13_cpn.
    eapply cpn13_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo13_clo.
      eapply paco13_mon; [apply H0|].
      intros. apply rclo13_step.
      eapply gf_mon; [apply PR1|].
      intros. apply rclo13_base, PR2.
    + apply rclo13_step.
      eapply gf_mon; [apply H0|].
      intros. apply rclo13_base, PR1.
  - apply rclo13_clo.
    eapply paco13_mon; [apply H|].
    intros. apply rclo13_base, PR.
Qed.

Lemma cpn13_from_paco r:
  paco13 gcpn13 r <13= cpn13 r.
Proof. intros. apply cpn13_from_upaco. left. apply PR. Qed.

Lemma gcpn13_from_paco r:
  paco13 gcpn13 r <13= gcpn13 r.
Proof.
  intros. _punfold PR; [|apply gcpn13_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn13_cpn.
  eapply cpn13_mon; [apply PR0|].
  apply cpn13_from_upaco.
Qed.

Lemma gcpn13_to_paco r:
  gcpn13 r <13= paco13 gcpn13 r.
Proof.
  intros. pfold. eapply gcpn13_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn13_complete:
  paco13 gf bot13 <13= cpn13 bot13.
Proof.
  intros. apply cpn13_from_paco.
  eapply paco13_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn13_base].
  - intros. apply PR0.
Qed.

Lemma cpn13_init:
  cpn13 bot13 <13= paco13 gf bot13.
Proof.
  intros. apply gcpn13_sound, gcpn13_to_paco, (compat13_compat cpn13_compat).
  eapply cpn13_mon; [apply PR|contradiction].
Qed.

Lemma cpn13_clo
      r clo (LE: clo <14= cpn13):
  clo (cpn13 r) <13= cpn13 r.
Proof.
  intros. apply cpn13_cpn, LE, PR.
Qed.

Lemma cpn13_unfold:
  cpn13 bot13 <13= gcpn13 bot13.
Proof.
  intros. apply cpn13_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn13_complete, PR0.
Qed.

Lemma cpn13_step r:
  gcpn13 r <13= cpn13 r.
Proof.
  intros. eapply cpn13_clo, PR.
  intros. eapply wcompat13_sound, PR0.
  econstructor; [apply gf_mon|].
  intros. eapply gf_mon; [apply PR1|].
  intros. apply rclo13_step.
  eapply gf_mon; [apply PR2|].
  intros. apply rclo13_base, PR3.
Qed.

Lemma gcpn13_clo
      r clo (LE: clo <14= cpn13):
  clo (gcpn13 r) <13= gcpn13 r.
Proof.
  intros. apply LE, (compat13_compat cpn13_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn13_cpn, PR0.
Qed.

Lemma cpn13_final: forall r, upaco13 gf r <13= cpn13 r.
Proof.
  intros. eapply cpn13_from_upaco.
  intros. eapply upaco13_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn13_base, PR1.
Qed.

Lemma gcpn13_final: forall r, paco13 gf r <13= gcpn13 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn13_final].
Qed.

Lemma cpn13_algebra r :
  r <13= gf r -> r <13= cpn13 bot13.
Proof.
  intros. apply cpn13_final. left.
  revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion13_main.

Lemma cpn13_mon_bot (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 r
      (IN: @cpn13 gf bot13 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12)
      (MONgf: monotone13 gf)
      (MONgf': monotone13 gf')
      (LE: gf <14= gf'):
  @cpn13 gf' r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
Proof.
  apply cpn13_init in IN; [|apply MONgf].
  apply cpn13_final; [apply MONgf'|].
  left. eapply paco13_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma gcpn13_mon_bot (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 r
      (IN: @gcpn13 gf bot13 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12)
      (MONgf: monotone13 gf)
      (MONgf': monotone13 gf')
      (LE: gf <14= gf'):
  @gcpn13 gf' r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
Proof.
  apply LE. eapply MONgf. apply IN.
  intros. eapply cpn13_mon_bot; eassumption.
Qed.

End Companion13.

Hint Unfold gcpn13 : paco.

Hint Resolve cpn13_base : paco.
Hint Resolve cpn13_step : paco.
Hint Resolve cpn13_final gcpn13_final : paco.
(* Hint Resolve cpn13_mon : paco.
Hint Resolve gcpn13_mon : paco.
Hint Resolve rclo13_mon : paco. *)

Hint Constructors cpn13 compatible13 wcompatible13.

Hint Constructors rclo13 : rclo.
Hint Resolve rclo13_clo rclo13_step rclo13_cpn : rclo.

