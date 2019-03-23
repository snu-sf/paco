Require Export Program.Basics. Open Scope program_scope.
Require Import paco9 pacotac.
Set Implicit Arguments.

Section Companion9.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.

Local Notation rel := (rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8).

Section Companion9_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone9 gf.

(** 
  Compatibility, Companion & Guarded Companion
*)

Structure compatible9 (clo: rel -> rel) : Prop :=
  compat9_intro {
      compat9_mon: monotone9 clo;
      compat9_compat : forall r,
          clo (gf r) <9= gf (clo r);
    }.

Inductive cpn9 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 : Prop :=
| cpn9_intro
    clo
    (COM: compatible9 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8)
.

Definition gcpn9 := compose gf cpn9.

Lemma cpn9_mon: monotone9 cpn9.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat9_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn9_compat: compatible9 cpn9.
Proof.
  econstructor; [apply cpn9_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat9_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn9_greatest: forall clo (COM: compatible9 clo), clo <10= cpn9.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn9_cpn: forall r,
    cpn9 (cpn9 r) <9= cpn9 r.
Proof.
  intros. exists (compose cpn9 cpn9); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn9_mon; [apply IN|].
    intros. eapply cpn9_mon; [apply PR0|apply LE].
  - intros. eapply (compat9_compat cpn9_compat).
    eapply cpn9_mon; [apply PR0|].
    intros. eapply (compat9_compat cpn9_compat), PR1. 
Qed.

Lemma gcpn9_mon: monotone9 gcpn9.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn9_mon; [apply PR|apply LE].
Qed.

Lemma gcpn9_sound:
  paco9 gcpn9 bot9 <9= paco9 gf bot9.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \9/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn9 n (paco9 gcpn9 bot9) x0 x1 x2 x3 x4 x5 x6 x7 x8) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn9 n (paco9 gcpn9 bot9) <9= gf (rclo cpn9 (S n) (paco9 gcpn9 bot9))).
  { intro X. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply gcpn9_mon].
    + intros. right. eapply cpn9_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat9_compat cpn9_compat).
        eapply (compat9_mon cpn9_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo9 (clo: rel->rel) (r: rel): rel :=
| rclo9_base
    e0 e1 e2 e3 e4 e5 e6 e7 e8
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8):
    @rclo9 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8
| rclo9_clo'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8
    (R': r' <9= rclo9 clo r)
    (CLOR': clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8):
    @rclo9 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8
| rclo9_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8
    (R': r' <9= rclo9 clo r)
    (CLOR': @gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8):
    @rclo9 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8
| rclo9_cpn'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8
    (R': r' <9= rclo9 clo r)
    (CLOR': @cpn9 r' e0 e1 e2 e3 e4 e5 e6 e7 e8):
    @rclo9 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8
.

Structure wcompatible9 (clo: rel -> rel) : Prop :=
  wcompat9_intro {
      wcompat9_mon: monotone9 clo;
      wcompat9_wcompat: forall r,
          clo (gf r) <9= gf (rclo9 clo r);
    }.

Lemma rclo9_mon_gen clo clo' r r' e0 e1 e2 e3 e4 e5 e6 e7 e8
      (IN: @rclo9 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8)
      (LEclo: clo <10= clo')
      (LEr: r <9= r') :
  @rclo9 clo' r' e0 e1 e2 e3 e4 e5 e6 e7 e8.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn9_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo9_mon clo:
  monotone9 (rclo9 clo).
Proof.
  repeat intro. eapply rclo9_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo9_clo clo r:
  clo (rclo9 clo r) <9= rclo9 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo9_step clo r:
  gf (rclo9 clo r) <9= rclo9 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo9_cpn clo r:
  cpn9 (rclo9 clo r) <9= rclo9 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo9_mult clo r:
  rclo9 clo (rclo9 clo r) <9= rclo9 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo9_compose clo r:
  rclo9 (rclo9 clo) r <9= rclo9 clo r.
Proof.
  intros. induction PR.
  - apply rclo9_base, R.
  - apply rclo9_mult.
    eapply rclo9_mon; [apply CLOR'|apply H].
  - apply rclo9_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo9_cpn.
    eapply cpn9_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat9_compat
      clo (WCOM: wcompatible9 clo):
  compatible9 (rclo9 clo).
Proof.
  econstructor; [eapply rclo9_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply R|]. intros.
    apply rclo9_base. apply PR.
  - eapply gf_mon.
    + eapply (wcompat9_wcompat WCOM).
      eapply (wcompat9_mon WCOM); [apply CLOR'|apply H].
    + intros. apply rclo9_mult, PR.
  - eapply gf_mon; [apply CLOR'|].
    intros. apply H in PR. apply rclo9_step, PR.
  - eapply gf_mon; [|intros; apply rclo9_cpn, PR].
    apply (compat9_compat cpn9_compat).
    eapply cpn9_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat9_sound clo (WCOM: wcompatible9 clo):
  clo <10= cpn9.
Proof.
  intros. exists (rclo9 clo).
  - apply wcompat9_compat, WCOM.
  - apply rclo9_clo.
    eapply (wcompat9_mon WCOM); [apply PR|].
    intros. apply rclo9_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn9_base: forall r, r <9= cpn9 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
  - apply PR.
Qed.

Lemma cpn9_from_upaco r:
  upaco9 gcpn9 r <9= cpn9 r.
Proof.
  intros. destruct PR; [| apply cpn9_base, H].
  exists (rclo9 (paco9 gcpn9)).
  - apply wcompat9_compat.
    econstructor; [apply paco9_mon|].
    intros. _punfold PR; [|apply gcpn9_mon].
    eapply gf_mon; [apply PR|].
    intros. apply rclo9_cpn.
    eapply cpn9_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo9_clo.
      eapply paco9_mon; [apply H0|].
      intros. apply rclo9_step.
      eapply gf_mon; [apply PR1|].
      intros. apply rclo9_base, PR2.
    + apply rclo9_step.
      eapply gf_mon; [apply H0|].
      intros. apply rclo9_base, PR1.
  - apply rclo9_clo.
    eapply paco9_mon; [apply H|].
    intros. apply rclo9_base, PR.
Qed.

Lemma cpn9_from_paco r:
  paco9 gcpn9 r <9= cpn9 r.
Proof. intros. apply cpn9_from_upaco. left. apply PR. Qed.

Lemma gcpn9_from_paco r:
  paco9 gcpn9 r <9= gcpn9 r.
Proof.
  intros. _punfold PR; [|apply gcpn9_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn9_cpn.
  eapply cpn9_mon; [apply PR0|].
  apply cpn9_from_upaco.
Qed.

Lemma gcpn9_to_paco r:
  gcpn9 r <9= paco9 gcpn9 r.
Proof.
  intros. pfold. eapply gcpn9_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn9_complete:
  paco9 gf bot9 <9= cpn9 bot9.
Proof.
  intros. apply cpn9_from_paco.
  eapply paco9_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn9_base].
  - intros. apply PR0.
Qed.

Lemma cpn9_init:
  cpn9 bot9 <9= paco9 gf bot9.
Proof.
  intros. apply gcpn9_sound, gcpn9_to_paco, (compat9_compat cpn9_compat).
  eapply cpn9_mon; [apply PR|contradiction].
Qed.

Lemma cpn9_clo
      r clo (LE: clo <10= cpn9):
  clo (cpn9 r) <9= cpn9 r.
Proof.
  intros. apply cpn9_cpn, LE, PR.
Qed.

Lemma cpn9_unfold:
  cpn9 bot9 <9= gcpn9 bot9.
Proof.
  intros. apply cpn9_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn9_complete, PR0.
Qed.

Lemma cpn9_step r:
  gcpn9 r <9= cpn9 r.
Proof.
  intros. eapply cpn9_clo, PR.
  intros. eapply wcompat9_sound, PR0.
  econstructor; [apply gf_mon|].
  intros. eapply gf_mon; [apply PR1|].
  intros. apply rclo9_step.
  eapply gf_mon; [apply PR2|].
  intros. apply rclo9_base, PR3.
Qed.

Lemma gcpn9_clo
      r clo (LE: clo <10= cpn9):
  clo (gcpn9 r) <9= gcpn9 r.
Proof.
  intros. apply LE, (compat9_compat cpn9_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn9_cpn, PR0.
Qed.

Lemma cpn9_final: forall r, upaco9 gf r <9= cpn9 r.
Proof.
  intros. eapply cpn9_from_upaco.
  intros. eapply upaco9_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn9_base, PR1.
Qed.

Lemma gcpn9_final: forall r, paco9 gf r <9= gcpn9 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn9_final].
Qed.

Lemma cpn9_algebra r :
  r <9= gf r -> r <9= cpn9 bot9.
Proof.
  intros. apply cpn9_final. left.
  revert x0 x1 x2 x3 x4 x5 x6 x7 x8 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion9_main.

Lemma cpn9_mon_bot (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 r
      (IN: @cpn9 gf bot9 e0 e1 e2 e3 e4 e5 e6 e7 e8)
      (MONgf: monotone9 gf)
      (MONgf': monotone9 gf')
      (LE: gf <10= gf'):
  @cpn9 gf' r e0 e1 e2 e3 e4 e5 e6 e7 e8.
Proof.
  apply cpn9_init in IN; [|apply MONgf].
  apply cpn9_final; [apply MONgf'|].
  left. eapply paco9_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma gcpn9_mon_bot (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 r
      (IN: @gcpn9 gf bot9 e0 e1 e2 e3 e4 e5 e6 e7 e8)
      (MONgf: monotone9 gf)
      (MONgf': monotone9 gf')
      (LE: gf <10= gf'):
  @gcpn9 gf' r e0 e1 e2 e3 e4 e5 e6 e7 e8.
Proof.
  apply LE. eapply MONgf. apply IN.
  intros. eapply cpn9_mon_bot; eassumption.
Qed.

End Companion9.

Hint Unfold gcpn9 : paco.

Hint Resolve cpn9_base : paco.
Hint Resolve cpn9_step : paco.
Hint Resolve cpn9_final gcpn9_final : paco.
(* Hint Resolve cpn9_mon : paco.
Hint Resolve gcpn9_mon : paco.
Hint Resolve rclo9_mon : paco. *)

Hint Constructors cpn9 compatible9 wcompatible9.

Hint Constructors rclo9 : rclo.
Hint Resolve rclo9_clo rclo9_step rclo9_cpn : rclo.

