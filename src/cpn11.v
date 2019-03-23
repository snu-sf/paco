Require Export Program.Basics. Open Scope program_scope.
Require Import paco11 pacotac.
Set Implicit Arguments.

Section Companion11.

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

Local Notation rel := (rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10).

Section Companion11_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone11 gf.

(** 
  Compatibility, Companion & Guarded Companion
*)

Structure compatible11 (clo: rel -> rel) : Prop :=
  compat11_intro {
      compat11_mon: monotone11 clo;
      compat11_compat : forall r,
          clo (gf r) <11= gf (clo r);
    }.

Inductive cpn11 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 : Prop :=
| cpn11_intro
    clo
    (COM: compatible11 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)
.

Definition gcpn11 := compose gf cpn11.

Lemma cpn11_mon: monotone11 cpn11.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat11_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn11_compat: compatible11 cpn11.
Proof.
  econstructor; [apply cpn11_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat11_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn11_greatest: forall clo (COM: compatible11 clo), clo <12= cpn11.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn11_cpn: forall r,
    cpn11 (cpn11 r) <11= cpn11 r.
Proof.
  intros. exists (compose cpn11 cpn11); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn11_mon; [apply IN|].
    intros. eapply cpn11_mon; [apply PR0|apply LE].
  - intros. eapply (compat11_compat cpn11_compat).
    eapply cpn11_mon; [apply PR0|].
    intros. eapply (compat11_compat cpn11_compat), PR1. 
Qed.

Lemma gcpn11_mon: monotone11 gcpn11.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn11_mon; [apply PR|apply LE].
Qed.

Lemma gcpn11_sound:
  paco11 gcpn11 bot11 <11= paco11 gf bot11.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \11/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn11 n (paco11 gcpn11 bot11) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn11 n (paco11 gcpn11 bot11) <11= gf (rclo cpn11 (S n) (paco11 gcpn11 bot11))).
  { intro X. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply gcpn11_mon].
    + intros. right. eapply cpn11_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat11_compat cpn11_compat).
        eapply (compat11_mon cpn11_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo11 (clo: rel->rel) (r: rel): rel :=
| rclo11_base
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10):
    @rclo11 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
| rclo11_clo'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    (R': r' <11= rclo11 clo r)
    (CLOR': clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10):
    @rclo11 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
| rclo11_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    (R': r' <11= rclo11 clo r)
    (CLOR': @gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10):
    @rclo11 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
| rclo11_cpn'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    (R': r' <11= rclo11 clo r)
    (CLOR': @cpn11 r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10):
    @rclo11 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
.

Structure wcompatible11 (clo: rel -> rel) : Prop :=
  wcompat11_intro {
      wcompat11_mon: monotone11 clo;
      wcompat11_wcompat: forall r,
          clo (gf r) <11= gf (rclo11 clo r);
    }.

Lemma rclo11_mon_gen clo clo' r r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
      (IN: @rclo11 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)
      (LEclo: clo <12= clo')
      (LEr: r <11= r') :
  @rclo11 clo' r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn11_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo11_mon clo:
  monotone11 (rclo11 clo).
Proof.
  repeat intro. eapply rclo11_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo11_clo clo r:
  clo (rclo11 clo r) <11= rclo11 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo11_step clo r:
  gf (rclo11 clo r) <11= rclo11 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo11_cpn clo r:
  cpn11 (rclo11 clo r) <11= rclo11 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo11_mult clo r:
  rclo11 clo (rclo11 clo r) <11= rclo11 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo11_compose clo r:
  rclo11 (rclo11 clo) r <11= rclo11 clo r.
Proof.
  intros. induction PR.
  - apply rclo11_base, R.
  - apply rclo11_mult.
    eapply rclo11_mon; [apply CLOR'|apply H].
  - apply rclo11_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo11_cpn.
    eapply cpn11_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat11_compat
      clo (WCOM: wcompatible11 clo):
  compatible11 (rclo11 clo).
Proof.
  econstructor; [eapply rclo11_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply R|]. intros.
    apply rclo11_base. apply PR.
  - eapply gf_mon.
    + eapply (wcompat11_wcompat WCOM).
      eapply (wcompat11_mon WCOM); [apply CLOR'|apply H].
    + intros. apply rclo11_mult, PR.
  - eapply gf_mon; [apply CLOR'|].
    intros. apply H in PR. apply rclo11_step, PR.
  - eapply gf_mon; [|intros; apply rclo11_cpn, PR].
    apply (compat11_compat cpn11_compat).
    eapply cpn11_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat11_sound clo (WCOM: wcompatible11 clo):
  clo <12= cpn11.
Proof.
  intros. exists (rclo11 clo).
  - apply wcompat11_compat, WCOM.
  - apply rclo11_clo.
    eapply (wcompat11_mon WCOM); [apply PR|].
    intros. apply rclo11_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn11_base: forall r, r <11= cpn11 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
  - apply PR.
Qed.

Lemma cpn11_from_upaco r:
  upaco11 gcpn11 r <11= cpn11 r.
Proof.
  intros. destruct PR; [| apply cpn11_base, H].
  exists (rclo11 (paco11 gcpn11)).
  - apply wcompat11_compat.
    econstructor; [apply paco11_mon|].
    intros. _punfold PR; [|apply gcpn11_mon].
    eapply gf_mon; [apply PR|].
    intros. apply rclo11_cpn.
    eapply cpn11_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo11_clo.
      eapply paco11_mon; [apply H0|].
      intros. apply rclo11_step.
      eapply gf_mon; [apply PR1|].
      intros. apply rclo11_base, PR2.
    + apply rclo11_step.
      eapply gf_mon; [apply H0|].
      intros. apply rclo11_base, PR1.
  - apply rclo11_clo.
    eapply paco11_mon; [apply H|].
    intros. apply rclo11_base, PR.
Qed.

Lemma cpn11_from_paco r:
  paco11 gcpn11 r <11= cpn11 r.
Proof. intros. apply cpn11_from_upaco. left. apply PR. Qed.

Lemma gcpn11_from_paco r:
  paco11 gcpn11 r <11= gcpn11 r.
Proof.
  intros. _punfold PR; [|apply gcpn11_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn11_cpn.
  eapply cpn11_mon; [apply PR0|].
  apply cpn11_from_upaco.
Qed.

Lemma gcpn11_to_paco r:
  gcpn11 r <11= paco11 gcpn11 r.
Proof.
  intros. pfold. eapply gcpn11_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn11_complete:
  paco11 gf bot11 <11= cpn11 bot11.
Proof.
  intros. apply cpn11_from_paco.
  eapply paco11_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn11_base].
  - intros. apply PR0.
Qed.

Lemma cpn11_init:
  cpn11 bot11 <11= paco11 gf bot11.
Proof.
  intros. apply gcpn11_sound, gcpn11_to_paco, (compat11_compat cpn11_compat).
  eapply cpn11_mon; [apply PR|contradiction].
Qed.

Lemma cpn11_clo
      r clo (LE: clo <12= cpn11):
  clo (cpn11 r) <11= cpn11 r.
Proof.
  intros. apply cpn11_cpn, LE, PR.
Qed.

Lemma cpn11_unfold:
  cpn11 bot11 <11= gcpn11 bot11.
Proof.
  intros. apply cpn11_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn11_complete, PR0.
Qed.

Lemma cpn11_step r:
  gcpn11 r <11= cpn11 r.
Proof.
  intros. eapply cpn11_clo, PR.
  intros. eapply wcompat11_sound, PR0.
  econstructor; [apply gf_mon|].
  intros. eapply gf_mon; [apply PR1|].
  intros. apply rclo11_step.
  eapply gf_mon; [apply PR2|].
  intros. apply rclo11_base, PR3.
Qed.

Lemma gcpn11_clo
      r clo (LE: clo <12= cpn11):
  clo (gcpn11 r) <11= gcpn11 r.
Proof.
  intros. apply LE, (compat11_compat cpn11_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn11_cpn, PR0.
Qed.

Lemma cpn11_final: forall r, upaco11 gf r <11= cpn11 r.
Proof.
  intros. eapply cpn11_from_upaco.
  intros. eapply upaco11_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn11_base, PR1.
Qed.

Lemma gcpn11_final: forall r, paco11 gf r <11= gcpn11 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn11_final].
Qed.

Lemma cpn11_algebra r :
  r <11= gf r -> r <11= cpn11 bot11.
Proof.
  intros. apply cpn11_final. left.
  revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion11_main.

Lemma cpn11_mon_bot (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 r
      (IN: @cpn11 gf bot11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)
      (MONgf: monotone11 gf)
      (MONgf': monotone11 gf')
      (LE: gf <12= gf'):
  @cpn11 gf' r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
Proof.
  apply cpn11_init in IN; [|apply MONgf].
  apply cpn11_final; [apply MONgf'|].
  left. eapply paco11_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma gcpn11_mon_bot (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 r
      (IN: @gcpn11 gf bot11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)
      (MONgf: monotone11 gf)
      (MONgf': monotone11 gf')
      (LE: gf <12= gf'):
  @gcpn11 gf' r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
Proof.
  apply LE. eapply MONgf. apply IN.
  intros. eapply cpn11_mon_bot; eassumption.
Qed.

End Companion11.

Hint Unfold gcpn11 : paco.

Hint Resolve cpn11_base : paco.
Hint Resolve cpn11_step : paco.
Hint Resolve cpn11_final gcpn11_final : paco.
(* Hint Resolve cpn11_mon : paco.
Hint Resolve gcpn11_mon : paco.
Hint Resolve rclo11_mon : paco. *)

Hint Constructors cpn11 compatible11 wcompatible11.

Hint Constructors rclo11 : rclo.
Hint Resolve rclo11_clo rclo11_step rclo11_cpn : rclo.

