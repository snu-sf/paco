Require Export Program.Basics. Open Scope program_scope.
Require Import paco4 pacotac.
Set Implicit Arguments.

Section Companion4.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.

Local Notation rel := (rel4 T0 T1 T2 T3).

Section Companion4_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone4 gf.

(** 
  Compatibility, Companion & Guarded Companion
*)

Structure compatible4 (clo: rel -> rel) : Prop :=
  compat4_intro {
      compat4_mon: monotone4 clo;
      compat4_compat : forall r,
          clo (gf r) <4= gf (clo r);
    }.

Inductive cpn4 (r: rel) e0 e1 e2 e3 : Prop :=
| cpn4_intro
    clo
    (COM: compatible4 clo)
    (CLO: clo r e0 e1 e2 e3)
.

Definition gcpn4 := compose gf cpn4.

Lemma cpn4_mon: monotone4 cpn4.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat4_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn4_compat: compatible4 cpn4.
Proof.
  econstructor; [apply cpn4_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat4_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn4_greatest: forall clo (COM: compatible4 clo), clo <5= cpn4.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn4_cpn: forall r,
    cpn4 (cpn4 r) <4= cpn4 r.
Proof.
  intros. exists (compose cpn4 cpn4); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn4_mon; [apply IN|].
    intros. eapply cpn4_mon; [apply PR0|apply LE].
  - intros. eapply (compat4_compat cpn4_compat).
    eapply cpn4_mon; [apply PR0|].
    intros. eapply (compat4_compat cpn4_compat), PR1. 
Qed.

Lemma gcpn4_mon: monotone4 gcpn4.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn4_mon; [apply PR|apply LE].
Qed.

Lemma gcpn4_sound:
  paco4 gcpn4 bot4 <4= paco4 gf bot4.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \4/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn4 n (paco4 gcpn4 bot4) x0 x1 x2 x3) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn4 n (paco4 gcpn4 bot4) <4= gf (rclo cpn4 (S n) (paco4 gcpn4 bot4))).
  { intro X. revert x0 x1 x2 x3 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply gcpn4_mon].
    + intros. right. eapply cpn4_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat4_compat cpn4_compat).
        eapply (compat4_mon cpn4_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo4 (clo: rel->rel) (r: rel): rel :=
| rclo4_base
    e0 e1 e2 e3
    (R: r e0 e1 e2 e3):
    @rclo4 clo r e0 e1 e2 e3
| rclo4_clo'
    r' e0 e1 e2 e3
    (R': r' <4= rclo4 clo r)
    (CLOR': clo r' e0 e1 e2 e3):
    @rclo4 clo r e0 e1 e2 e3
| rclo4_step'
    r' e0 e1 e2 e3
    (R': r' <4= rclo4 clo r)
    (CLOR': @gf r' e0 e1 e2 e3):
    @rclo4 clo r e0 e1 e2 e3
| rclo4_cpn'
    r' e0 e1 e2 e3
    (R': r' <4= rclo4 clo r)
    (CLOR': @cpn4 r' e0 e1 e2 e3):
    @rclo4 clo r e0 e1 e2 e3
.

Structure wcompatible4 (clo: rel -> rel) : Prop :=
  wcompat4_intro {
      wcompat4_mon: monotone4 clo;
      wcompat4_wcompat: forall r,
          clo (gf r) <4= gf (rclo4 clo r);
    }.

Lemma rclo4_mon_gen clo clo' r r' e0 e1 e2 e3
      (IN: @rclo4 clo r e0 e1 e2 e3)
      (LEclo: clo <5= clo')
      (LEr: r <4= r') :
  @rclo4 clo' r' e0 e1 e2 e3.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn4_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo4_mon clo:
  monotone4 (rclo4 clo).
Proof.
  repeat intro. eapply rclo4_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo4_clo clo r:
  clo (rclo4 clo r) <4= rclo4 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo4_step clo r:
  gf (rclo4 clo r) <4= rclo4 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo4_cpn clo r:
  cpn4 (rclo4 clo r) <4= rclo4 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo4_mult clo r:
  rclo4 clo (rclo4 clo r) <4= rclo4 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo4_compose clo r:
  rclo4 (rclo4 clo) r <4= rclo4 clo r.
Proof.
  intros. induction PR.
  - apply rclo4_base, R.
  - apply rclo4_mult.
    eapply rclo4_mon; [apply CLOR'|apply H].
  - apply rclo4_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo4_cpn.
    eapply cpn4_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat4_compat
      clo (WCOM: wcompatible4 clo):
  compatible4 (rclo4 clo).
Proof.
  econstructor; [eapply rclo4_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply R|]. intros.
    apply rclo4_base. apply PR.
  - eapply gf_mon.
    + eapply (wcompat4_wcompat WCOM).
      eapply (wcompat4_mon WCOM); [apply CLOR'|apply H].
    + intros. apply rclo4_mult, PR.
  - eapply gf_mon; [apply CLOR'|].
    intros. apply H in PR. apply rclo4_step, PR.
  - eapply gf_mon; [|intros; apply rclo4_cpn, PR].
    apply (compat4_compat cpn4_compat).
    eapply cpn4_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat4_sound clo (WCOM: wcompatible4 clo):
  clo <5= cpn4.
Proof.
  intros. exists (rclo4 clo).
  - apply wcompat4_compat, WCOM.
  - apply rclo4_clo.
    eapply (wcompat4_mon WCOM); [apply PR|].
    intros. apply rclo4_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn4_base: forall r, r <4= cpn4 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
  - apply PR.
Qed.

Lemma cpn4_from_upaco r:
  upaco4 gcpn4 r <4= cpn4 r.
Proof.
  intros. destruct PR; [| apply cpn4_base, H].
  exists (rclo4 (paco4 gcpn4)).
  - apply wcompat4_compat.
    econstructor; [apply paco4_mon|].
    intros. _punfold PR; [|apply gcpn4_mon].
    eapply gf_mon; [apply PR|].
    intros. apply rclo4_cpn.
    eapply cpn4_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo4_clo.
      eapply paco4_mon; [apply H0|].
      intros. apply rclo4_step.
      eapply gf_mon; [apply PR1|].
      intros. apply rclo4_base, PR2.
    + apply rclo4_step.
      eapply gf_mon; [apply H0|].
      intros. apply rclo4_base, PR1.
  - apply rclo4_clo.
    eapply paco4_mon; [apply H|].
    intros. apply rclo4_base, PR.
Qed.

Lemma cpn4_from_paco r:
  paco4 gcpn4 r <4= cpn4 r.
Proof. intros. apply cpn4_from_upaco. left. apply PR. Qed.

Lemma gcpn4_from_paco r:
  paco4 gcpn4 r <4= gcpn4 r.
Proof.
  intros. _punfold PR; [|apply gcpn4_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn4_cpn.
  eapply cpn4_mon; [apply PR0|].
  apply cpn4_from_upaco.
Qed.

Lemma gcpn4_to_paco r:
  gcpn4 r <4= paco4 gcpn4 r.
Proof.
  intros. pfold. eapply gcpn4_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn4_complete:
  paco4 gf bot4 <4= cpn4 bot4.
Proof.
  intros. apply cpn4_from_paco.
  eapply paco4_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn4_base].
  - intros. apply PR0.
Qed.

Lemma cpn4_init:
  cpn4 bot4 <4= paco4 gf bot4.
Proof.
  intros. apply gcpn4_sound, gcpn4_to_paco, (compat4_compat cpn4_compat).
  eapply cpn4_mon; [apply PR|contradiction].
Qed.

Lemma cpn4_clo
      r clo (LE: clo <5= cpn4):
  clo (cpn4 r) <4= cpn4 r.
Proof.
  intros. apply cpn4_cpn, LE, PR.
Qed.

Lemma cpn4_unfold:
  cpn4 bot4 <4= gcpn4 bot4.
Proof.
  intros. apply cpn4_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn4_complete, PR0.
Qed.

Lemma cpn4_step r:
  gcpn4 r <4= cpn4 r.
Proof.
  intros. eapply cpn4_clo, PR.
  intros. eapply wcompat4_sound, PR0.
  econstructor; [apply gf_mon|].
  intros. eapply gf_mon; [apply PR1|].
  intros. apply rclo4_step.
  eapply gf_mon; [apply PR2|].
  intros. apply rclo4_base, PR3.
Qed.

Lemma gcpn4_clo
      r clo (LE: clo <5= cpn4):
  clo (gcpn4 r) <4= gcpn4 r.
Proof.
  intros. apply LE, (compat4_compat cpn4_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn4_cpn, PR0.
Qed.

Lemma cpn4_final: forall r, upaco4 gf r <4= cpn4 r.
Proof.
  intros. eapply cpn4_from_upaco.
  intros. eapply upaco4_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn4_base, PR1.
Qed.

Lemma gcpn4_final: forall r, paco4 gf r <4= gcpn4 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn4_final].
Qed.

Lemma cpn4_algebra r :
  r <4= gf r -> r <4= cpn4 bot4.
Proof.
  intros. apply cpn4_final. left.
  revert x0 x1 x2 x3 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion4_main.

Lemma cpn4_mon_bot (gf gf': rel -> rel) e0 e1 e2 e3 r
      (IN: @cpn4 gf bot4 e0 e1 e2 e3)
      (MONgf: monotone4 gf)
      (MONgf': monotone4 gf')
      (LE: gf <5= gf'):
  @cpn4 gf' r e0 e1 e2 e3.
Proof.
  apply cpn4_init in IN; [|apply MONgf].
  apply cpn4_final; [apply MONgf'|].
  left. eapply paco4_mon_gen; [apply IN| apply LE| contradiction].
Qed.

End Companion4.

Hint Unfold gcpn4 : paco.

Hint Resolve cpn4_base : paco.
Hint Resolve cpn4_step : paco.
Hint Resolve cpn4_final gcpn4_final : paco.
(* Hint Resolve cpn4_mon : paco.
Hint Resolve gcpn4_mon : paco.
Hint Resolve rclo4_mon : paco. *)

Hint Constructors cpn4 compatible4 wcompatible4.

Hint Constructors rclo4 : rclo.
Hint Resolve rclo4_clo rclo4_step rclo4_cpn : rclo.

