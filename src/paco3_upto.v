Require Export Program.Basics. Open Scope program_scope.
Require Import paco3.
Set Implicit Arguments.

Section Companion3.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.

Local Notation rel := (rel3 T0 T1 T2).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone3 gf.

(** 
  Compatibility, Companion & Guarded Companion
*)

Structure compatible3 (clo: rel -> rel) : Prop :=
  compat3_intro {
      compat3_mon: monotone3 clo;
      compat3_compat : forall r,
          clo (gf r) <3= gf (clo r);
    }.

Inductive cpn3 (r: rel) e0 e1 e2 : Prop :=
| cpn3_intro
    clo
    (COM: compatible3 clo)
    (CLO: clo r e0 e1 e2)
.

Definition gcpn3 := compose gf cpn3.

Lemma cpn3_mon: monotone3 cpn3.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat3_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn3_compat: compatible3 cpn3.
Proof.
  econstructor; [apply cpn3_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat3_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn3_greatest: forall clo (COM: compatible3 clo), clo <4= cpn3.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn3_comp: forall r,
    cpn3 (cpn3 r) <3= cpn3 r.
Proof.
  intros. exists (compose cpn3 cpn3); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn3_mon; [apply IN|].
    intros. eapply cpn3_mon; [apply PR0|apply LE].
  - intros. eapply (compat3_compat cpn3_compat).
    eapply cpn3_mon; [apply PR0|].
    intros. eapply (compat3_compat cpn3_compat), PR1. 
Qed.

Lemma gcpn3_mon: monotone3 gcpn3.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn3_mon; [apply PR|apply LE].
Qed.

Lemma gcpn3_sound:
  paco3 gcpn3 bot3 <3= paco3 gf bot3.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \3/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn3 n (paco3 gcpn3 bot3) x0 x1 x2) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn3 n (paco3 gcpn3 bot3) <3= gf (rclo cpn3 (S n) (paco3 gcpn3 bot3))).
  { intro X. revert x0 x1 x2 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply gcpn3_mon].
    + intros. right. eapply cpn3_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat3_compat cpn3_compat).
        eapply (compat3_mon cpn3_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo3 (clo: rel->rel) (r: rel): rel :=
| rclo3_base
    e0 e1 e2
    (R: r e0 e1 e2):
    @rclo3 clo r e0 e1 e2
| rclo3_clo'
    r' e0 e1 e2
    (R': r' <3= rclo3 clo r)
    (CLOR': clo r' e0 e1 e2):
    @rclo3 clo r e0 e1 e2
| rclo3_step'
    r' e0 e1 e2
    (R': r' <3= rclo3 clo r)
    (CLOR': @gf r' e0 e1 e2):
    @rclo3 clo r e0 e1 e2
| rclo3_cpn'
    r' e0 e1 e2
    (R': r' <3= rclo3 clo r)
    (CLOR': @cpn3 r' e0 e1 e2):
    @rclo3 clo r e0 e1 e2
.

Structure wcompatible3 (clo: rel -> rel) : Prop :=
  wcompat3_intro {
      wcompat3_mon: monotone3 clo;
      wcompat3_wcompat: forall r,
          clo (gf r) <3= gf (rclo3 clo r);
    }.

Lemma rclo3_mon_gen clo clo' r r' e0 e1 e2
      (IN: @rclo3 clo r e0 e1 e2)
      (LEclo: clo <4= clo')
      (LEr: r <3= r') :
  @rclo3 clo' r' e0 e1 e2.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn3_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo3_mon clo:
  monotone3 (rclo3 clo).
Proof.
  repeat intro. eapply rclo3_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo3_clo clo r:
  clo (rclo3 clo r) <3= rclo3 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo3_step clo r:
  gf (rclo3 clo r) <3= rclo3 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo3_cpn clo r:
  cpn3 (rclo3 clo r) <3= rclo3 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo3_mult clo r:
  rclo3 clo (rclo3 clo r) <3= rclo3 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo3_compose clo r:
  rclo3 (rclo3 clo) r <3= rclo3 clo r.
Proof.
  intros. induction PR.
  - apply rclo3_base, R.
  - apply rclo3_mult.
    eapply rclo3_mon; [apply CLOR'|apply H].
  - apply rclo3_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo3_cpn.
    eapply cpn3_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat3_compat
      clo (WCOM: wcompatible3 clo):
  compatible3 (rclo3 clo).
Proof.
  econstructor; [eapply rclo3_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply R|]. intros.
    apply rclo3_base. apply PR.
  - eapply gf_mon.
    + eapply (wcompat3_wcompat WCOM).
      eapply (wcompat3_mon WCOM); [apply CLOR'|apply H].
    + intros. apply rclo3_mult, PR.
  - eapply gf_mon; [apply CLOR'|].
    intros. apply H in PR. apply rclo3_step, PR.
  - eapply gf_mon; [|intros; apply rclo3_cpn, PR].
    apply (compat3_compat cpn3_compat).
    eapply cpn3_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat3_sound clo (WCOM: wcompatible3 clo):
  clo <4= cpn3.
Proof.
  intros. exists (rclo3 clo).
  - apply wcompat3_compat, WCOM.
  - apply rclo3_clo.
    eapply (wcompat3_mon WCOM); [apply PR|].
    intros. apply rclo3_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn3_base: forall r, r <3= cpn3 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
  - apply PR.
Qed.

Lemma cpn3_from_upaco r:
  upaco3 gcpn3 r <3= cpn3 r.
Proof.
  intros. destruct PR; [| apply cpn3_base, H].
  exists (rclo3 (paco3 gcpn3)).
  - apply wcompat3_compat.
    econstructor; [apply paco3_mon|].
    intros. _punfold PR; [|apply gcpn3_mon].
    eapply gf_mon; [apply PR|].
    intros. apply rclo3_cpn.
    eapply cpn3_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo3_clo.
      eapply paco3_mon; [apply H0|].
      intros. apply rclo3_step.
      eapply gf_mon; [apply PR1|].
      intros. apply rclo3_base, PR2.
    + apply rclo3_step.
      eapply gf_mon; [apply H0|].
      intros. apply rclo3_base, PR1.
  - apply rclo3_clo.
    eapply paco3_mon; [apply H|].
    intros. apply rclo3_base, PR.
Qed.

Lemma cpn3_from_paco r:
  paco3 gcpn3 r <3= cpn3 r.
Proof. intros. apply cpn3_from_upaco. left. apply PR. Qed.

Lemma gcpn3_from_paco r:
  paco3 gcpn3 r <3= gcpn3 r.
Proof.
  intros. _punfold PR; [|apply gcpn3_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn3_comp.
  eapply cpn3_mon; [apply PR0|].
  apply cpn3_from_upaco.
Qed.

Lemma gcpn3_to_paco r:
  gcpn3 r <3= paco3 gcpn3 r.
Proof.
  intros. pfold. eapply gcpn3_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn3_init:
  cpn3 bot3 <3= paco3 gf bot3.
Proof.
  intros. apply gcpn3_sound, gcpn3_to_paco, (compat3_compat cpn3_compat).
  eapply cpn3_mon; [apply PR|contradiction].
Qed.

Lemma cpn3_clo
      r clo (LE: clo <4= cpn3):
  clo (cpn3 r) <3= cpn3 r.
Proof.
  intros. apply cpn3_comp, LE, PR.
Qed.

Lemma gcpn3_clo
      r clo (LE: clo <4= cpn3):
  clo (gcpn3 r) <3= gcpn3 r.
Proof.
  intros. apply LE, (compat3_compat cpn3_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn3_comp, PR0.
Qed.

Lemma cpn3_step r:
  gcpn3 r <3= cpn3 r.
Proof.
  intros. eapply cpn3_clo, PR.
  intros. eapply wcompat3_sound, PR0.
  econstructor; [apply gf_mon|].
  intros. eapply gf_mon; [apply PR1|].
  intros. apply rclo3_step.
  eapply gf_mon; [apply PR2|].
  intros. apply rclo3_base, PR3.
Qed.

Lemma cpn3_final: forall r, upaco3 gf r <3= cpn3 r.
Proof.
  intros. eapply cpn3_from_upaco.
  intros. eapply upaco3_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn3_base, PR1.
Qed.

Lemma gcpn3_final: forall r, paco3 gf r <3= gcpn3 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn3_final].
Qed.

Lemma cpn3_complete:
  paco3 gf bot3 <3= cpn3 bot3.
Proof.
  intros. apply cpn3_from_paco.
  eapply paco3_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn3_base].
  - intros. apply PR0.
Qed.

End Companion3.

Hint Resolve cpn3_base : paco.
Hint Resolve cpn3_mon : paco.
Hint Resolve gcpn3_mon : paco.
Hint Resolve rclo3_mon : paco.
Hint Resolve cpn3_final gcpn3_final : paco.

Hint Constructors cpn3 compatible3 wcompatible3.

Hint Constructors rclo3 : rclo.
Hint Resolve rclo3_clo rclo3_step rclo3_cpn : rclo.

