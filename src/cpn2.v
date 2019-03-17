Require Export Program.Basics. Open Scope program_scope.
Require Import paco2 pacotac.
Set Implicit Arguments.

Section Companion2.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.

Local Notation rel := (rel2 T0 T1).

Section Companion2_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone2 gf.

(** 
  Compatibility, Companion & Guarded Companion
*)

Structure compatible2 (clo: rel -> rel) : Prop :=
  compat2_intro {
      compat2_mon: monotone2 clo;
      compat2_compat : forall r,
          clo (gf r) <2= gf (clo r);
    }.

Inductive cpn2 (r: rel) e0 e1 : Prop :=
| cpn2_intro
    clo
    (COM: compatible2 clo)
    (CLO: clo r e0 e1)
.

Definition gcpn2 := compose gf cpn2.

Lemma cpn2_mon: monotone2 cpn2.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat2_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn2_compat: compatible2 cpn2.
Proof.
  econstructor; [apply cpn2_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat2_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn2_greatest: forall clo (COM: compatible2 clo), clo <3= cpn2.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn2_comp: forall r,
    cpn2 (cpn2 r) <2= cpn2 r.
Proof.
  intros. exists (compose cpn2 cpn2); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn2_mon; [apply IN|].
    intros. eapply cpn2_mon; [apply PR0|apply LE].
  - intros. eapply (compat2_compat cpn2_compat).
    eapply cpn2_mon; [apply PR0|].
    intros. eapply (compat2_compat cpn2_compat), PR1. 
Qed.

Lemma gcpn2_mon: monotone2 gcpn2.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn2_mon; [apply PR|apply LE].
Qed.

Lemma gcpn2_sound:
  paco2 gcpn2 bot2 <2= paco2 gf bot2.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \2/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn2 n (paco2 gcpn2 bot2) x0 x1) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn2 n (paco2 gcpn2 bot2) <2= gf (rclo cpn2 (S n) (paco2 gcpn2 bot2))).
  { intro X. revert x0 x1 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply gcpn2_mon].
    + intros. right. eapply cpn2_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat2_compat cpn2_compat).
        eapply (compat2_mon cpn2_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo2 (clo: rel->rel) (r: rel): rel :=
| rclo2_base
    e0 e1
    (R: r e0 e1):
    @rclo2 clo r e0 e1
| rclo2_clo'
    r' e0 e1
    (R': r' <2= rclo2 clo r)
    (CLOR': clo r' e0 e1):
    @rclo2 clo r e0 e1
| rclo2_step'
    r' e0 e1
    (R': r' <2= rclo2 clo r)
    (CLOR': @gf r' e0 e1):
    @rclo2 clo r e0 e1
| rclo2_cpn'
    r' e0 e1
    (R': r' <2= rclo2 clo r)
    (CLOR': @cpn2 r' e0 e1):
    @rclo2 clo r e0 e1
.

Structure wcompatible2 (clo: rel -> rel) : Prop :=
  wcompat2_intro {
      wcompat2_mon: monotone2 clo;
      wcompat2_wcompat: forall r,
          clo (gf r) <2= gf (rclo2 clo r);
    }.

Lemma rclo2_mon_gen clo clo' r r' e0 e1
      (IN: @rclo2 clo r e0 e1)
      (LEclo: clo <3= clo')
      (LEr: r <2= r') :
  @rclo2 clo' r' e0 e1.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn2_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo2_mon clo:
  monotone2 (rclo2 clo).
Proof.
  repeat intro. eapply rclo2_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo2_clo clo r:
  clo (rclo2 clo r) <2= rclo2 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo2_step clo r:
  gf (rclo2 clo r) <2= rclo2 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo2_cpn clo r:
  cpn2 (rclo2 clo r) <2= rclo2 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo2_mult clo r:
  rclo2 clo (rclo2 clo r) <2= rclo2 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo2_compose clo r:
  rclo2 (rclo2 clo) r <2= rclo2 clo r.
Proof.
  intros. induction PR.
  - apply rclo2_base, R.
  - apply rclo2_mult.
    eapply rclo2_mon; [apply CLOR'|apply H].
  - apply rclo2_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo2_cpn.
    eapply cpn2_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat2_compat
      clo (WCOM: wcompatible2 clo):
  compatible2 (rclo2 clo).
Proof.
  econstructor; [eapply rclo2_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply R|]. intros.
    apply rclo2_base. apply PR.
  - eapply gf_mon.
    + eapply (wcompat2_wcompat WCOM).
      eapply (wcompat2_mon WCOM); [apply CLOR'|apply H].
    + intros. apply rclo2_mult, PR.
  - eapply gf_mon; [apply CLOR'|].
    intros. apply H in PR. apply rclo2_step, PR.
  - eapply gf_mon; [|intros; apply rclo2_cpn, PR].
    apply (compat2_compat cpn2_compat).
    eapply cpn2_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat2_sound clo (WCOM: wcompatible2 clo):
  clo <3= cpn2.
Proof.
  intros. exists (rclo2 clo).
  - apply wcompat2_compat, WCOM.
  - apply rclo2_clo.
    eapply (wcompat2_mon WCOM); [apply PR|].
    intros. apply rclo2_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn2_base: forall r, r <2= cpn2 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
  - apply PR.
Qed.

Lemma cpn2_from_upaco r:
  upaco2 gcpn2 r <2= cpn2 r.
Proof.
  intros. destruct PR; [| apply cpn2_base, H].
  exists (rclo2 (paco2 gcpn2)).
  - apply wcompat2_compat.
    econstructor; [apply paco2_mon|].
    intros. _punfold PR; [|apply gcpn2_mon].
    eapply gf_mon; [apply PR|].
    intros. apply rclo2_cpn.
    eapply cpn2_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo2_clo.
      eapply paco2_mon; [apply H0|].
      intros. apply rclo2_step.
      eapply gf_mon; [apply PR1|].
      intros. apply rclo2_base, PR2.
    + apply rclo2_step.
      eapply gf_mon; [apply H0|].
      intros. apply rclo2_base, PR1.
  - apply rclo2_clo.
    eapply paco2_mon; [apply H|].
    intros. apply rclo2_base, PR.
Qed.

Lemma cpn2_from_paco r:
  paco2 gcpn2 r <2= cpn2 r.
Proof. intros. apply cpn2_from_upaco. left. apply PR. Qed.

Lemma gcpn2_from_paco r:
  paco2 gcpn2 r <2= gcpn2 r.
Proof.
  intros. _punfold PR; [|apply gcpn2_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn2_comp.
  eapply cpn2_mon; [apply PR0|].
  apply cpn2_from_upaco.
Qed.

Lemma gcpn2_to_paco r:
  gcpn2 r <2= paco2 gcpn2 r.
Proof.
  intros. pfold. eapply gcpn2_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn2_complete:
  paco2 gf bot2 <2= cpn2 bot2.
Proof.
  intros. apply cpn2_from_paco.
  eapply paco2_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn2_base].
  - intros. apply PR0.
Qed.

Lemma cpn2_init:
  cpn2 bot2 <2= paco2 gf bot2.
Proof.
  intros. apply gcpn2_sound, gcpn2_to_paco, (compat2_compat cpn2_compat).
  eapply cpn2_mon; [apply PR|contradiction].
Qed.

Lemma cpn2_clo
      r clo (LE: clo <3= cpn2):
  clo (cpn2 r) <2= cpn2 r.
Proof.
  intros. apply cpn2_comp, LE, PR.
Qed.

Lemma cpn2_unfold:
  cpn2 bot2 <2= gcpn2 bot2.
Proof.
  intros. apply cpn2_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn2_complete, PR0.
Qed.

Lemma cpn2_step r:
  gcpn2 r <2= cpn2 r.
Proof.
  intros. eapply cpn2_clo, PR.
  intros. eapply wcompat2_sound, PR0.
  econstructor; [apply gf_mon|].
  intros. eapply gf_mon; [apply PR1|].
  intros. apply rclo2_step.
  eapply gf_mon; [apply PR2|].
  intros. apply rclo2_base, PR3.
Qed.

Lemma gcpn2_clo
      r clo (LE: clo <3= cpn2):
  clo (gcpn2 r) <2= gcpn2 r.
Proof.
  intros. apply LE, (compat2_compat cpn2_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn2_comp, PR0.
Qed.

Lemma cpn2_final: forall r, upaco2 gf r <2= cpn2 r.
Proof.
  intros. eapply cpn2_from_upaco.
  intros. eapply upaco2_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn2_base, PR1.
Qed.

Lemma gcpn2_final: forall r, paco2 gf r <2= gcpn2 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn2_final].
Qed.

End Companion2_main.

Lemma cpn2_mon_bot (gf gf': rel -> rel) e0 e1 r
      (IN: @cpn2 gf bot2 e0 e1)
      (MONgf: monotone2 gf)
      (MONgf': monotone2 gf')
      (LE: gf <3= gf'):
  @cpn2 gf' r e0 e1.
Proof.
  apply cpn2_init in IN; [|apply MONgf].
  apply cpn2_final; [apply MONgf'|].
  left. eapply paco2_mon_gen; [apply IN| apply LE| contradiction].
Qed.

End Companion2.

Hint Unfold gcpn2 : paco.

Hint Resolve cpn2_base : paco.
Hint Resolve cpn2_step : paco.
Hint Resolve cpn2_final gcpn2_final : paco.
(* Hint Resolve cpn2_mon : paco.
Hint Resolve gcpn2_mon : paco.
Hint Resolve rclo2_mon : paco. *)

Hint Constructors cpn2 compatible2 wcompatible2.

Hint Constructors rclo2 : rclo.
Hint Resolve rclo2_clo rclo2_step rclo2_cpn : rclo.

