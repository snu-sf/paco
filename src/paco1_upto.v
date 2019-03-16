Require Export Program.Basics. Open Scope program_scope.
Require Import paco1.
Set Implicit Arguments.

Section Companion1.

Variable T0 : Type.

Local Notation rel := (rel1 T0).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone1 gf.

(** 
  Compatibility, Companion & Guarded Companion
*)

Structure compatible1 (clo: rel -> rel) : Prop :=
  compat1_intro {
      compat1_mon: monotone1 clo;
      compat1_compat : forall r,
          clo (gf r) <1= gf (clo r);
    }.

Inductive cpn1 (r: rel) e0 : Prop :=
| cpn1_intro
    clo
    (COM: compatible1 clo)
    (CLO: clo r e0)
.

Definition gcpn1 := compose gf cpn1.

Lemma cpn1_mon: monotone1 cpn1.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat1_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn1_compat: compatible1 cpn1.
Proof.
  econstructor; [apply cpn1_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat1_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn1_greatest: forall clo (COM: compatible1 clo), clo <2= cpn1.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn1_comp: forall r,
    cpn1 (cpn1 r) <1= cpn1 r.
Proof.
  intros. exists (compose cpn1 cpn1); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn1_mon; [apply IN|].
    intros. eapply cpn1_mon; [apply PR0|apply LE].
  - intros. eapply (compat1_compat cpn1_compat).
    eapply cpn1_mon; [apply PR0|].
    intros. eapply (compat1_compat cpn1_compat), PR1. 
Qed.

Lemma gcpn1_mon: monotone1 gcpn1.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn1_mon; [apply PR|apply LE].
Qed.

Lemma gcpn1_sound:
  paco1 gcpn1 bot1 <1= paco1 gf bot1.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \1/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn1 n (paco1 gcpn1 bot1) x0) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn1 n (paco1 gcpn1 bot1) <1= gf (rclo cpn1 (S n) (paco1 gcpn1 bot1))).
  { intro X. revert x0 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply gcpn1_mon].
    + intros. right. eapply cpn1_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat1_compat cpn1_compat).
        eapply (compat1_mon cpn1_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo1 (clo: rel->rel) (r: rel): rel :=
| rclo1_base
    e0
    (R: r e0):
    @rclo1 clo r e0
| rclo1_clo'
    r' e0
    (R': r' <1= rclo1 clo r)
    (CLOR': clo r' e0):
    @rclo1 clo r e0
| rclo1_step'
    r' e0
    (R': r' <1= rclo1 clo r)
    (CLOR': @gf r' e0):
    @rclo1 clo r e0
| rclo1_cpn'
    r' e0
    (R': r' <1= rclo1 clo r)
    (CLOR': @cpn1 r' e0):
    @rclo1 clo r e0
.

Structure wcompatible1 (clo: rel -> rel) : Prop :=
  wcompat1_intro {
      wcompat1_mon: monotone1 clo;
      wcompat1_wcompat: forall r,
          clo (gf r) <1= gf (rclo1 clo r);
    }.

Lemma rclo1_mon_gen clo clo' r r' e0
      (IN: @rclo1 clo r e0)
      (LEclo: clo <2= clo')
      (LEr: r <1= r') :
  @rclo1 clo' r' e0.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn1_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo1_mon clo:
  monotone1 (rclo1 clo).
Proof.
  repeat intro. eapply rclo1_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo1_clo clo r:
  clo (rclo1 clo r) <1= rclo1 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo1_step clo r:
  gf (rclo1 clo r) <1= rclo1 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo1_cpn clo r:
  cpn1 (rclo1 clo r) <1= rclo1 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo1_mult clo r:
  rclo1 clo (rclo1 clo r) <1= rclo1 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo1_compose clo r:
  rclo1 (rclo1 clo) r <1= rclo1 clo r.
Proof.
  intros. induction PR.
  - apply rclo1_base, R.
  - apply rclo1_mult.
    eapply rclo1_mon; [apply CLOR'|apply H].
  - apply rclo1_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo1_cpn.
    eapply cpn1_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat1_compat
      clo (WCOM: wcompatible1 clo):
  compatible1 (rclo1 clo).
Proof.
  econstructor; [eapply rclo1_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply R|]. intros.
    apply rclo1_base. apply PR.
  - eapply gf_mon.
    + eapply (wcompat1_wcompat WCOM).
      eapply (wcompat1_mon WCOM); [apply CLOR'|apply H].
    + intros. apply rclo1_mult, PR.
  - eapply gf_mon; [apply CLOR'|].
    intros. apply H in PR. apply rclo1_step, PR.
  - eapply gf_mon; [|intros; apply rclo1_cpn, PR].
    apply (compat1_compat cpn1_compat).
    eapply cpn1_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat1_sound clo (WCOM: wcompatible1 clo):
  clo <2= cpn1.
Proof.
  intros. exists (rclo1 clo).
  - apply wcompat1_compat, WCOM.
  - apply rclo1_clo.
    eapply (wcompat1_mon WCOM); [apply PR|].
    intros. apply rclo1_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn1_base: forall r, r <1= cpn1 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
  - apply PR.
Qed.

Lemma cpn1_from_upaco r:
  upaco1 gcpn1 r <1= cpn1 r.
Proof.
  intros. destruct PR; [| apply cpn1_base, H].
  exists (rclo1 (paco1 gcpn1)).
  - apply wcompat1_compat.
    econstructor; [apply paco1_mon|].
    intros. _punfold PR; [|apply gcpn1_mon].
    eapply gf_mon; [apply PR|].
    intros. apply rclo1_cpn.
    eapply cpn1_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo1_clo.
      eapply paco1_mon; [apply H0|].
      intros. apply rclo1_step.
      eapply gf_mon; [apply PR1|].
      intros. apply rclo1_base, PR2.
    + apply rclo1_step.
      eapply gf_mon; [apply H0|].
      intros. apply rclo1_base, PR1.
  - apply rclo1_clo.
    eapply paco1_mon; [apply H|].
    intros. apply rclo1_base, PR.
Qed.

Lemma cpn1_from_paco r:
  paco1 gcpn1 r <1= cpn1 r.
Proof. intros. apply cpn1_from_upaco. left. apply PR. Qed.

Lemma gcpn1_from_paco r:
  paco1 gcpn1 r <1= gcpn1 r.
Proof.
  intros. _punfold PR; [|apply gcpn1_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn1_comp.
  eapply cpn1_mon; [apply PR0|].
  apply cpn1_from_upaco.
Qed.

Lemma gcpn1_to_paco r:
  gcpn1 r <1= paco1 gcpn1 r.
Proof.
  intros. pfold. eapply gcpn1_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn1_init:
  cpn1 bot1 <1= paco1 gf bot1.
Proof.
  intros. apply gcpn1_sound, gcpn1_to_paco, (compat1_compat cpn1_compat).
  eapply cpn1_mon; [apply PR|contradiction].
Qed.

Lemma cpn1_clo
      r clo (LE: clo <2= cpn1):
  clo (cpn1 r) <1= cpn1 r.
Proof.
  intros. apply cpn1_comp, LE, PR.
Qed.

Lemma gcpn1_clo
      r clo (LE: clo <2= cpn1):
  clo (gcpn1 r) <1= gcpn1 r.
Proof.
  intros. apply LE, (compat1_compat cpn1_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn1_comp, PR0.
Qed.

Lemma cpn1_step r:
  gcpn1 r <1= cpn1 r.
Proof.
  intros. eapply cpn1_clo, PR.
  intros. eapply wcompat1_sound, PR0.
  econstructor; [apply gf_mon|].
  intros. eapply gf_mon; [apply PR1|].
  intros. apply rclo1_step.
  eapply gf_mon; [apply PR2|].
  intros. apply rclo1_base, PR3.
Qed.

Lemma cpn1_final: forall r, upaco1 gf r <1= cpn1 r.
Proof.
  intros. eapply cpn1_from_upaco.
  intros. eapply upaco1_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn1_base, PR1.
Qed.

Lemma gcpn1_final: forall r, paco1 gf r <1= gcpn1 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn1_final].
Qed.

Lemma cpn1_complete:
  paco1 gf bot1 <1= cpn1 bot1.
Proof.
  intros. apply cpn1_from_paco.
  eapply paco1_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn1_base].
  - intros. apply PR0.
Qed.

End Companion1.

Hint Resolve cpn1_base : paco.
Hint Resolve cpn1_mon : paco.
Hint Resolve gcpn1_mon : paco.
Hint Resolve rclo1_mon : paco.
Hint Resolve cpn1_final gcpn1_final : paco.

Hint Constructors cpn1 compatible1 wcompatible1.

Hint Constructors rclo1 : rclo.
Hint Resolve rclo1_clo rclo1_step rclo1_cpn : rclo.

