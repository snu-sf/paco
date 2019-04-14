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

Inductive cpn4 (r: rel) x0 x1 x2 x3 : Prop :=
| cpn4_intro
    clo
    (COM: compatible4 clo)
    (CLO: clo r x0 x1 x2 x3)
.

Definition fcpn4 := compose gf cpn4.

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

Lemma monotone4_compose (clo1 clo2: rel -> rel)
      (MON1: monotone4 clo1)
      (MON2: monotone4 clo2):
  monotone4 (compose clo1 clo2).
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma fcpn4_mon: monotone4 fcpn4.
Proof.
  apply monotone4_compose. apply gf_mon. apply cpn4_mon.
Qed.

Lemma fcpn4_sound:
  paco4 fcpn4 bot4 <4= paco4 gf bot4.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \4/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn4 n (paco4 fcpn4 bot4) x0 x1 x2 x3) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn4 n (paco4 fcpn4 bot4) <4= gf (rclo cpn4 (S n) (paco4 fcpn4 bot4))).
  { intro X. revert x0 x1 x2 x3 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply fcpn4_mon].
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
    x0 x1 x2 x3
    (IN: r x0 x1 x2 x3):
    @rclo4 clo r x0 x1 x2 x3
| rclo4_clo'
    r' x0 x1 x2 x3
    (LE: r' <4= rclo4 clo r)
    (IN: clo r' x0 x1 x2 x3):
    @rclo4 clo r x0 x1 x2 x3
.           

Structure wcompatible4 (clo: rel -> rel) : Prop :=
  wcompat4_intro {
      wcompat4_mon: monotone4 clo;
      wcompat4_wcompat : forall r,
          clo (gf r) <4= gf (rclo4 (clo \5/ cpn4) r);
    }.

Lemma rclo4_mon_gen clo clo' r r' x0 x1 x2 x3
      (IN: @rclo4 clo r x0 x1 x2 x3)
      (LEclo: clo <5= clo')
      (LEr: r <4= r') :
  @rclo4 clo' r' x0 x1 x2 x3.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
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

Lemma rclo4_rclo clo r:
  rclo4 clo (rclo4 clo r) <4= rclo4 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo4_compose clo r:
  rclo4 (rclo4 clo) r <4= rclo4 clo r.
Proof.
  intros. induction PR.
  - apply rclo4_base, IN.
  - apply rclo4_rclo.
    eapply rclo4_mon; [apply IN|apply H].
Qed.

Lemma rclo4_compat clo
      (COM: compatible4 clo):
  compatible4 (rclo4 clo).
Proof.
  econstructor.
  - apply rclo4_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo4_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo4_clo. apply PR.
Qed.

Lemma wcompat4_compat  clo
      (WCOM: wcompatible4 clo):
  compatible4 (rclo4 (clo \5/ cpn4)).
Proof.
  econstructor; [eapply rclo4_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply IN|]. intros.
    apply rclo4_base. apply PR.
  - destruct IN as [IN|IN].
    + eapply gf_mon.
      * eapply WCOM. eapply WCOM; [apply IN|apply H].
      * intros. apply rclo4_rclo, PR.
    + eapply gf_mon; [|intros; apply rclo4_clo; right; apply PR].
      apply (compat4_compat cpn4_compat).
      eapply cpn4_mon; [apply IN|apply H].
Qed.

Lemma wcompat4_sound clo
      (WCOM: wcompatible4 clo):
  clo <5= cpn4.
Proof.
  intros. exists (rclo4 (clo \5/ cpn4)).
  - apply wcompat4_compat, WCOM.
  - apply rclo4_clo.
    left. eapply WCOM. apply PR.
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

Lemma cpn4_step r:
  fcpn4 r <4= cpn4 r.
Proof.
  intros. eapply cpn4_cpn. exists gf.
  - econstructor. apply gf_mon. intros; apply PR0.
  - apply PR.
Qed.

Lemma cpn4_from_upaco r:
  upaco4 fcpn4 r <4= cpn4 r.
Proof.
  eapply wcompat4_sound.
  econstructor; [apply upaco4_mon|].
  intros. destruct PR as [PR|PR].
  - _punfold PR; [|apply fcpn4_mon]. 
    eapply gf_mon; [apply PR|].
    intros. apply rclo4_clo; right.
    eapply cpn4_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo4_clo; left.
      left. eapply paco4_mon; [apply H|].
      intros. apply rclo4_clo; right. apply cpn4_step.
      eapply gf_mon; [apply PR1|].
      intros. apply cpn4_base, rclo4_base, PR2.
    + apply rclo4_clo; right. apply cpn4_step.
      eapply gf_mon; [apply H|].
      intros. apply cpn4_base, rclo4_base, PR1.
  - eapply gf_mon. apply PR.
    intros. apply rclo4_base, PR0. 
Qed.

Lemma cpn4_from_paco r:
  paco4 fcpn4 r <4= cpn4 r.
Proof. intros. apply cpn4_from_upaco. left. apply PR. Qed.

Lemma fcpn4_from_paco r:
  paco4 fcpn4 r <4= fcpn4 r.
Proof.
  intros. _punfold PR; [|apply fcpn4_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn4_cpn.
  eapply cpn4_mon; [apply PR0|].
  apply cpn4_from_upaco.
Qed.

Lemma fcpn4_to_paco r:
  fcpn4 r <4= paco4 fcpn4 r.
Proof.
  intros. pfold. eapply fcpn4_mon; [apply PR|].
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
  intros. apply fcpn4_sound, fcpn4_to_paco, (compat4_compat cpn4_compat).
  eapply cpn4_mon; [apply PR|contradiction].
Qed.

Lemma cpn4_clo
      r clo (LE: clo <5= cpn4):
  clo (cpn4 r) <4= cpn4 r.
Proof.
  intros. apply cpn4_cpn, LE, PR.
Qed.

Lemma cpn4_unfold:
  cpn4 bot4 <4= fcpn4 bot4.
Proof.
  intros. apply cpn4_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn4_complete, PR0.
Qed.

Lemma fcpn4_clo
      r clo (LE: clo <5= cpn4):
  clo (fcpn4 r) <4= fcpn4 r.
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

Lemma fcpn4_final: forall r, paco4 gf r <4= fcpn4 r.
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

Lemma cpn4_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 r
      (IN: @cpn4 gf bot4 x0 x1 x2 x3)
      (MONgf: monotone4 gf)
      (MONgf': monotone4 gf')
      (LE: gf <5= gf'):
  @cpn4 gf' r x0 x1 x2 x3.
Proof.
  apply cpn4_init in IN; [|apply MONgf].
  apply cpn4_final; [apply MONgf'|].
  left. eapply paco4_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn4_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 r
      (IN: @fcpn4 gf bot4 x0 x1 x2 x3)
      (MONgf: monotone4 gf)
      (MONgf': monotone4 gf')
      (LE: gf <5= gf'):
  @fcpn4 gf' r x0 x1 x2 x3.
Proof.
  apply LE. eapply MONgf. apply IN.
  intros. eapply cpn4_mon_bot; eassumption.
Qed.

End Companion4.

Hint Unfold fcpn4 : paco.

Hint Resolve cpn4_base : paco.
Hint Resolve cpn4_step : paco.
Hint Constructors rclo4 : paco.
Hint Resolve rclo4_clo : paco.
