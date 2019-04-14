Require Export Program.Basics. Open Scope program_scope.
Require Import paco3 pacotac.
Set Implicit Arguments.

Section Companion3.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.

Local Notation rel := (rel3 T0 T1 T2).

Section Companion3_main.

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

Inductive cpn3 (r: rel) x0 x1 x2 : Prop :=
| cpn3_intro
    clo
    (COM: compatible3 clo)
    (CLO: clo r x0 x1 x2)
.

Definition fcpn3 := compose gf cpn3.

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

Lemma cpn3_cpn: forall r,
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

Lemma monotone3_compose (clo1 clo2: rel -> rel)
      (MON1: monotone3 clo1)
      (MON2: monotone3 clo2):
  monotone3 (compose clo1 clo2).
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma fcpn3_mon: monotone3 fcpn3.
Proof.
  apply monotone3_compose. apply gf_mon. apply cpn3_mon.
Qed.

Lemma fcpn3_sound:
  paco3 fcpn3 bot3 <3= paco3 gf bot3.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \3/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn3 n (paco3 fcpn3 bot3) x0 x1 x2) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn3 n (paco3 fcpn3 bot3) <3= gf (rclo cpn3 (S n) (paco3 fcpn3 bot3))).
  { intro X. revert x0 x1 x2 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply fcpn3_mon].
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
    x0 x1 x2
    (IN: r x0 x1 x2):
    @rclo3 clo r x0 x1 x2
| rclo3_clo'
    r' x0 x1 x2
    (LE: r' <3= rclo3 clo r)
    (IN: clo r' x0 x1 x2):
    @rclo3 clo r x0 x1 x2
.           

Structure wcompatible3 (clo: rel -> rel) : Prop :=
  wcompat3_intro {
      wcompat3_mon: monotone3 clo;
      wcompat3_wcompat : forall r,
          clo (gf r) <3= gf (rclo3 (clo \4/ cpn3) r);
    }.

Lemma rclo3_mon_gen clo clo' r r' x0 x1 x2
      (IN: @rclo3 clo r x0 x1 x2)
      (LEclo: clo <4= clo')
      (LEr: r <3= r') :
  @rclo3 clo' r' x0 x1 x2.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
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

Lemma rclo3_rclo clo r:
  rclo3 clo (rclo3 clo r) <3= rclo3 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo3_compose clo r:
  rclo3 (rclo3 clo) r <3= rclo3 clo r.
Proof.
  intros. induction PR.
  - apply rclo3_base, IN.
  - apply rclo3_rclo.
    eapply rclo3_mon; [apply IN|apply H].
Qed.

Lemma rclo3_compat clo
      (COM: compatible3 clo):
  compatible3 (rclo3 clo).
Proof.
  econstructor.
  - apply rclo3_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo3_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo3_clo. apply PR.
Qed.

Lemma wcompat3_compat  clo
      (WCOM: wcompatible3 clo):
  compatible3 (rclo3 (clo \4/ cpn3)).
Proof.
  econstructor; [eapply rclo3_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply IN|]. intros.
    apply rclo3_base. apply PR.
  - destruct IN as [IN|IN].
    + eapply gf_mon.
      * eapply WCOM. eapply WCOM; [apply IN|apply H].
      * intros. apply rclo3_rclo, PR.
    + eapply gf_mon; [|intros; apply rclo3_clo; right; apply PR].
      apply (compat3_compat cpn3_compat).
      eapply cpn3_mon; [apply IN|apply H].
Qed.

Lemma wcompat3_sound clo
      (WCOM: wcompatible3 clo):
  clo <4= cpn3.
Proof.
  intros. exists (rclo3 (clo \4/ cpn3)).
  - apply wcompat3_compat, WCOM.
  - apply rclo3_clo.
    left. eapply WCOM. apply PR.
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

Lemma cpn3_step r:
  fcpn3 r <3= cpn3 r.
Proof.
  intros. eapply cpn3_cpn. exists gf.
  - econstructor. apply gf_mon. intros; apply PR0.
  - apply PR.
Qed.

Lemma cpn3_from_upaco r:
  upaco3 fcpn3 r <3= cpn3 r.
Proof.
  eapply wcompat3_sound.
  econstructor; [apply upaco3_mon|].
  intros. destruct PR as [PR|PR].
  - _punfold PR; [|apply fcpn3_mon]. 
    eapply gf_mon; [apply PR|].
    intros. apply rclo3_clo; right.
    eapply cpn3_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo3_clo; left.
      left. eapply paco3_mon; [apply H|].
      intros. apply rclo3_clo; right. apply cpn3_step.
      eapply gf_mon; [apply PR1|].
      intros. apply cpn3_base, rclo3_base, PR2.
    + apply rclo3_clo; right. apply cpn3_step.
      eapply gf_mon; [apply H|].
      intros. apply cpn3_base, rclo3_base, PR1.
  - eapply gf_mon. apply PR.
    intros. apply rclo3_base, PR0. 
Qed.

Lemma cpn3_from_paco r:
  paco3 fcpn3 r <3= cpn3 r.
Proof. intros. apply cpn3_from_upaco. left. apply PR. Qed.

Lemma fcpn3_from_paco r:
  paco3 fcpn3 r <3= fcpn3 r.
Proof.
  intros. _punfold PR; [|apply fcpn3_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn3_cpn.
  eapply cpn3_mon; [apply PR0|].
  apply cpn3_from_upaco.
Qed.

Lemma fcpn3_to_paco r:
  fcpn3 r <3= paco3 fcpn3 r.
Proof.
  intros. pfold. eapply fcpn3_mon; [apply PR|].
  intros. right. apply PR0.
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

Lemma cpn3_init:
  cpn3 bot3 <3= paco3 gf bot3.
Proof.
  intros. apply fcpn3_sound, fcpn3_to_paco, (compat3_compat cpn3_compat).
  eapply cpn3_mon; [apply PR|contradiction].
Qed.

Lemma cpn3_clo
      r clo (LE: clo <4= cpn3):
  clo (cpn3 r) <3= cpn3 r.
Proof.
  intros. apply cpn3_cpn, LE, PR.
Qed.

Lemma cpn3_unfold:
  cpn3 bot3 <3= fcpn3 bot3.
Proof.
  intros. apply cpn3_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn3_complete, PR0.
Qed.

Lemma fcpn3_clo
      r clo (LE: clo <4= cpn3):
  clo (fcpn3 r) <3= fcpn3 r.
Proof.
  intros. apply LE, (compat3_compat cpn3_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn3_cpn, PR0.
Qed.

Lemma cpn3_final: forall r, upaco3 gf r <3= cpn3 r.
Proof.
  intros. eapply cpn3_from_upaco.
  intros. eapply upaco3_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn3_base, PR1.
Qed.

Lemma fcpn3_final: forall r, paco3 gf r <3= fcpn3 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn3_final].
Qed.

Lemma cpn3_algebra r :
  r <3= gf r -> r <3= cpn3 bot3.
Proof.
  intros. apply cpn3_final. left.
  revert x0 x1 x2 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion3_main.

Lemma cpn3_mon_bot (gf gf': rel -> rel) x0 x1 x2 r
      (IN: @cpn3 gf bot3 x0 x1 x2)
      (MONgf: monotone3 gf)
      (MONgf': monotone3 gf')
      (LE: gf <4= gf'):
  @cpn3 gf' r x0 x1 x2.
Proof.
  apply cpn3_init in IN; [|apply MONgf].
  apply cpn3_final; [apply MONgf'|].
  left. eapply paco3_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn3_mon_bot (gf gf': rel -> rel) x0 x1 x2 r
      (IN: @fcpn3 gf bot3 x0 x1 x2)
      (MONgf: monotone3 gf)
      (MONgf': monotone3 gf')
      (LE: gf <4= gf'):
  @fcpn3 gf' r x0 x1 x2.
Proof.
  apply LE. eapply MONgf. apply IN.
  intros. eapply cpn3_mon_bot; eassumption.
Qed.

End Companion3.

Hint Unfold fcpn3 : paco.

Hint Resolve cpn3_base : paco.
Hint Resolve cpn3_step : paco.
Hint Constructors rclo3 : paco.
Hint Resolve rclo3_clo : paco.
