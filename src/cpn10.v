Require Export Program.Basics. Open Scope program_scope.
Require Import paco10 pacotac.
Set Implicit Arguments.

Section Companion10.

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

Local Notation rel := (rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9).

Section Companion10_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone10 gf.

(** 
  Compatibility, Companion & Guarded Companion
*)

Structure compatible10 (clo: rel -> rel) : Prop :=
  compat10_intro {
      compat10_mon: monotone10 clo;
      compat10_compat : forall r,
          clo (gf r) <10= gf (clo r);
    }.

Inductive cpn10 (r: rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop :=
| cpn10_intro
    clo
    (COM: compatible10 clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
.

Definition fcpn10 := compose gf cpn10.

Lemma cpn10_mon: monotone10 cpn10.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat10_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn10_compat: compatible10 cpn10.
Proof.
  econstructor; [apply cpn10_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat10_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn10_greatest: forall clo (COM: compatible10 clo), clo <11= cpn10.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn10_cpn: forall r,
    cpn10 (cpn10 r) <10= cpn10 r.
Proof.
  intros. exists (compose cpn10 cpn10); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn10_mon; [apply IN|].
    intros. eapply cpn10_mon; [apply PR0|apply LE].
  - intros. eapply (compat10_compat cpn10_compat).
    eapply cpn10_mon; [apply PR0|].
    intros. eapply (compat10_compat cpn10_compat), PR1. 
Qed.

Lemma monotone10_compose (clo1 clo2: rel -> rel)
      (MON1: monotone10 clo1)
      (MON2: monotone10 clo2):
  monotone10 (compose clo1 clo2).
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma fcpn10_mon: monotone10 fcpn10.
Proof.
  apply monotone10_compose. apply gf_mon. apply cpn10_mon.
Qed.

Lemma fcpn10_sound:
  paco10 fcpn10 bot10 <10= paco10 gf bot10.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \10/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn10 n (paco10 fcpn10 bot10) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn10 n (paco10 fcpn10 bot10) <10= gf (rclo cpn10 (S n) (paco10 fcpn10 bot10))).
  { intro X. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply fcpn10_mon].
    + intros. right. eapply cpn10_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat10_compat cpn10_compat).
        eapply (compat10_mon cpn10_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo10 (clo: rel->rel) (r: rel): rel :=
| rclo10_base
    x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    (IN: r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9):
    @rclo10 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
| rclo10_clo'
    r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    (LE: r' <10= rclo10 clo r)
    (IN: clo r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9):
    @rclo10 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
.           

Structure wcompatible10 (clo: rel -> rel) : Prop :=
  wcompat10_intro {
      wcompat10_mon: monotone10 clo;
      wcompat10_wcompat : forall r,
          clo (gf r) <10= gf (rclo10 (clo \11/ cpn10) r);
    }.

Lemma rclo10_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
      (IN: @rclo10 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (LEclo: clo <11= clo')
      (LEr: r <10= r') :
  @rclo10 clo' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo10_mon clo:
  monotone10 (rclo10 clo).
Proof.
  repeat intro. eapply rclo10_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo10_clo clo r:
  clo (rclo10 clo r) <10= rclo10 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo10_rclo clo r:
  rclo10 clo (rclo10 clo r) <10= rclo10 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo10_compose clo r:
  rclo10 (rclo10 clo) r <10= rclo10 clo r.
Proof.
  intros. induction PR.
  - apply rclo10_base, IN.
  - apply rclo10_rclo.
    eapply rclo10_mon; [apply IN|apply H].
Qed.

Lemma rclo10_compat clo
      (COM: compatible10 clo):
  compatible10 (rclo10 clo).
Proof.
  econstructor.
  - apply rclo10_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo10_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo10_clo. apply PR.
Qed.

Lemma wcompat10_compat  clo
      (WCOM: wcompatible10 clo):
  compatible10 (rclo10 (clo \11/ cpn10)).
Proof.
  econstructor; [eapply rclo10_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply IN|]. intros.
    apply rclo10_base. apply PR.
  - destruct IN as [IN|IN].
    + eapply gf_mon.
      * eapply WCOM. eapply WCOM; [apply IN|apply H].
      * intros. apply rclo10_rclo, PR.
    + eapply gf_mon; [|intros; apply rclo10_clo; right; apply PR].
      apply (compat10_compat cpn10_compat).
      eapply cpn10_mon; [apply IN|apply H].
Qed.

Lemma wcompat10_sound clo
      (WCOM: wcompatible10 clo):
  clo <11= cpn10.
Proof.
  intros. exists (rclo10 (clo \11/ cpn10)).
  - apply wcompat10_compat, WCOM.
  - apply rclo10_clo.
    left. eapply WCOM. apply PR.
    intros. apply rclo10_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn10_base: forall r, r <10= cpn10 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
  - apply PR.
Qed.

Lemma cpn10_step r:
  fcpn10 r <10= cpn10 r.
Proof.
  intros. eapply cpn10_cpn. exists gf.
  - econstructor. apply gf_mon. intros; apply PR0.
  - apply PR.
Qed.

Lemma cpn10_from_upaco r:
  upaco10 fcpn10 r <10= cpn10 r.
Proof.
  eapply wcompat10_sound.
  econstructor; [apply upaco10_mon|].
  intros. destruct PR as [PR|PR].
  - _punfold PR; [|apply fcpn10_mon]. 
    eapply gf_mon; [apply PR|].
    intros. apply rclo10_clo; right.
    eapply cpn10_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo10_clo; left.
      left. eapply paco10_mon; [apply H|].
      intros. apply rclo10_clo; right. apply cpn10_step.
      eapply gf_mon; [apply PR1|].
      intros. apply cpn10_base, rclo10_base, PR2.
    + apply rclo10_clo; right. apply cpn10_step.
      eapply gf_mon; [apply H|].
      intros. apply cpn10_base, rclo10_base, PR1.
  - eapply gf_mon. apply PR.
    intros. apply rclo10_base, PR0. 
Qed.

Lemma cpn10_from_paco r:
  paco10 fcpn10 r <10= cpn10 r.
Proof. intros. apply cpn10_from_upaco. left. apply PR. Qed.

Lemma fcpn10_from_paco r:
  paco10 fcpn10 r <10= fcpn10 r.
Proof.
  intros. _punfold PR; [|apply fcpn10_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn10_cpn.
  eapply cpn10_mon; [apply PR0|].
  apply cpn10_from_upaco.
Qed.

Lemma fcpn10_to_paco r:
  fcpn10 r <10= paco10 fcpn10 r.
Proof.
  intros. pfold. eapply fcpn10_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn10_complete:
  paco10 gf bot10 <10= cpn10 bot10.
Proof.
  intros. apply cpn10_from_paco.
  eapply paco10_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn10_base].
  - intros. apply PR0.
Qed.

Lemma cpn10_init:
  cpn10 bot10 <10= paco10 gf bot10.
Proof.
  intros. apply fcpn10_sound, fcpn10_to_paco, (compat10_compat cpn10_compat).
  eapply cpn10_mon; [apply PR|contradiction].
Qed.

Lemma cpn10_clo
      r clo (LE: clo <11= cpn10):
  clo (cpn10 r) <10= cpn10 r.
Proof.
  intros. apply cpn10_cpn, LE, PR.
Qed.

Lemma cpn10_unfold:
  cpn10 bot10 <10= fcpn10 bot10.
Proof.
  intros. apply cpn10_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn10_complete, PR0.
Qed.

Lemma fcpn10_clo
      r clo (LE: clo <11= cpn10):
  clo (fcpn10 r) <10= fcpn10 r.
Proof.
  intros. apply LE, (compat10_compat cpn10_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn10_cpn, PR0.
Qed.

Lemma cpn10_final: forall r, upaco10 gf r <10= cpn10 r.
Proof.
  intros. eapply cpn10_from_upaco.
  intros. eapply upaco10_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn10_base, PR1.
Qed.

Lemma fcpn10_final: forall r, paco10 gf r <10= fcpn10 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn10_final].
Qed.

Lemma cpn10_algebra r :
  r <10= gf r -> r <10= cpn10 bot10.
Proof.
  intros. apply cpn10_final. left.
  revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion10_main.

Lemma cpn10_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r
      (IN: @cpn10 gf bot10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (MONgf: monotone10 gf)
      (MONgf': monotone10 gf')
      (LE: gf <11= gf'):
  @cpn10 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  apply cpn10_init in IN; [|apply MONgf].
  apply cpn10_final; [apply MONgf'|].
  left. eapply paco10_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn10_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r
      (IN: @fcpn10 gf bot10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (MONgf: monotone10 gf)
      (MONgf': monotone10 gf')
      (LE: gf <11= gf'):
  @fcpn10 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  apply LE. eapply MONgf. apply IN.
  intros. eapply cpn10_mon_bot; eassumption.
Qed.

End Companion10.

Hint Unfold fcpn10 : paco.

Hint Resolve cpn10_base : paco.
Hint Resolve cpn10_step : paco.
Hint Constructors rclo10 : paco.
Hint Resolve rclo10_clo : paco.
