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

Inductive cpn11 (r: rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Prop :=
| cpn11_intro
    clo
    (COM: compatible11 clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
.

Definition fcpn11 := compose gf cpn11.

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

Lemma fcpn11_mon: monotone11 fcpn11.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn11_mon; [apply PR|apply LE].
Qed.

Lemma fcpn11_sound:
  paco11 fcpn11 bot11 <11= paco11 gf bot11.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \11/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn11 n (paco11 fcpn11 bot11) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn11 n (paco11 fcpn11 bot11) <11= gf (rclo cpn11 (S n) (paco11 fcpn11 bot11))).
  { intro X. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply fcpn11_mon].
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
    x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    (IN: r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10):
    @rclo11 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
| rclo11_clo'
    r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    (LE: r' <11= rclo11 clo r)
    (IN: clo r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10):
    @rclo11 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
.           

Structure wcompatible11 (clo: rel -> rel) : Prop :=
  wcompat11_intro {
      wcompat11_mon: monotone11 clo;
      wcompat11_wcompat : forall r,
          clo (gf r) <11= gf (rclo11 (clo \12/ cpn11) r);
    }.


Lemma rclo11_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
      (IN: @rclo11 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (LEclo: clo <12= clo')
      (LEr: r <11= r') :
  @rclo11 clo' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
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

Lemma rclo11_rclo clo r:
  rclo11 clo (rclo11 clo r) <11= rclo11 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo11_compose clo r:
  rclo11 (rclo11 clo) r <11= rclo11 clo r.
Proof.
  intros. induction PR.
  - apply rclo11_base, IN.
  - apply rclo11_rclo.
    eapply rclo11_mon; [apply IN|apply H].
Qed.

Lemma rclo11_compat clo
      (COM: compatible11 clo):
  compatible11 (rclo11 clo).
Proof.
  econstructor.
  - apply rclo11_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo11_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo11_clo. apply PR.
Qed.

Lemma wcompat11_compat  clo
      (WCOM: wcompatible11 clo):
  compatible11 (rclo11 (clo \12/ cpn11)).
Proof.
  econstructor; [eapply rclo11_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply IN|]. intros.
    apply rclo11_base. apply PR.
  - destruct IN as [IN|IN].
    + eapply gf_mon.
      * eapply WCOM. eapply WCOM; [apply IN|apply H].
      * intros. apply rclo11_rclo, PR.
    + eapply gf_mon; [|intros; apply rclo11_clo; right; apply PR].
      apply (compat11_compat cpn11_compat).
      eapply cpn11_mon; [apply IN|apply H].
Qed.

Lemma wcompat11_sound clo
      (WCOM: wcompatible11 clo):
  clo <12= cpn11.
Proof.
  intros. exists (rclo11 (clo \12/ cpn11)).
  - apply wcompat11_compat, WCOM.
  - apply rclo11_clo.
    left. eapply WCOM. apply PR.
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

Lemma cpn11_step r:
  fcpn11 r <11= cpn11 r.
Proof.
  intros. eapply cpn11_cpn. exists gf.
  - econstructor. apply gf_mon. intros; apply PR0.
  - apply PR.
Qed.

Lemma cpn11_from_upaco r:
  upaco11 fcpn11 r <11= cpn11 r.
Proof.
  eapply wcompat11_sound.
  econstructor; [apply upaco11_mon|].
  intros. destruct PR as [PR|PR].
  - _punfold PR; [|apply fcpn11_mon]. 
    eapply gf_mon; [apply PR|].
    intros. apply rclo11_clo; right.
    eapply cpn11_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo11_clo; left.
      left. eapply paco11_mon; [apply H|].
      intros. apply rclo11_clo; right. apply cpn11_step.
      eapply gf_mon; [apply PR1|].
      intros. apply cpn11_base, rclo11_base, PR2.
    + apply rclo11_clo; right. apply cpn11_step.
      eapply gf_mon; [apply H|].
      intros. apply cpn11_base, rclo11_base, PR1.
  - eapply gf_mon. apply PR.
    intros. apply rclo11_base, PR0. 
Qed.

Lemma cpn11_from_paco r:
  paco11 fcpn11 r <11= cpn11 r.
Proof. intros. apply cpn11_from_upaco. left. apply PR. Qed.

Lemma fcpn11_from_paco r:
  paco11 fcpn11 r <11= fcpn11 r.
Proof.
  intros. _punfold PR; [|apply fcpn11_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn11_cpn.
  eapply cpn11_mon; [apply PR0|].
  apply cpn11_from_upaco.
Qed.

Lemma fcpn11_to_paco r:
  fcpn11 r <11= paco11 fcpn11 r.
Proof.
  intros. pfold. eapply fcpn11_mon; [apply PR|].
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
  intros. apply fcpn11_sound, fcpn11_to_paco, (compat11_compat cpn11_compat).
  eapply cpn11_mon; [apply PR|contradiction].
Qed.

Lemma cpn11_clo
      r clo (LE: clo <12= cpn11):
  clo (cpn11 r) <11= cpn11 r.
Proof.
  intros. apply cpn11_cpn, LE, PR.
Qed.

Lemma cpn11_unfold:
  cpn11 bot11 <11= fcpn11 bot11.
Proof.
  intros. apply cpn11_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn11_complete, PR0.
Qed.

Lemma fcpn11_clo
      r clo (LE: clo <12= cpn11):
  clo (fcpn11 r) <11= fcpn11 r.
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

Lemma fcpn11_final: forall r, paco11 gf r <11= fcpn11 r.
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

Lemma cpn11_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r
      (IN: @cpn11 gf bot11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (MONgf: monotone11 gf)
      (MONgf': monotone11 gf')
      (LE: gf <12= gf'):
  @cpn11 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  apply cpn11_init in IN; [|apply MONgf].
  apply cpn11_final; [apply MONgf'|].
  left. eapply paco11_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn11_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r
      (IN: @fcpn11 gf bot11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (MONgf: monotone11 gf)
      (MONgf': monotone11 gf')
      (LE: gf <12= gf'):
  @fcpn11 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  apply LE. eapply MONgf. apply IN.
  intros. eapply cpn11_mon_bot; eassumption.
Qed.

End Companion11.

Hint Unfold fcpn11 : paco.

Hint Resolve cpn11_base : paco.
Hint Resolve cpn11_step : paco.
Hint Constructors rclo11 : paco.
Hint Resolve rclo11_clo : paco.
