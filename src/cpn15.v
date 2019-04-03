Require Export Program.Basics. Open Scope program_scope.
Require Import paco15 pacotac.
Set Implicit Arguments.

Section Companion15.

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
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.
Variable T14 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12), Type.

Local Notation rel := (rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14).

Section Companion15_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone15 gf.

(** 
  Bounded Compatibility, Companion & Guarded Companion
*)

Inductive pointwise_union (bnd: rel -> rel) (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 : Prop :=
| pw_union_ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14
            (IN: r d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14)
            (PTW: forall (s: rel), s d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 -> bnd s e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14)
.

Structure compatible_bound15 (bnd: rel -> rel) : Prop :=
  cbound15_intro {
      cbound15_distr : forall r,
          bnd r <15= pointwise_union bnd r;
      cbound15_compat: forall r,
          bnd (gf r) <15= gf (bnd r);
      cbound15_bound: forall r,
          bnd (bnd r) <15= (bnd r \15/ gf (bnd r));
    }.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound15 bnd.

Structure compatible15 (clo: rel -> rel) : Prop :=
  compat15_intro {
      compat15_mon: monotone15 clo;
      compat15_compat : forall r,
          clo (gf r) <15= gf (clo r);
      compat15_bound : forall r,
          bnd (clo r) <15= (bnd r \15/ gf (clo r))
    }.

Inductive cpn15 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 : Prop :=
| cpn15_intro
    clo
    (COM: compatible15 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14)
.

Definition fcpn15 := compose gf cpn15.

Lemma cbound15_union r1 r2 : bnd (r1 \15/ r2) <15= (bnd r1 \15/ bnd r2).
Proof.
  intros. eapply cbound15_distr in PR; [|apply bnd_compat].
  destruct PR. destruct IN.
  - left. apply PTW, H.
  - right. apply PTW, H.
Qed.

Lemma cbound15_mon: monotone15 bnd.
Proof.
  repeat intro.
  apply (cbound15_distr bnd_compat) in IN.
  destruct IN.
  apply PTW, LE, IN.
Qed.

Lemma cpn15_mon: monotone15 cpn15.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat15_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn15_compat: compatible15 cpn15.
Proof.
  econstructor; [apply cpn15_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (compat15_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - eapply (cbound15_distr bnd_compat) in PR.
    destruct PR. destruct IN.
    specialize (PTW (clo r) CLO).
    apply (compat15_bound COM) in PTW.
    destruct PTW.
    + left. apply H.
    + right. eapply gf_mon; [apply H|].
      intros. econstructor;[apply COM|apply PR].
Qed.

Lemma cpn15_greatest: forall clo (COM: compatible15 clo), clo <16= cpn15.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn15_base: forall r, r <15= cpn15 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
    + left. apply PR0.
  - apply PR.
Qed.

Lemma cpn15_bound : forall r, bnd r <15= cpn15 r.
Proof.
  intros. exists bnd.
  - econstructor; repeat intro.
    + eapply cbound15_mon. apply IN. apply LE.
    + apply (cbound15_compat bnd_compat), PR0.
    + apply (cbound15_bound bnd_compat), PR0.
  - apply PR.
Qed.

Lemma cpn15_cpn: forall r,
    cpn15 (cpn15 r) <15= cpn15 r.
Proof.
  intros. exists (compose cpn15 cpn15); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn15_mon; [apply IN|].
    intros. eapply cpn15_mon; [apply PR0|apply LE].
  - intros. eapply (compat15_compat cpn15_compat).
    eapply cpn15_mon; [apply PR0|].
    intros. eapply (compat15_compat cpn15_compat), PR1.
  - intros. eapply (compat15_bound cpn15_compat) in PR0.
    destruct PR0; [|right; apply H].
    eapply (compat15_bound cpn15_compat) in H.
    destruct H; [left; apply H|].
    right. eapply gf_mon; [apply H|].
    intros. apply cpn15_base. apply PR0.
Qed.

Lemma fcpn15_mon: monotone15 fcpn15.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn15_mon; [apply PR|apply LE].
Qed.

Lemma fcpn15_sound:
  paco15 fcpn15 bot15 <15= paco15 gf bot15.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \15/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn15 n (paco15 fcpn15 bot15) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn15 n (paco15 fcpn15 bot15) <15= gf (rclo cpn15 (S n) (paco15 fcpn15 bot15))).
  { intro X. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply fcpn15_mon].
    + intros. right. eapply cpn15_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat15_compat cpn15_compat).
        eapply (compat15_mon cpn15_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo15 (clo: rel->rel) (r: rel): rel :=
| rclo15_base
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14):
    @rclo15 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
| rclo15_clo'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
    (R': r' <15= rclo15 clo r)
    (CLOR': clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14):
    @rclo15 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
| rclo15_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
    (R': r' <15= rclo15 clo r)
    (CLOR': @gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14):
    @rclo15 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
| rclo15_cpn'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
    (R': r' <15= rclo15 clo r)
    (CLOR': @cpn15 r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14):
    @rclo15 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
.

Structure wcompatible15 (clo: rel -> rel) : Prop :=
  wcompat15_intro {
      wcompat15_mon: monotone15 clo;
      wcompat15_wcompat: forall r,
          clo (gf r) <15= gf (rclo15 clo r);
      wcompat15_bound : forall r,
          bnd (clo r) <15= (bnd r \15/ gf (rclo15 clo r))
    }.

Lemma rclo15_mon_gen clo clo' r r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
      (IN: @rclo15 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14)
      (LEclo: clo <16= clo')
      (LEr: r <15= r') :
  @rclo15 clo' r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn15_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo15_mon clo:
  monotone15 (rclo15 clo).
Proof.
  repeat intro. eapply rclo15_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo15_clo clo r:
  clo (rclo15 clo r) <15= rclo15 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo15_step clo r:
  gf (rclo15 clo r) <15= rclo15 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo15_cpn clo r:
  cpn15 (rclo15 clo r) <15= rclo15 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo15_mult clo r:
  rclo15 clo (rclo15 clo r) <15= rclo15 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo15_compose clo r:
  rclo15 (rclo15 clo) r <15= rclo15 clo r.
Proof.
  intros. induction PR.
  - apply rclo15_base, R.
  - apply rclo15_mult.
    eapply rclo15_mon; [apply CLOR'|apply H].
  - apply rclo15_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo15_cpn.
    eapply cpn15_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat15_compat
      clo (WCOM: wcompatible15 clo):
  compatible15 (rclo15 clo).
Proof.
  econstructor; [eapply rclo15_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo15_base. apply PR.
    + eapply gf_mon.
      * eapply (wcompat15_wcompat WCOM).
        eapply (wcompat15_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo15_mult, PR.
    + eapply gf_mon; [apply CLOR'|].
      intros. apply H in PR. apply rclo15_step, PR.
    + eapply gf_mon; [|intros; apply rclo15_cpn, PR].
      apply (compat15_compat cpn15_compat).
      eapply cpn15_mon; [apply CLOR'|apply H].
  - eapply (cbound15_distr bnd_compat) in PR.
    destruct PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 PTW.
    induction IN; intros.
    + left. apply PTW, R.
    + specialize (PTW _ CLOR').
      eapply (wcompat15_bound WCOM) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound15_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo15_mult.
        eapply rclo15_mon, R'. apply PR.
    + specialize (PTW _ CLOR').
      eapply (cbound15_compat bnd_compat) in PTW.
      right. eapply gf_mon. apply PTW. intros.
      eapply (cbound15_distr bnd_compat) in PR.
      destruct PR.
      eapply H in IN; [|apply PTW0].
      destruct IN.
      * apply rclo15_cpn, cpn15_bound.
        eapply cbound15_mon. apply H0. apply rclo15_base.
      * apply rclo15_step. apply H0.
    + specialize (PTW _ CLOR').
      apply (compat15_bound cpn15_compat) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound15_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo15_cpn.
        eapply cpn15_mon; [apply PR|].
        intros. apply R', PR0.
Qed.

Lemma wcompat15_sound clo (WCOM: wcompatible15 clo):
  clo <16= cpn15.
Proof.
  intros. exists (rclo15 clo).
  - apply wcompat15_compat, WCOM.
  - apply rclo15_clo.
    eapply (wcompat15_mon WCOM); [apply PR|].
    intros. apply rclo15_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn15_from_upaco r:
  upaco15 fcpn15 r <15= cpn15 r.
Proof.
  intros. destruct PR; [| apply cpn15_base, H].
  exists (rclo15 (paco15 fcpn15)).
  - apply wcompat15_compat.
    econstructor; [apply paco15_mon| |].
    + intros. _punfold PR; [|apply fcpn15_mon].
      eapply gf_mon; [apply PR|].
      intros. apply rclo15_cpn.
      eapply cpn15_mon; [apply PR0|].
      intros. destruct PR1.
      * apply rclo15_clo.
        eapply paco15_mon; [apply H0|].
        intros. apply rclo15_step.
        eapply gf_mon; [apply PR1|].
        intros. apply rclo15_base, PR2.
      * apply rclo15_step.
        eapply gf_mon; [apply H0|].
        intros. apply rclo15_base, PR1.
    + intros. right.
      eapply gf_mon, rclo15_cpn.
      eapply gf_mon, cpn15_bound.
      apply (cbound15_compat bnd_compat).
      eapply cbound15_mon. apply PR.
      intros. _punfold PR0; [|apply fcpn15_mon].
      eapply gf_mon. apply PR0.
      intros. apply rclo15_cpn.
      eapply cpn15_mon. apply PR1.
      intros. destruct PR2.
      * apply rclo15_clo.
        eapply paco15_mon. apply H0.
        intros. apply rclo15_base. apply PR2.
      * apply rclo15_base. apply H0.
  - apply rclo15_clo.
    eapply paco15_mon; [apply H|].
    intros. apply rclo15_base, PR.
Qed.

Lemma cpn15_from_paco r:
  paco15 fcpn15 r <15= cpn15 r.
Proof. intros. apply cpn15_from_upaco. left. apply PR. Qed.

Lemma fcpn15_from_paco r:
  paco15 fcpn15 r <15= fcpn15 r.
Proof.
  intros. _punfold PR; [|apply fcpn15_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn15_cpn.
  eapply cpn15_mon; [apply PR0|].
  apply cpn15_from_upaco.
Qed.

Lemma fcpn15_to_paco r:
  fcpn15 r <15= paco15 fcpn15 r.
Proof.
  intros. pfold. eapply fcpn15_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn15_complete:
  paco15 gf bot15 <15= cpn15 bot15.
Proof.
  intros. apply cpn15_from_paco.
  eapply paco15_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn15_base].
  - intros. apply PR0.
Qed.

Lemma cpn15_init:
  cpn15 bot15 <15= paco15 gf bot15.
Proof.
  intros. apply fcpn15_sound, fcpn15_to_paco, (compat15_compat cpn15_compat).
  eapply cpn15_mon; [apply PR|contradiction].
Qed.

Lemma cpn15_clo
      r clo (LE: clo <16= cpn15):
  clo (cpn15 r) <15= cpn15 r.
Proof.
  intros. apply cpn15_cpn, LE, PR.
Qed.

Lemma cpn15_unfold:
  cpn15 bot15 <15= fcpn15 bot15.
Proof.
  intros. apply cpn15_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn15_complete, PR0.
Qed.

Lemma cpn15_unfold_bound r
      (BASE: forall r, r <15= bnd r):
  cpn15 r <15= (bnd r \15/ fcpn15 r).
Proof.
  intros. apply BASE in PR.
  eapply compat15_bound in PR.
  - apply PR.
  - apply cpn15_compat.
Qed.

Lemma cpn15_step r:
  fcpn15 r <15= cpn15 r.
Proof.
  intros. eapply cpn15_clo, PR.
  intros. eapply wcompat15_sound, PR0.
  econstructor; [apply gf_mon| |].
  - intros. eapply gf_mon; [apply PR1|].
    intros. apply rclo15_step.
    eapply gf_mon; [apply PR2|].
    intros. apply rclo15_base, PR3.
  - intros. apply (cbound15_compat bnd_compat) in PR1.
    right. eapply gf_mon. apply PR1.
    intros. apply rclo15_cpn, cpn15_bound.
    eapply cbound15_mon. apply PR2.
    intros. apply rclo15_base, PR3.
Qed.

Lemma fcpn15_clo
      r clo (LE: clo <16= cpn15):
  clo (fcpn15 r) <15= fcpn15 r.
Proof.
  intros. apply LE, (compat15_compat cpn15_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn15_cpn, PR0.
Qed.

Lemma cpn15_final: forall r, upaco15 gf r <15= cpn15 r.
Proof.
  intros. eapply cpn15_from_upaco.
  intros. eapply upaco15_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn15_base, PR1.
Qed.

Lemma fcpn15_final: forall r, paco15 gf r <15= fcpn15 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn15_final].
Qed.

Lemma cpn15_algebra r :
  r <15= gf r -> r <15= cpn15 bot15.
Proof.
  intros. apply cpn15_final. left.
  revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion15_main.

Lemma cbound15_bot gf:
  compatible_bound15 gf bot16.
Proof.
  econstructor; intros; contradiction.
Qed.

Lemma cpn15_mon_bot (gf gf': rel -> rel) bnd bnd' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 r
      (IN: @cpn15 gf bnd bot15 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14)
      (MON: monotone15 gf)
      (MON': monotone15 gf')
      (BASE: compatible_bound15 gf bnd)
      (BASE': compatible_bound15 gf' bnd')
      (LE: gf <16= gf'):
  @cpn15 gf' bnd' r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
Proof.
  apply cpn15_init in IN; [|apply MON|apply BASE].
  apply cpn15_final; [apply MON'|apply BASE'|].
  left. eapply paco15_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn15_mon_bot (gf gf': rel -> rel) bnd bnd' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 r
      (IN: @fcpn15 gf bnd bot15 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14)
      (MON: monotone15 gf)
      (MON': monotone15 gf')
      (BASE: compatible_bound15 gf bnd)
      (BASE': compatible_bound15 gf' bnd')
      (LE: gf <16= gf'):
  @fcpn15 gf' bnd' r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
Proof.
  apply LE. eapply MON. apply IN.
  intros. eapply cpn15_mon_bot; eassumption.
Qed.

End Companion15.

Hint Unfold fcpn15 : paco.
Hint Resolve cpn15_base : paco.
Hint Resolve cpn15_step : paco.
Hint Resolve cbound15_bot : paco.

Hint Constructors rclo15 : rclo.
Hint Resolve rclo15_clo rclo15_step rclo15_cpn : rclo.

