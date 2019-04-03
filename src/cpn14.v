Require Export Program.Basics. Open Scope program_scope.
Require Import paco14 pacotac.
Set Implicit Arguments.

Section Companion14.

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

Local Notation rel := (rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13).

Section Companion14_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone14 gf.

(** 
  Bounded Compatibility, Companion & Guarded Companion
*)

Inductive pointwise_union (bnd: rel -> rel) (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 : Prop :=
| pw_union_ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13
            (IN: r d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13)
            (PTW: forall (s: rel), s d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 -> bnd s e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
.

Structure compatible_bound14 (bnd: rel -> rel) : Prop :=
  cbound14_intro {
      cbound14_distr : forall r,
          bnd r <14= pointwise_union bnd r;
      cbound14_compat: forall r,
          bnd (gf r) <14= gf (bnd r);
      cbound14_bound: forall r,
          bnd (bnd r) <14= (bnd r \14/ gf (bnd r));
    }.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound14 bnd.

Structure compatible14 (clo: rel -> rel) : Prop :=
  compat14_intro {
      compat14_mon: monotone14 clo;
      compat14_compat : forall r,
          clo (gf r) <14= gf (clo r);
      compat14_bound : forall r,
          bnd (clo r) <14= (bnd r \14/ gf (clo r))
    }.

Inductive cpn14 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 : Prop :=
| cpn14_intro
    clo
    (COM: compatible14 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
.

Definition fcpn14 := compose gf cpn14.

Lemma cbound14_union r1 r2 : bnd (r1 \14/ r2) <14= (bnd r1 \14/ bnd r2).
Proof.
  intros. eapply cbound14_distr in PR; [|apply bnd_compat].
  destruct PR. destruct IN.
  - left. apply PTW, H.
  - right. apply PTW, H.
Qed.

Lemma cbound14_mon: monotone14 bnd.
Proof.
  repeat intro.
  apply (cbound14_distr bnd_compat) in IN.
  destruct IN.
  apply PTW, LE, IN.
Qed.

Lemma cpn14_mon: monotone14 cpn14.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat14_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn14_compat: compatible14 cpn14.
Proof.
  econstructor; [apply cpn14_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (compat14_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - eapply (cbound14_distr bnd_compat) in PR.
    destruct PR. destruct IN.
    specialize (PTW (clo r) CLO).
    apply (compat14_bound COM) in PTW.
    destruct PTW.
    + left. apply H.
    + right. eapply gf_mon; [apply H|].
      intros. econstructor;[apply COM|apply PR].
Qed.

Lemma cpn14_greatest: forall clo (COM: compatible14 clo), clo <15= cpn14.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn14_base: forall r, r <14= cpn14 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
    + left. apply PR0.
  - apply PR.
Qed.

Lemma cpn14_bound : forall r, bnd r <14= cpn14 r.
Proof.
  intros. exists bnd.
  - econstructor; repeat intro.
    + eapply cbound14_mon. apply IN. apply LE.
    + apply (cbound14_compat bnd_compat), PR0.
    + apply (cbound14_bound bnd_compat), PR0.
  - apply PR.
Qed.

Lemma cpn14_cpn: forall r,
    cpn14 (cpn14 r) <14= cpn14 r.
Proof.
  intros. exists (compose cpn14 cpn14); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn14_mon; [apply IN|].
    intros. eapply cpn14_mon; [apply PR0|apply LE].
  - intros. eapply (compat14_compat cpn14_compat).
    eapply cpn14_mon; [apply PR0|].
    intros. eapply (compat14_compat cpn14_compat), PR1.
  - intros. eapply (compat14_bound cpn14_compat) in PR0.
    destruct PR0; [|right; apply H].
    eapply (compat14_bound cpn14_compat) in H.
    destruct H; [left; apply H|].
    right. eapply gf_mon; [apply H|].
    intros. apply cpn14_base. apply PR0.
Qed.

Lemma fcpn14_mon: monotone14 fcpn14.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn14_mon; [apply PR|apply LE].
Qed.

Lemma fcpn14_sound:
  paco14 fcpn14 bot14 <14= paco14 gf bot14.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \14/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn14 n (paco14 fcpn14 bot14) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn14 n (paco14 fcpn14 bot14) <14= gf (rclo cpn14 (S n) (paco14 fcpn14 bot14))).
  { intro X. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply fcpn14_mon].
    + intros. right. eapply cpn14_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat14_compat cpn14_compat).
        eapply (compat14_mon cpn14_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo14 (clo: rel->rel) (r: rel): rel :=
| rclo14_base
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13):
    @rclo14 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
| rclo14_clo'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
    (R': r' <14= rclo14 clo r)
    (CLOR': clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13):
    @rclo14 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
| rclo14_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
    (R': r' <14= rclo14 clo r)
    (CLOR': @gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13):
    @rclo14 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
| rclo14_cpn'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
    (R': r' <14= rclo14 clo r)
    (CLOR': @cpn14 r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13):
    @rclo14 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
.

Structure wcompatible14 (clo: rel -> rel) : Prop :=
  wcompat14_intro {
      wcompat14_mon: monotone14 clo;
      wcompat14_wcompat: forall r,
          clo (gf r) <14= gf (rclo14 clo r);
      wcompat14_bound : forall r,
          bnd (clo r) <14= (bnd r \14/ gf (rclo14 clo r))
    }.

Lemma rclo14_mon_gen clo clo' r r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
      (IN: @rclo14 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
      (LEclo: clo <15= clo')
      (LEr: r <14= r') :
  @rclo14 clo' r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn14_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo14_mon clo:
  monotone14 (rclo14 clo).
Proof.
  repeat intro. eapply rclo14_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo14_clo clo r:
  clo (rclo14 clo r) <14= rclo14 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo14_step clo r:
  gf (rclo14 clo r) <14= rclo14 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo14_cpn clo r:
  cpn14 (rclo14 clo r) <14= rclo14 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo14_mult clo r:
  rclo14 clo (rclo14 clo r) <14= rclo14 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo14_compose clo r:
  rclo14 (rclo14 clo) r <14= rclo14 clo r.
Proof.
  intros. induction PR.
  - apply rclo14_base, R.
  - apply rclo14_mult.
    eapply rclo14_mon; [apply CLOR'|apply H].
  - apply rclo14_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo14_cpn.
    eapply cpn14_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat14_compat
      clo (WCOM: wcompatible14 clo):
  compatible14 (rclo14 clo).
Proof.
  econstructor; [eapply rclo14_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo14_base. apply PR.
    + eapply gf_mon.
      * eapply (wcompat14_wcompat WCOM).
        eapply (wcompat14_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo14_mult, PR.
    + eapply gf_mon; [apply CLOR'|].
      intros. apply H in PR. apply rclo14_step, PR.
    + eapply gf_mon; [|intros; apply rclo14_cpn, PR].
      apply (compat14_compat cpn14_compat).
      eapply cpn14_mon; [apply CLOR'|apply H].
  - eapply (cbound14_distr bnd_compat) in PR.
    destruct PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 PTW.
    induction IN; intros.
    + left. apply PTW, R.
    + specialize (PTW _ CLOR').
      eapply (wcompat14_bound WCOM) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound14_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo14_mult.
        eapply rclo14_mon, R'. apply PR.
    + specialize (PTW _ CLOR').
      eapply (cbound14_compat bnd_compat) in PTW.
      right. eapply gf_mon. apply PTW. intros.
      eapply (cbound14_distr bnd_compat) in PR.
      destruct PR.
      eapply H in IN; [|apply PTW0].
      destruct IN.
      * apply rclo14_cpn, cpn14_bound.
        eapply cbound14_mon. apply H0. apply rclo14_base.
      * apply rclo14_step. apply H0.
    + specialize (PTW _ CLOR').
      apply (compat14_bound cpn14_compat) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound14_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo14_cpn.
        eapply cpn14_mon; [apply PR|].
        intros. apply R', PR0.
Qed.

Lemma wcompat14_sound clo (WCOM: wcompatible14 clo):
  clo <15= cpn14.
Proof.
  intros. exists (rclo14 clo).
  - apply wcompat14_compat, WCOM.
  - apply rclo14_clo.
    eapply (wcompat14_mon WCOM); [apply PR|].
    intros. apply rclo14_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn14_from_upaco r:
  upaco14 fcpn14 r <14= cpn14 r.
Proof.
  intros. destruct PR; [| apply cpn14_base, H].
  exists (rclo14 (paco14 fcpn14)).
  - apply wcompat14_compat.
    econstructor; [apply paco14_mon| |].
    + intros. _punfold PR; [|apply fcpn14_mon].
      eapply gf_mon; [apply PR|].
      intros. apply rclo14_cpn.
      eapply cpn14_mon; [apply PR0|].
      intros. destruct PR1.
      * apply rclo14_clo.
        eapply paco14_mon; [apply H0|].
        intros. apply rclo14_step.
        eapply gf_mon; [apply PR1|].
        intros. apply rclo14_base, PR2.
      * apply rclo14_step.
        eapply gf_mon; [apply H0|].
        intros. apply rclo14_base, PR1.
    + intros. right.
      eapply gf_mon, rclo14_cpn.
      eapply gf_mon, cpn14_bound.
      apply (cbound14_compat bnd_compat).
      eapply cbound14_mon. apply PR.
      intros. _punfold PR0; [|apply fcpn14_mon].
      eapply gf_mon. apply PR0.
      intros. apply rclo14_cpn.
      eapply cpn14_mon. apply PR1.
      intros. destruct PR2.
      * apply rclo14_clo.
        eapply paco14_mon. apply H0.
        intros. apply rclo14_base. apply PR2.
      * apply rclo14_base. apply H0.
  - apply rclo14_clo.
    eapply paco14_mon; [apply H|].
    intros. apply rclo14_base, PR.
Qed.

Lemma cpn14_from_paco r:
  paco14 fcpn14 r <14= cpn14 r.
Proof. intros. apply cpn14_from_upaco. left. apply PR. Qed.

Lemma fcpn14_from_paco r:
  paco14 fcpn14 r <14= fcpn14 r.
Proof.
  intros. _punfold PR; [|apply fcpn14_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn14_cpn.
  eapply cpn14_mon; [apply PR0|].
  apply cpn14_from_upaco.
Qed.

Lemma fcpn14_to_paco r:
  fcpn14 r <14= paco14 fcpn14 r.
Proof.
  intros. pfold. eapply fcpn14_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn14_complete:
  paco14 gf bot14 <14= cpn14 bot14.
Proof.
  intros. apply cpn14_from_paco.
  eapply paco14_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn14_base].
  - intros. apply PR0.
Qed.

Lemma cpn14_init:
  cpn14 bot14 <14= paco14 gf bot14.
Proof.
  intros. apply fcpn14_sound, fcpn14_to_paco, (compat14_compat cpn14_compat).
  eapply cpn14_mon; [apply PR|contradiction].
Qed.

Lemma cpn14_clo
      r clo (LE: clo <15= cpn14):
  clo (cpn14 r) <14= cpn14 r.
Proof.
  intros. apply cpn14_cpn, LE, PR.
Qed.

Lemma cpn14_unfold:
  cpn14 bot14 <14= fcpn14 bot14.
Proof.
  intros. apply cpn14_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn14_complete, PR0.
Qed.

Lemma cpn14_unfold_bound r
      (BASE: forall r, r <14= bnd r):
  cpn14 r <14= (bnd r \14/ fcpn14 r).
Proof.
  intros. apply BASE in PR.
  eapply compat14_bound in PR.
  - apply PR.
  - apply cpn14_compat.
Qed.

Lemma cpn14_step r:
  fcpn14 r <14= cpn14 r.
Proof.
  intros. eapply cpn14_clo, PR.
  intros. eapply wcompat14_sound, PR0.
  econstructor; [apply gf_mon| |].
  - intros. eapply gf_mon; [apply PR1|].
    intros. apply rclo14_step.
    eapply gf_mon; [apply PR2|].
    intros. apply rclo14_base, PR3.
  - intros. apply (cbound14_compat bnd_compat) in PR1.
    right. eapply gf_mon. apply PR1.
    intros. apply rclo14_cpn, cpn14_bound.
    eapply cbound14_mon. apply PR2.
    intros. apply rclo14_base, PR3.
Qed.

Lemma fcpn14_clo
      r clo (LE: clo <15= cpn14):
  clo (fcpn14 r) <14= fcpn14 r.
Proof.
  intros. apply LE, (compat14_compat cpn14_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn14_cpn, PR0.
Qed.

Lemma cpn14_final: forall r, upaco14 gf r <14= cpn14 r.
Proof.
  intros. eapply cpn14_from_upaco.
  intros. eapply upaco14_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn14_base, PR1.
Qed.

Lemma fcpn14_final: forall r, paco14 gf r <14= fcpn14 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn14_final].
Qed.

Lemma cpn14_algebra r :
  r <14= gf r -> r <14= cpn14 bot14.
Proof.
  intros. apply cpn14_final. left.
  revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion14_main.

Lemma cbound14_bot gf:
  compatible_bound14 gf bot15.
Proof.
  econstructor; intros; contradiction.
Qed.

Lemma cpn14_mon_bot (gf gf': rel -> rel) bnd bnd' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 r
      (IN: @cpn14 gf bnd bot14 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
      (MON: monotone14 gf)
      (MON': monotone14 gf')
      (BASE: compatible_bound14 gf bnd)
      (BASE': compatible_bound14 gf' bnd')
      (LE: gf <15= gf'):
  @cpn14 gf' bnd' r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
Proof.
  apply cpn14_init in IN; [|apply MON|apply BASE].
  apply cpn14_final; [apply MON'|apply BASE'|].
  left. eapply paco14_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn14_mon_bot (gf gf': rel -> rel) bnd bnd' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 r
      (IN: @fcpn14 gf bnd bot14 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
      (MON: monotone14 gf)
      (MON': monotone14 gf')
      (BASE: compatible_bound14 gf bnd)
      (BASE': compatible_bound14 gf' bnd')
      (LE: gf <15= gf'):
  @fcpn14 gf' bnd' r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
Proof.
  apply LE. eapply MON. apply IN.
  intros. eapply cpn14_mon_bot; eassumption.
Qed.

End Companion14.

Hint Unfold fcpn14 : paco.
Hint Resolve cpn14_base : paco.
Hint Resolve cpn14_step : paco.
Hint Resolve cbound14_bot : paco.

Hint Constructors rclo14 : rclo.
Hint Resolve rclo14_clo rclo14_step rclo14_cpn : rclo.

