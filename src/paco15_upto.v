Require Import paco15.
Require Export Program.
Set Implicit Arguments.

Section Respectful15.

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

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone15 gf.

Inductive sound15 (clo: rel -> rel): Prop :=
| sound15_intro
    (MON: monotone15 clo)
    (SOUND:
       forall r (PFIX: r <15= gf (clo r)),
         r <15= paco15 gf bot15)
.
Hint Constructors sound15.

Structure respectful15 (clo: rel -> rel) : Prop :=
  respectful15_intro {
      MON: monotone15 clo;
      RESPECTFUL:
        forall l r (LE: l <15= r) (GF: l <15= gf r),
          clo l <15= gf (clo r);
    }.
Hint Constructors respectful15.

Inductive gres15 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 : Prop :=
| gres15_intro
    clo
    (RES: respectful15 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14)
.
Hint Constructors gres15.
Lemma gfclo15_mon: forall clo, sound15 clo -> monotone15 (compose gf clo).
Proof.
  intros; destruct H; red; intros.
  eapply gf_mon; [apply IN|intros; eapply MON0; [apply PR|apply LE]].
Qed.
Hint Resolve gfclo15_mon : paco.

Lemma sound15_is_gf: forall clo (UPTO: sound15 clo),
    paco15 (compose gf clo) bot15 <15= paco15 gf bot15.
Proof.
  intros. _punfold PR; [|apply gfclo15_mon, UPTO]. edestruct UPTO.
  eapply (SOUND (paco15 (compose gf clo) bot15)).
  - intros. _punfold PR0; [|apply gfclo15_mon, UPTO].
    eapply (gfclo15_mon UPTO); [apply PR0| intros; destruct PR1; [apply H|destruct H]].
  - pfold. apply PR.
Qed.

Lemma respectful15_is_sound15: respectful15 <1= sound15.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \15/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; [apply MON0|].
  intros. set (rr e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 := exists n, rclo clo n r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14).
  assert (rr x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) by (exists 0; apply PR); clear PR.
  cut (forall n, rclo clo n r <15= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 H; pcofix CIH; intros.
    unfold rr in *; destruct H0.
    pfold. eapply gf_mon.
    - apply X. apply H.
    - intros. right. apply CIH. exists (S x). apply PR.
  }
  induction n; intros.
  - eapply gf_mon.
    + clear RESPECTFUL0. eapply PFIX, PR.
    + intros. right. eapply PR0.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H0|]. intros. left. apply PR.
    + eapply gf_mon; [eapply RESPECTFUL0; [|apply IHn|]|]; intros.
      * left; apply PR.
      * apply H0.
      * right; apply PR.
Qed.

Lemma respectful15_compose
      clo0 clo1
      (RES0: respectful15 clo0)
      (RES1: respectful15 clo1):
  respectful15 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; [apply IN|].
    intros. eapply MON1; [apply PR|apply LE].
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; [apply PR0|apply LE].
    + intros. eapply RESPECTFUL1; [apply LE| apply GF| apply PR0].
Qed.

Lemma grespectful15_mon: monotone15 gres15.
Proof.
  red. intros.
  destruct IN; destruct RES; exists clo; [|eapply MON0; [eapply CLO| eapply LE]].
  constructor; [eapply MON0|].
  intros. eapply RESPECTFUL0; [apply LE0|apply GF|apply PR].
Qed.

Lemma grespectful15_respectful15: respectful15 gres15.
Proof.
  econstructor; [apply grespectful15_mon|intros].
  destruct PR; destruct RES; eapply gf_mon with (r:=clo r).
  eapply RESPECTFUL0; [apply LE|apply GF|apply CLO].
  intros. econstructor; [constructor; [apply MON0|apply RESPECTFUL0]|apply PR].
Qed.

Lemma gfgres15_mon: monotone15 (compose gf gres15).
Proof.
  destruct grespectful15_respectful15.
  unfold monotone15. intros. eapply gf_mon; [eapply IN|].
  intros. eapply MON0;[apply PR|apply LE].
Qed.
Hint Resolve gfgres15_mon : paco.

Lemma grespectful15_greatest: forall clo (RES: respectful15 clo), clo <16= gres15.
Proof. intros. econstructor;[apply RES|apply PR]. Qed.

Lemma grespectful15_incl: forall r, r <15= gres15 r.
Proof.
  intros; eexists (fun x => x).
  - econstructor.
    + red; intros; apply LE, IN.
    + intros; apply GF, PR0.
  - apply PR.
Qed.
Hint Resolve grespectful15_incl.

Lemma grespectful15_compose: forall clo (RES: respectful15 clo) r,
    clo (gres15 r) <15= gres15 r.
Proof.
  intros; eapply grespectful15_greatest with (clo := compose clo gres15); [|apply PR].
  apply respectful15_compose; [apply RES|apply grespectful15_respectful15].
Qed.

Lemma grespectful15_incl_rev: forall r,
    gres15 (paco15 (compose gf gres15) r) <15= paco15 (compose gf gres15) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful15_compose, grespectful15_respectful15.
  destruct grespectful15_respectful15; eapply RESPECTFUL0, PR; intros; [apply grespectful15_incl; right; apply CIH, grespectful15_incl, PR0|].
  _punfold PR0; [|apply gfgres15_mon].
  eapply gfgres15_mon; [apply PR0|].
  intros; destruct PR1.
  - left. eapply paco15_mon; [apply H| apply CIH0].
  - right. eapply CIH0, H.
Qed.

Inductive rclo15 clo (r: rel): rel :=
| rclo15_incl
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14):
    @rclo15 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
| rclo15_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
    (R': r' <15= rclo15 clo r)
    (CLOR':clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14):
    @rclo15 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
| rclo15_gf
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
    (R': r' <15= rclo15 clo r)
    (CLOR':@gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14):
    @rclo15 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
.
Lemma rclo15_mon clo:
  monotone15 (rclo15 clo).
Proof.
  repeat intro. induction IN.
  - econstructor 1. apply LE, R.
  - econstructor 2; [intros; eapply H, PR| eapply CLOR'].
  - econstructor 3; [intros; eapply H, PR| eapply CLOR'].
Qed.
Hint Resolve rclo15_mon: paco.

Lemma rclo15_base
      clo
      (MON: monotone15 clo):
  clo <16= rclo15 clo.
Proof.
  intros. econstructor 2; [intros; apply PR0|].
  eapply MON; [apply PR|intros; constructor; apply PR0].
Qed.

Lemma rclo15_step
      (clo: rel -> rel) r:
  clo (rclo15 clo r) <15= rclo15 clo r.
Proof.
  intros. econstructor 2; [intros; apply PR0|apply PR].
Qed.

Lemma rclo15_rclo15
      clo r
      (MON: monotone15 clo):
  rclo15 clo (rclo15 clo r) <15= rclo15 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
Qed.

Structure weak_respectful15 (clo: rel -> rel) : Prop :=
  weak_respectful15_intro {
      WEAK_MON: monotone15 clo;
      WEAK_RESPECTFUL:
        forall l r (LE: l <15= r) (GF: l <15= gf r),
          clo l <15= gf (rclo15 clo r);
    }.
Hint Constructors weak_respectful15.

Lemma weak_respectful15_respectful15
      clo (RES: weak_respectful15 clo):
  respectful15 (rclo15 clo).
Proof.
  inversion RES. econstructor; [eapply rclo15_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply GF, R|]. intros.
    apply rclo15_incl. apply PR.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo15_mon; [apply R', PR|apply LE].
    + intros. apply rclo15_rclo15;[apply WEAK_MON0|apply PR].
  - eapply gf_mon; [apply CLOR'|].
    intros. eapply rclo15_mon; [apply R', PR| apply LE].
Qed.

Lemma upto15_init:
  paco15 (compose gf gres15) bot15 <15= paco15 gf bot15.
Proof.
  apply sound15_is_gf.
  apply respectful15_is_sound15.
  apply grespectful15_respectful15.
Qed.

Lemma upto15_final:
  paco15 gf <16= paco15 (compose gf gres15).
Proof.
  pcofix CIH. intros. _punfold PR; [|apply gf_mon]. pfold.
  eapply gf_mon; [|apply grespectful15_incl].
  eapply gf_mon; [apply PR|]. intros. right.
  inversion PR0; [apply CIH, H | apply CIH0, H].
Qed.

Lemma upto15_step
      r clo (RES: weak_respectful15 clo):
  clo (paco15 (compose gf gres15) r) <15= paco15 (compose gf gres15) r.
Proof.
  intros. apply grespectful15_incl_rev.
  assert (RES' := weak_respectful15_respectful15 RES).
  eapply grespectful15_greatest; [apply RES'|].
  eapply rclo15_base; [apply RES|].
  inversion RES. apply PR.
Qed.

Lemma upto15_step_under
      r clo (RES: weak_respectful15 clo):
  clo (gres15 r) <15= gres15 r.
Proof.
  intros. apply weak_respectful15_respectful15 in RES.
  eapply grespectful15_compose; [apply RES|].
  econstructor 2; [intros; constructor 1; apply PR0 | apply PR].
Qed.

End Respectful15.

Lemma grespectful15_impl T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 (gf gf': rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14
    (PR: gres15 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)
    (EQ: forall r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 <-> gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14):
  gres15 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.
Proof.
  intros. destruct PR. econstructor; [|apply CLO].
  destruct RES. econstructor; [apply MON0|].
  intros. rewrite <-EQ. eapply RESPECTFUL0; [apply LE| |apply PR].
  intros. rewrite EQ. apply GF, PR0.
Qed.

Lemma grespectful15_iff T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 (gf gf': rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14
    (EQ: forall r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 <-> gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14):
  gres15 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 <-> gres15 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.
Proof.
  split; intros.
  - eapply grespectful15_impl; [apply H | apply EQ].
  - eapply grespectful15_impl; [apply H | symmetry; apply EQ].
Qed.

Hint Constructors sound15.
Hint Constructors respectful15.
Hint Constructors gres15.
Hint Resolve gfclo15_mon : paco.
Hint Resolve gfgres15_mon : paco.
Hint Resolve grespectful15_incl.
Hint Resolve rclo15_mon: paco.
Hint Constructors weak_respectful15.

Ltac pupto15_init := eapply upto15_init; [eauto with paco|].
Ltac pupto15_final := first [eapply upto15_final; [eauto with paco|] | eapply grespectful15_incl].
Ltac pupto15 H := first [eapply upto15_step|eapply upto15_step_under]; [|eapply H|]; [eauto with paco|].

