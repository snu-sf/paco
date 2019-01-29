Require Import paco16.
Require Export Program.
Set Implicit Arguments.

Section Respectful16.

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
Variable T15 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (x14: @T14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13), Type.

Local Notation rel := (rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone16 gf.

Inductive sound16 (clo: rel -> rel): Prop :=
| sound16_intro
    (MON: monotone16 clo)
    (SOUND:
       forall r (PFIX: r <16= gf (clo r)),
         r <16= paco16 gf bot16)
.
Hint Constructors sound16.

Structure respectful16 (clo: rel -> rel) : Prop :=
  respectful16_intro {
      MON: monotone16 clo;
      RESPECTFUL:
        forall l r (LE: l <16= r) (GF: l <16= gf r),
          clo l <16= gf (clo r);
    }.
Hint Constructors respectful16.

Inductive gres16 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 : Prop :=
| gres16_intro
    clo
    (RES: respectful16 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15)
.
Hint Constructors gres16.
Lemma gfclo16_mon: forall clo, sound16 clo -> monotone16 (compose gf clo).
Proof. intros; destruct H; eauto using gf_mon. Qed.
Hint Resolve gfclo16_mon : paco.

Lemma sound16_is_gf: forall clo (UPTO: sound16 clo),
    paco16 (compose gf clo) bot16 <16= paco16 gf bot16.
Proof.
  intros. punfold PR. edestruct UPTO.
  eapply (SOUND (paco16 (compose gf clo) bot16)); [|eauto].
  intros. punfold PR0.
  eapply (gfclo16_mon UPTO); eauto. intros. destruct PR1; eauto. contradiction.
Qed.

Lemma respectful16_is_sound16: respectful16 <1= sound16.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \16/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; eauto.
  intros. set (rr e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 := exists n, rclo clo n r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15).
  assert (rr x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) by (exists 0; eauto); clear PR.
  cut (forall n, rclo clo n r <16= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 H; pcofix CIH; intros.
    unfold rr in *; destruct H0; eauto 10 using gf_mon. }
  induction n; intros; [simpl; eauto using gf_mon|].
  simpl in *; destruct PR; [eauto using gf_mon|].
  eapply gf_mon; [eapply RESPECTFUL0; [|apply IHn|]|]; instantiate; simpl; eauto.
Qed.

Lemma respectful16_compose
      clo0 clo1
      (RES0: respectful16 clo0)
      (RES1: respectful16 clo1):
  respectful16 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; eauto.
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; eauto.
    + intros. eapply RESPECTFUL1; eauto.
Qed.

Lemma grespectful16_respectful16: respectful16 gres16.
Proof.
  econstructor; repeat intro.
  - destruct IN; destruct RES; exists clo; eauto.
  - destruct PR; destruct RES; eapply gf_mon with (r:=clo r); eauto.
Qed.

Lemma gfgres16_mon: monotone16 (compose gf gres16).
Proof.
  destruct grespectful16_respectful16; eauto using gf_mon.
Qed.
Hint Resolve gfgres16_mon : paco.

Lemma grespectful16_greatest: forall clo (RES: respectful16 clo), clo <17= gres16.
Proof. eauto. Qed.

Lemma grespectful16_incl: forall r, r <16= gres16 r.
Proof.
  intros; eexists (fun x => x); eauto.
Qed.
Hint Resolve grespectful16_incl.

Lemma grespectful16_compose: forall clo (RES: respectful16 clo) r,
    clo (gres16 r) <16= gres16 r.
Proof.
  intros; eapply grespectful16_greatest with (clo := compose clo gres16);
    eauto using respectful16_compose, grespectful16_respectful16.
Qed.

Lemma grespectful16_incl_rev: forall r,
    gres16 (paco16 (compose gf gres16) r) <16= paco16 (compose gf gres16) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful16_compose, grespectful16_respectful16.
  destruct grespectful16_respectful16; eapply RESPECTFUL0, PR; intros; [apply grespectful16_incl; eauto|].
  punfold PR0.
  eapply gfgres16_mon; eauto; intros; destruct PR1; eauto.
Qed.

Inductive rclo16 clo (r: rel): rel :=
| rclo16_incl
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15):
    @rclo16 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
| rclo16_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
    (R': r' <16= rclo16 clo r)
    (CLOR':clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15):
    @rclo16 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
| rclo16_gf
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
    (R': r' <16= rclo16 clo r)
    (CLOR':@gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15):
    @rclo16 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
.
Lemma rclo16_mon clo:
  monotone16 (rclo16 clo).
Proof.
  repeat intro. induction IN; eauto using rclo16.
Qed.
Hint Resolve rclo16_mon: paco.

Lemma rclo16_base
      clo
      (MON: monotone16 clo):
  clo <17= rclo16 clo.
Proof.
  simpl. intros. econstructor 2; eauto.
  eapply MON; eauto using rclo16.
Qed.

Lemma rclo16_step
      (clo: rel -> rel) r:
  clo (rclo16 clo r) <16= rclo16 clo r.
Proof.
  intros. econstructor 2; eauto.
Qed.

Lemma rclo16_rclo16
      clo r
      (MON: monotone16 clo):
  rclo16 clo (rclo16 clo r) <16= rclo16 clo r.
Proof.
  intros. induction PR; eauto using rclo16.
Qed.

Structure weak_respectful16 (clo: rel -> rel) : Prop :=
  weak_respectful16_intro {
      WEAK_MON: monotone16 clo;
      WEAK_RESPECTFUL:
        forall l r (LE: l <16= r) (GF: l <16= gf r),
          clo l <16= gf (rclo16 clo r);
    }.
Hint Constructors weak_respectful16.

Lemma weak_respectful16_respectful16
      clo (RES: weak_respectful16 clo):
  respectful16 (rclo16 clo).
Proof.
  inversion RES. econstructor; eauto with paco. intros.
  induction PR; intros.
  - eapply gf_mon; eauto. intros.
    apply rclo16_incl. auto.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo16_mon; eauto.
    + intros. apply rclo16_rclo16; auto.
  - eapply gf_mon; eauto using rclo16.
Qed.

Lemma upto16_init:
  paco16 (compose gf gres16) bot16 <16= paco16 gf bot16.
Proof.
  apply sound16_is_gf; eauto.
  apply respectful16_is_sound16.
  apply grespectful16_respectful16.
Qed.

Lemma upto16_final:
  paco16 gf <17= paco16 (compose gf gres16).
Proof.
  pcofix CIH. intros. punfold PR. pfold.
  eapply gf_mon; [|apply grespectful16_incl].
  eapply gf_mon; [eauto|]. intros. right. inversion PR0; auto.
Qed.

Lemma upto16_step
      r clo (RES: weak_respectful16 clo):
  clo (paco16 (compose gf gres16) r) <16= paco16 (compose gf gres16) r.
Proof.
  intros. apply grespectful16_incl_rev.
  assert (RES' := weak_respectful16_respectful16 RES).
  eapply grespectful16_greatest. eauto.
  eapply rclo16_base; eauto.
  inversion RES. auto.
Qed.

Lemma upto16_step_under
      r clo (RES: weak_respectful16 clo):
  clo (gres16 r) <16= gres16 r.
Proof.
  intros. apply weak_respectful16_respectful16 in RES; eauto.
  eapply grespectful16_compose; eauto. eauto using rclo16.
Qed.

End Respectful16.

Hint Constructors sound16.
Hint Constructors respectful16.
Hint Constructors gres16.
Hint Resolve gfclo16_mon : paco.
Hint Resolve gfgres16_mon : paco.
Hint Resolve grespectful16_incl.
Hint Resolve rclo16_mon: paco.
Hint Constructors weak_respectful16.

Ltac pupto16_init := eapply upto16_init; eauto with paco.
Ltac pupto16_final := first [eapply upto16_final; eauto with paco | eapply grespectful16_incl].
Ltac pupto16 H := first [eapply upto16_step|eapply upto16_step_under]; [|eapply H|]; eauto with paco.

