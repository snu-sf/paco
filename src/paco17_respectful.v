Require Import paco17.
Require Export Program.
Set Implicit Arguments.

Section Respectful17.

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
Variable T16 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (x14: @T14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) (x15: @T15 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14), Type.

Local Notation rel := (rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone17 gf.

Inductive sound17 (clo: rel -> rel): Prop :=
| sound17_intro
    (MON: monotone17 clo)
    (SOUND:
       forall r (PFIX: r <17= gf (clo r)),
         r <17= paco17 gf bot17)
.
Hint Constructors sound17.

Structure respectful17 (clo: rel -> rel) : Prop :=
  respectful17_intro {
      MON: monotone17 clo;
      RESPECTFUL:
        forall l r (LE: l <17= r) (GF: l <17= gf r),
          clo l <17= gf (clo r);
    }.
Hint Constructors respectful17.

Inductive gres17 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 : Prop :=
| gres17_intro
    clo
    (RES: respectful17 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16)
.
Hint Constructors gres17.
Lemma gfclo17_mon: forall clo, sound17 clo -> monotone17 (compose gf clo).
Proof. intros; destruct H; eauto using gf_mon. Qed.
Hint Resolve gfclo17_mon : paco.

Lemma sound17_is_gf: forall clo (UPTO: sound17 clo),
    paco17 (compose gf clo) bot17 <17= paco17 gf bot17.
Proof.
  intros. punfold PR. edestruct UPTO.
  eapply (SOUND (paco17 (compose gf clo) bot17)); [|eauto].
  intros. punfold PR0.
  eapply (gfclo17_mon UPTO); eauto. intros. destruct PR1; eauto. contradiction.
Qed.

Lemma respectful17_is_sound17: respectful17 <1= sound17.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \17/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; eauto.
  intros. set (rr e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 := exists n, rclo clo n r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16).
  assert (rr x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) by (exists 0; eauto); clear PR.
  cut (forall n, rclo clo n r <17= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 H; pcofix CIH; intros.
    unfold rr in *; destruct H0; eauto 10 using gf_mon. }
  induction n; intros; [simpl; eauto using gf_mon|].
  simpl in *; destruct PR; [eauto using gf_mon|].
  eapply gf_mon; [eapply RESPECTFUL0; [|apply IHn|]|]; instantiate; simpl; eauto.
Qed.

Lemma respectful17_compose
      clo0 clo1
      (RES0: respectful17 clo0)
      (RES1: respectful17 clo1):
  respectful17 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; eauto.
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; eauto.
    + intros. eapply RESPECTFUL1; eauto.
Qed.

Lemma grespectful17_respectful17: respectful17 gres17.
Proof.
  econstructor; repeat intro.
  - destruct IN; destruct RES; exists clo; eauto.
  - destruct PR; destruct RES; eapply gf_mon with (r:=clo r); eauto.
Qed.

Lemma gfgres17_mon: monotone17 (compose gf gres17).
Proof.
  destruct grespectful17_respectful17; eauto using gf_mon.
Qed.
Hint Resolve gfgres17_mon : paco.

Lemma grespectful17_greatest: forall clo (RES: respectful17 clo), clo <18= gres17.
Proof. eauto. Qed.

Lemma grespectful17_incl: forall r, r <17= gres17 r.
Proof.
  intros; eexists (fun x => x); eauto.
Qed.
Hint Resolve grespectful17_incl.

Lemma grespectful17_compose: forall clo (RES: respectful17 clo) r,
    clo (gres17 r) <17= gres17 r.
Proof.
  intros; eapply grespectful17_greatest with (clo := compose clo gres17);
    eauto using respectful17_compose, grespectful17_respectful17.
Qed.

Lemma grespectful17_incl_rev: forall r,
    gres17 (paco17 (compose gf gres17) r) <17= paco17 (compose gf gres17) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful17_compose, grespectful17_respectful17.
  destruct grespectful17_respectful17; eapply RESPECTFUL0, PR; intros; [apply grespectful17_incl; eauto|].
  punfold PR0.
  eapply gfgres17_mon; eauto; intros; destruct PR1; eauto.
Qed.

Inductive rclo17 clo (r: rel): rel :=
| rclo17_incl
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16):
    @rclo17 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16
| rclo17_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16
    (R': r' <17= rclo17 clo r)
    (CLOR':clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16):
    @rclo17 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16
| rclo17_gf
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16
    (R': r' <17= rclo17 clo r)
    (CLOR':@gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16):
    @rclo17 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16
.
Lemma rclo17_mon clo:
  monotone17 (rclo17 clo).
Proof.
  repeat intro. induction IN; eauto using rclo17.
Qed.
Hint Resolve rclo17_mon: paco.

Lemma rclo17_base
      clo
      (MON: monotone17 clo):
  clo <18= rclo17 clo.
Proof.
  simpl. intros. econstructor 2; eauto.
  eapply MON; eauto using rclo17.
Qed.

Lemma rclo17_step
      (clo: rel -> rel) r:
  clo (rclo17 clo r) <17= rclo17 clo r.
Proof.
  intros. econstructor 2; eauto.
Qed.

Lemma rclo17_rclo17
      clo r
      (MON: monotone17 clo):
  rclo17 clo (rclo17 clo r) <17= rclo17 clo r.
Proof.
  intros. induction PR; eauto using rclo17.
Qed.

Structure weak_respectful17 (clo: rel -> rel) : Prop :=
  weak_respectful17_intro {
      WEAK_MON: monotone17 clo;
      WEAK_RESPECTFUL:
        forall l r (LE: l <17= r) (GF: l <17= gf r),
          clo l <17= gf (rclo17 clo r);
    }.
Hint Constructors weak_respectful17.

Lemma weak_respectful17_respectful17
      clo (RES: weak_respectful17 clo):
  respectful17 (rclo17 clo).
Proof.
  inversion RES. econstructor; eauto with paco. intros.
  induction PR; intros.
  - eapply gf_mon; eauto. intros.
    apply rclo17_incl. auto.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo17_mon; eauto.
    + intros. apply rclo17_rclo17; auto.
  - eapply gf_mon; eauto using rclo17.
Qed.

Lemma upto17_init:
  paco17 (compose gf gres17) bot17 <17= paco17 gf bot17.
Proof.
  apply sound17_is_gf; eauto.
  apply respectful17_is_sound17.
  apply grespectful17_respectful17.
Qed.

Lemma upto17_final:
  paco17 gf <18= paco17 (compose gf gres17).
Proof.
  pcofix CIH. intros. punfold PR. pfold.
  eapply gf_mon; [|apply grespectful17_incl].
  eapply gf_mon; [eauto|]. intros. right. inversion PR0; auto.
Qed.

Lemma upto17_step
      r clo (RES: weak_respectful17 clo):
  clo (paco17 (compose gf gres17) r) <17= paco17 (compose gf gres17) r.
Proof.
  intros. apply grespectful17_incl_rev.
  assert (RES' := weak_respectful17_respectful17 RES).
  eapply grespectful17_greatest. eauto.
  eapply rclo17_base; eauto.
  inversion RES. auto.
Qed.

Lemma upto17_step_under
      r clo (RES: weak_respectful17 clo):
  clo (gres17 r) <17= gres17 r.
Proof.
  intros. apply weak_respectful17_respectful17 in RES; eauto.
  eapply grespectful17_compose; eauto. eauto using rclo17.
Qed.

End Respectful17.

Hint Constructors sound17.
Hint Constructors respectful17.
Hint Constructors gres17.
Hint Resolve gfclo17_mon : paco.
Hint Resolve gfgres17_mon : paco.
Hint Resolve grespectful17_incl.
Hint Resolve rclo17_mon: paco.
Hint Constructors weak_respectful17.

Ltac pupto17_init := eapply upto17_init; eauto with paco.
Ltac pupto17_final := first [eapply upto17_final; eauto with paco | eapply grespectful17_incl].
Ltac pupto17 H := first [eapply upto17_step|eapply upto17_step_under]; [|eapply H|]; eauto with paco.

