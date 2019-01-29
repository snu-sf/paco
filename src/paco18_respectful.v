Require Import paco18.
Require Export Program.
Set Implicit Arguments.

Section Respectful18.

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
Variable T17 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (x14: @T14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) (x15: @T15 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) (x16: @T16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15), Type.

Local Notation rel := (rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone18 gf.

Inductive sound18 (clo: rel -> rel): Prop :=
| sound18_intro
    (MON: monotone18 clo)
    (SOUND:
       forall r (PFIX: r <18= gf (clo r)),
         r <18= paco18 gf bot18)
.
Hint Constructors sound18.

Structure respectful18 (clo: rel -> rel) : Prop :=
  respectful18_intro {
      MON: monotone18 clo;
      RESPECTFUL:
        forall l r (LE: l <18= r) (GF: l <18= gf r),
          clo l <18= gf (clo r);
    }.
Hint Constructors respectful18.

Inductive gres18 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 : Prop :=
| gres18_intro
    clo
    (RES: respectful18 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17)
.
Hint Constructors gres18.
Lemma gfclo18_mon: forall clo, sound18 clo -> monotone18 (compose gf clo).
Proof. intros; destruct H; eauto using gf_mon. Qed.
Hint Resolve gfclo18_mon : paco.

Lemma sound18_is_gf: forall clo (UPTO: sound18 clo),
    paco18 (compose gf clo) bot18 <18= paco18 gf bot18.
Proof.
  intros. punfold PR. edestruct UPTO.
  eapply (SOUND (paco18 (compose gf clo) bot18)); [|eauto].
  intros. punfold PR0.
  eapply (gfclo18_mon UPTO); eauto. intros. destruct PR1; eauto. contradiction.
Qed.

Lemma respectful18_is_sound18: respectful18 <1= sound18.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \18/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; eauto.
  intros. set (rr e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 := exists n, rclo clo n r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17).
  assert (rr x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) by (exists 0; eauto); clear PR.
  cut (forall n, rclo clo n r <18= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 H; pcofix CIH; intros.
    unfold rr in *; destruct H0; eauto 10 using gf_mon. }
  induction n; intros; [simpl; eauto using gf_mon|].
  simpl in *; destruct PR; [eauto using gf_mon|].
  eapply gf_mon; [eapply RESPECTFUL0; [|apply IHn|]|]; instantiate; simpl; eauto.
Qed.

Lemma respectful18_compose
      clo0 clo1
      (RES0: respectful18 clo0)
      (RES1: respectful18 clo1):
  respectful18 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; eauto.
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; eauto.
    + intros. eapply RESPECTFUL1; eauto.
Qed.

Lemma grespectful18_respectful18: respectful18 gres18.
Proof.
  econstructor; repeat intro.
  - destruct IN; destruct RES; exists clo; eauto.
  - destruct PR; destruct RES; eapply gf_mon with (r:=clo r); eauto.
Qed.

Lemma gfgres18_mon: monotone18 (compose gf gres18).
Proof.
  destruct grespectful18_respectful18; eauto using gf_mon.
Qed.
Hint Resolve gfgres18_mon : paco.

Lemma grespectful18_greatest: forall clo (RES: respectful18 clo), clo <19= gres18.
Proof. eauto. Qed.

Lemma grespectful18_incl: forall r, r <18= gres18 r.
Proof.
  intros; eexists (fun x => x); eauto.
Qed.
Hint Resolve grespectful18_incl.

Lemma grespectful18_compose: forall clo (RES: respectful18 clo) r,
    clo (gres18 r) <18= gres18 r.
Proof.
  intros; eapply grespectful18_greatest with (clo := compose clo gres18);
    eauto using respectful18_compose, grespectful18_respectful18.
Qed.

Lemma grespectful18_incl_rev: forall r,
    gres18 (paco18 (compose gf gres18) r) <18= paco18 (compose gf gres18) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful18_compose, grespectful18_respectful18.
  destruct grespectful18_respectful18; eapply RESPECTFUL0, PR; intros; [apply grespectful18_incl; eauto|].
  punfold PR0.
  eapply gfgres18_mon; eauto; intros; destruct PR1; eauto.
Qed.

Inductive rclo18 clo (r: rel): rel :=
| rclo18_incl
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17):
    @rclo18 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
| rclo18_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
    (R': r' <18= rclo18 clo r)
    (CLOR':clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17):
    @rclo18 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
| rclo18_gf
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
    (R': r' <18= rclo18 clo r)
    (CLOR':@gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17):
    @rclo18 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
.
Lemma rclo18_mon clo:
  monotone18 (rclo18 clo).
Proof.
  repeat intro. induction IN; eauto using rclo18.
Qed.
Hint Resolve rclo18_mon: paco.

Lemma rclo18_base
      clo
      (MON: monotone18 clo):
  clo <19= rclo18 clo.
Proof.
  simpl. intros. econstructor 2; eauto.
  eapply MON; eauto using rclo18.
Qed.

Lemma rclo18_step
      (clo: rel -> rel) r:
  clo (rclo18 clo r) <18= rclo18 clo r.
Proof.
  intros. econstructor 2; eauto.
Qed.

Lemma rclo18_rclo18
      clo r
      (MON: monotone18 clo):
  rclo18 clo (rclo18 clo r) <18= rclo18 clo r.
Proof.
  intros. induction PR; eauto using rclo18.
Qed.

Structure weak_respectful18 (clo: rel -> rel) : Prop :=
  weak_respectful18_intro {
      WEAK_MON: monotone18 clo;
      WEAK_RESPECTFUL:
        forall l r (LE: l <18= r) (GF: l <18= gf r),
          clo l <18= gf (rclo18 clo r);
    }.
Hint Constructors weak_respectful18.

Lemma weak_respectful18_respectful18
      clo (RES: weak_respectful18 clo):
  respectful18 (rclo18 clo).
Proof.
  inversion RES. econstructor; eauto with paco. intros.
  induction PR; intros.
  - eapply gf_mon; eauto. intros.
    apply rclo18_incl. auto.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo18_mon; eauto.
    + intros. apply rclo18_rclo18; auto.
  - eapply gf_mon; eauto using rclo18.
Qed.

Lemma upto18_init:
  paco18 (compose gf gres18) bot18 <18= paco18 gf bot18.
Proof.
  apply sound18_is_gf; eauto.
  apply respectful18_is_sound18.
  apply grespectful18_respectful18.
Qed.

Lemma upto18_final:
  paco18 gf <19= paco18 (compose gf gres18).
Proof.
  pcofix CIH. intros. punfold PR. pfold.
  eapply gf_mon; [|apply grespectful18_incl].
  eapply gf_mon; [eauto|]. intros. right. inversion PR0; auto.
Qed.

Lemma upto18_step
      r clo (RES: weak_respectful18 clo):
  clo (paco18 (compose gf gres18) r) <18= paco18 (compose gf gres18) r.
Proof.
  intros. apply grespectful18_incl_rev.
  assert (RES' := weak_respectful18_respectful18 RES).
  eapply grespectful18_greatest. eauto.
  eapply rclo18_base; eauto.
  inversion RES. auto.
Qed.

Lemma upto18_step_under
      r clo (RES: weak_respectful18 clo):
  clo (gres18 r) <18= gres18 r.
Proof.
  intros. apply weak_respectful18_respectful18 in RES; eauto.
  eapply grespectful18_compose; eauto. eauto using rclo18.
Qed.

End Respectful18.

Hint Constructors sound18.
Hint Constructors respectful18.
Hint Constructors gres18.
Hint Resolve gfclo18_mon : paco.
Hint Resolve gfgres18_mon : paco.
Hint Resolve grespectful18_incl.
Hint Resolve rclo18_mon: paco.
Hint Constructors weak_respectful18.

Ltac pupto18_init := eapply upto18_init; eauto with paco.
Ltac pupto18_final := first [eapply upto18_final; eauto with paco | eapply grespectful18_incl].
Ltac pupto18 H := first [eapply upto18_step|eapply upto18_step_under]; [|eapply H|]; eauto with paco.

