Require Import paco13.
Require Export Program.
Set Implicit Arguments.

Section Respectful13.

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

Local Notation rel := (rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone13 gf.

Inductive sound13 (clo: rel -> rel): Prop :=
| sound13_intro
    (MON: monotone13 clo)
    (SOUND:
       forall r (PFIX: r <13= gf (clo r)),
         r <13= paco13 gf bot13)
.
Hint Constructors sound13.

Structure respectful13 (clo: rel -> rel) : Prop :=
  respectful13_intro {
      MON: monotone13 clo;
      RESPECTFUL:
        forall l r (LE: l <13= r) (GF: l <13= gf r),
          clo l <13= gf (clo r);
    }.
Hint Constructors respectful13.

Inductive gres13 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 : Prop :=
| gres13_intro
    clo
    (RES: respectful13 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12)
.
Hint Constructors gres13.
Lemma gfclo13_mon: forall clo, sound13 clo -> monotone13 (compose gf clo).
Proof. intros; destruct H; eauto using gf_mon. Qed.
Hint Resolve gfclo13_mon : paco.

Lemma sound13_is_gf: forall clo (UPTO: sound13 clo),
    paco13 (compose gf clo) bot13 <13= paco13 gf bot13.
Proof.
  intros. punfold PR. edestruct UPTO.
  eapply (SOUND (paco13 (compose gf clo) bot13)); [|eauto].
  intros. punfold PR0.
  eapply (gfclo13_mon UPTO); eauto. intros. destruct PR1; eauto. contradiction.
Qed.

Lemma respectful13_is_sound13: respectful13 <1= sound13.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \13/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; eauto.
  intros. set (rr e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 := exists n, rclo clo n r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12).
  assert (rr x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) by (exists 0; eauto); clear PR.
  cut (forall n, rclo clo n r <13= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 H; pcofix CIH; intros.
    unfold rr in *; destruct H0; eauto 10 using gf_mon. }
  induction n; intros; [simpl; eauto using gf_mon|].
  simpl in *; destruct PR; [eauto using gf_mon|].
  eapply gf_mon; [eapply RESPECTFUL0; [|apply IHn|]|]; instantiate; simpl; eauto.
Qed.

Lemma respectful13_compose
      clo0 clo1
      (RES0: respectful13 clo0)
      (RES1: respectful13 clo1):
  respectful13 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; eauto.
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; eauto.
    + intros. eapply RESPECTFUL1; eauto.
Qed.

Lemma grespectful13_respectful13: respectful13 gres13.
Proof.
  econstructor; repeat intro.
  - destruct IN; destruct RES; exists clo; eauto.
  - destruct PR; destruct RES; eapply gf_mon with (r:=clo r); eauto.
Qed.

Lemma gfgres13_mon: monotone13 (compose gf gres13).
Proof.
  destruct grespectful13_respectful13; eauto using gf_mon.
Qed.
Hint Resolve gfgres13_mon : paco.

Lemma grespectful13_greatest: forall clo (RES: respectful13 clo), clo <14= gres13.
Proof. eauto. Qed.

Lemma grespectful13_incl: forall r, r <13= gres13 r.
Proof.
  intros; eexists (fun x => x); eauto.
Qed.
Hint Resolve grespectful13_incl.

Lemma grespectful13_compose: forall clo (RES: respectful13 clo) r,
    clo (gres13 r) <13= gres13 r.
Proof.
  intros; eapply grespectful13_greatest with (clo := compose clo gres13);
    eauto using respectful13_compose, grespectful13_respectful13.
Qed.

Lemma grespectful13_incl_rev: forall r,
    gres13 (paco13 (compose gf gres13) r) <13= paco13 (compose gf gres13) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful13_compose, grespectful13_respectful13.
  destruct grespectful13_respectful13; eapply RESPECTFUL0, PR; intros; [apply grespectful13_incl; eauto|].
  punfold PR0.
  eapply gfgres13_mon; eauto; intros; destruct PR1; eauto.
Qed.

Inductive rclo13 clo (r: rel): rel :=
| rclo13_incl
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12):
    @rclo13 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
| rclo13_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
    (R': r' <13= rclo13 clo r)
    (CLOR':clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12):
    @rclo13 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
| rclo13_gf
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
    (R': r' <13= rclo13 clo r)
    (CLOR':@gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12):
    @rclo13 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
.
Lemma rclo13_mon clo:
  monotone13 (rclo13 clo).
Proof.
  repeat intro. induction IN; eauto using rclo13.
Qed.
Hint Resolve rclo13_mon: paco.

Lemma rclo13_base
      clo
      (MON: monotone13 clo):
  clo <14= rclo13 clo.
Proof.
  simpl. intros. econstructor 2; eauto.
  eapply MON; eauto using rclo13.
Qed.

Lemma rclo13_step
      (clo: rel -> rel) r:
  clo (rclo13 clo r) <13= rclo13 clo r.
Proof.
  intros. econstructor 2; eauto.
Qed.

Lemma rclo13_rclo13
      clo r
      (MON: monotone13 clo):
  rclo13 clo (rclo13 clo r) <13= rclo13 clo r.
Proof.
  intros. induction PR; eauto using rclo13.
Qed.

Structure weak_respectful13 (clo: rel -> rel) : Prop :=
  weak_respectful13_intro {
      WEAK_MON: monotone13 clo;
      WEAK_RESPECTFUL:
        forall l r (LE: l <13= r) (GF: l <13= gf r),
          clo l <13= gf (rclo13 clo r);
    }.
Hint Constructors weak_respectful13.

Lemma weak_respectful13_respectful13
      clo (RES: weak_respectful13 clo):
  respectful13 (rclo13 clo).
Proof.
  inversion RES. econstructor; eauto with paco. intros.
  induction PR; intros.
  - eapply gf_mon; eauto. intros.
    apply rclo13_incl. auto.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo13_mon; eauto.
    + intros. apply rclo13_rclo13; auto.
  - eapply gf_mon; eauto using rclo13.
Qed.

Lemma upto13_init:
  paco13 (compose gf gres13) bot13 <13= paco13 gf bot13.
Proof.
  apply sound13_is_gf; eauto.
  apply respectful13_is_sound13.
  apply grespectful13_respectful13.
Qed.

Lemma upto13_final:
  paco13 gf <14= paco13 (compose gf gres13).
Proof.
  pcofix CIH. intros. punfold PR. pfold.
  eapply gf_mon; [|apply grespectful13_incl].
  eapply gf_mon; [eauto|]. intros. right. inversion PR0; auto.
Qed.

Lemma upto13_step
      r clo (RES: weak_respectful13 clo):
  clo (paco13 (compose gf gres13) r) <13= paco13 (compose gf gres13) r.
Proof.
  intros. apply grespectful13_incl_rev.
  assert (RES' := weak_respectful13_respectful13 RES).
  eapply grespectful13_greatest. eauto.
  eapply rclo13_base; eauto.
  inversion RES. auto.
Qed.

Lemma upto13_step_under
      r clo (RES: weak_respectful13 clo):
  clo (gres13 r) <13= gres13 r.
Proof.
  intros. apply weak_respectful13_respectful13 in RES; eauto.
  eapply grespectful13_compose; eauto. eauto using rclo13.
Qed.

End Respectful13.

Hint Constructors sound13.
Hint Constructors respectful13.
Hint Constructors gres13.
Hint Resolve gfclo13_mon : paco.
Hint Resolve gfgres13_mon : paco.
Hint Resolve grespectful13_incl.
Hint Resolve rclo13_mon: paco.
Hint Constructors weak_respectful13.

Ltac pupto13_init := eapply upto13_init; eauto with paco.
Ltac pupto13_final := first [eapply upto13_final; eauto with paco | eapply grespectful13_incl].
Ltac pupto13 H := first [eapply upto13_step|eapply upto13_step_under]; [|eapply H|]; eauto with paco.

