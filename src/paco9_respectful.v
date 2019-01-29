Require Import paco9.
Require Export Program.
Set Implicit Arguments.

Section Respectful9.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.

Local Notation rel := (rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone9 gf.

Inductive sound9 (clo: rel -> rel): Prop :=
| sound9_intro
    (MON: monotone9 clo)
    (SOUND:
       forall r (PFIX: r <9= gf (clo r)),
         r <9= paco9 gf bot9)
.
Hint Constructors sound9.

Structure respectful9 (clo: rel -> rel) : Prop :=
  respectful9_intro {
      MON: monotone9 clo;
      RESPECTFUL:
        forall l r (LE: l <9= r) (GF: l <9= gf r),
          clo l <9= gf (clo r);
    }.
Hint Constructors respectful9.

Inductive gres9 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 : Prop :=
| gres9_intro
    clo
    (RES: respectful9 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8)
.
Hint Constructors gres9.
Lemma gfclo9_mon: forall clo, sound9 clo -> monotone9 (compose gf clo).
Proof. intros; destruct H; eauto using gf_mon. Qed.
Hint Resolve gfclo9_mon : paco.

Lemma sound9_is_gf: forall clo (UPTO: sound9 clo),
    paco9 (compose gf clo) bot9 <9= paco9 gf bot9.
Proof.
  intros. punfold PR. edestruct UPTO.
  eapply (SOUND (paco9 (compose gf clo) bot9)); [|eauto].
  intros. punfold PR0.
  eapply (gfclo9_mon UPTO); eauto. intros. destruct PR1; eauto. contradiction.
Qed.

Lemma respectful9_is_sound9: respectful9 <1= sound9.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \9/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; eauto.
  intros. set (rr e0 e1 e2 e3 e4 e5 e6 e7 e8 := exists n, rclo clo n r e0 e1 e2 e3 e4 e5 e6 e7 e8).
  assert (rr x0 x1 x2 x3 x4 x5 x6 x7 x8) by (exists 0; eauto); clear PR.
  cut (forall n, rclo clo n r <9= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 H; pcofix CIH; intros.
    unfold rr in *; destruct H0; eauto 10 using gf_mon. }
  induction n; intros; [simpl; eauto using gf_mon|].
  simpl in *; destruct PR; [eauto using gf_mon|].
  eapply gf_mon; [eapply RESPECTFUL0; [|apply IHn|]|]; instantiate; simpl; eauto.
Qed.

Lemma respectful9_compose
      clo0 clo1
      (RES0: respectful9 clo0)
      (RES1: respectful9 clo1):
  respectful9 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; eauto.
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; eauto.
    + intros. eapply RESPECTFUL1; eauto.
Qed.

Lemma grespectful9_respectful9: respectful9 gres9.
Proof.
  econstructor; repeat intro.
  - destruct IN; destruct RES; exists clo; eauto.
  - destruct PR; destruct RES; eapply gf_mon with (r:=clo r); eauto.
Qed.

Lemma gfgres9_mon: monotone9 (compose gf gres9).
Proof.
  destruct grespectful9_respectful9; eauto using gf_mon.
Qed.
Hint Resolve gfgres9_mon : paco.

Lemma grespectful9_greatest: forall clo (RES: respectful9 clo), clo <10= gres9.
Proof. eauto. Qed.

Lemma grespectful9_incl: forall r, r <9= gres9 r.
Proof.
  intros; eexists (fun x => x); eauto.
Qed.
Hint Resolve grespectful9_incl.

Lemma grespectful9_compose: forall clo (RES: respectful9 clo) r,
    clo (gres9 r) <9= gres9 r.
Proof.
  intros; eapply grespectful9_greatest with (clo := compose clo gres9);
    eauto using respectful9_compose, grespectful9_respectful9.
Qed.

Lemma grespectful9_incl_rev: forall r,
    gres9 (paco9 (compose gf gres9) r) <9= paco9 (compose gf gres9) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful9_compose, grespectful9_respectful9.
  destruct grespectful9_respectful9; eapply RESPECTFUL0, PR; intros; [apply grespectful9_incl; eauto|].
  punfold PR0.
  eapply gfgres9_mon; eauto; intros; destruct PR1; eauto.
Qed.

Inductive rclo9 clo (r: rel): rel :=
| rclo9_incl
    e0 e1 e2 e3 e4 e5 e6 e7 e8
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8):
    @rclo9 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8
| rclo9_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8
    (R': r' <9= rclo9 clo r)
    (CLOR':clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8):
    @rclo9 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8
| rclo9_gf
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8
    (R': r' <9= rclo9 clo r)
    (CLOR':@gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8):
    @rclo9 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8
.
Lemma rclo9_mon clo:
  monotone9 (rclo9 clo).
Proof.
  repeat intro. induction IN; eauto using rclo9.
Qed.
Hint Resolve rclo9_mon: paco.

Lemma rclo9_base
      clo
      (MON: monotone9 clo):
  clo <10= rclo9 clo.
Proof.
  simpl. intros. econstructor 2; eauto.
  eapply MON; eauto using rclo9.
Qed.

Lemma rclo9_step
      (clo: rel -> rel) r:
  clo (rclo9 clo r) <9= rclo9 clo r.
Proof.
  intros. econstructor 2; eauto.
Qed.

Lemma rclo9_rclo9
      clo r
      (MON: monotone9 clo):
  rclo9 clo (rclo9 clo r) <9= rclo9 clo r.
Proof.
  intros. induction PR; eauto using rclo9.
Qed.

Structure weak_respectful9 (clo: rel -> rel) : Prop :=
  weak_respectful9_intro {
      WEAK_MON: monotone9 clo;
      WEAK_RESPECTFUL:
        forall l r (LE: l <9= r) (GF: l <9= gf r),
          clo l <9= gf (rclo9 clo r);
    }.
Hint Constructors weak_respectful9.

Lemma weak_respectful9_respectful9
      clo (RES: weak_respectful9 clo):
  respectful9 (rclo9 clo).
Proof.
  inversion RES. econstructor; eauto with paco. intros.
  induction PR; intros.
  - eapply gf_mon; eauto. intros.
    apply rclo9_incl. auto.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo9_mon; eauto.
    + intros. apply rclo9_rclo9; auto.
  - eapply gf_mon; eauto using rclo9.
Qed.

Lemma upto9_init:
  paco9 (compose gf gres9) bot9 <9= paco9 gf bot9.
Proof.
  apply sound9_is_gf; eauto.
  apply respectful9_is_sound9.
  apply grespectful9_respectful9.
Qed.

Lemma upto9_final:
  paco9 gf <10= paco9 (compose gf gres9).
Proof.
  pcofix CIH. intros. punfold PR. pfold.
  eapply gf_mon; [|apply grespectful9_incl].
  eapply gf_mon; [eauto|]. intros. right. inversion PR0; auto.
Qed.

Lemma upto9_step
      r clo (RES: weak_respectful9 clo):
  clo (paco9 (compose gf gres9) r) <9= paco9 (compose gf gres9) r.
Proof.
  intros. apply grespectful9_incl_rev.
  assert (RES' := weak_respectful9_respectful9 RES).
  eapply grespectful9_greatest. eauto.
  eapply rclo9_base; eauto.
  inversion RES. auto.
Qed.

Lemma upto9_step_under
      r clo (RES: weak_respectful9 clo):
  clo (gres9 r) <9= gres9 r.
Proof.
  intros. apply weak_respectful9_respectful9 in RES; eauto.
  eapply grespectful9_compose; eauto. eauto using rclo9.
Qed.

End Respectful9.

Hint Constructors sound9.
Hint Constructors respectful9.
Hint Constructors gres9.
Hint Resolve gfclo9_mon : paco.
Hint Resolve gfgres9_mon : paco.
Hint Resolve grespectful9_incl.
Hint Resolve rclo9_mon: paco.
Hint Constructors weak_respectful9.

Ltac pupto9_init := eapply upto9_init; eauto with paco.
Ltac pupto9_final := first [eapply upto9_final; eauto with paco | eapply grespectful9_incl].
Ltac pupto9 H := first [eapply upto9_step|eapply upto9_step_under]; [|eapply H|]; eauto with paco.

