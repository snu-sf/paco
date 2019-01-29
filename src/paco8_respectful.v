Require Import paco8.
Require Export Program.
Set Implicit Arguments.

Section Respectful8.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.

Local Notation rel := (rel8 T0 T1 T2 T3 T4 T5 T6 T7).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone8 gf.

Inductive sound8 (clo: rel -> rel): Prop :=
| sound8_intro
    (MON: monotone8 clo)
    (SOUND:
       forall r (PFIX: r <8= gf (clo r)),
         r <8= paco8 gf bot8)
.
Hint Constructors sound8.

Structure respectful8 (clo: rel -> rel) : Prop :=
  respectful8_intro {
      MON: monotone8 clo;
      RESPECTFUL:
        forall l r (LE: l <8= r) (GF: l <8= gf r),
          clo l <8= gf (clo r);
    }.
Hint Constructors respectful8.

Inductive gres8 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 : Prop :=
| gres8_intro
    clo
    (RES: respectful8 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7)
.
Hint Constructors gres8.
Lemma gfclo8_mon: forall clo, sound8 clo -> monotone8 (compose gf clo).
Proof. intros; destruct H; eauto using gf_mon. Qed.
Hint Resolve gfclo8_mon : paco.

Lemma sound8_is_gf: forall clo (UPTO: sound8 clo),
    paco8 (compose gf clo) bot8 <8= paco8 gf bot8.
Proof.
  intros. punfold PR. edestruct UPTO.
  eapply (SOUND (paco8 (compose gf clo) bot8)); [|eauto].
  intros. punfold PR0.
  eapply (gfclo8_mon UPTO); eauto. intros. destruct PR1; eauto. contradiction.
Qed.

Lemma respectful8_is_sound8: respectful8 <1= sound8.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \8/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; eauto.
  intros. set (rr e0 e1 e2 e3 e4 e5 e6 e7 := exists n, rclo clo n r e0 e1 e2 e3 e4 e5 e6 e7).
  assert (rr x0 x1 x2 x3 x4 x5 x6 x7) by (exists 0; eauto); clear PR.
  cut (forall n, rclo clo n r <8= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 x4 x5 x6 x7 H; pcofix CIH; intros.
    unfold rr in *; destruct H0; eauto 10 using gf_mon. }
  induction n; intros; [simpl; eauto using gf_mon|].
  simpl in *; destruct PR; [eauto using gf_mon|].
  eapply gf_mon; [eapply RESPECTFUL0; [|apply IHn|]|]; instantiate; simpl; eauto.
Qed.

Lemma respectful8_compose
      clo0 clo1
      (RES0: respectful8 clo0)
      (RES1: respectful8 clo1):
  respectful8 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; eauto.
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; eauto.
    + intros. eapply RESPECTFUL1; eauto.
Qed.

Lemma grespectful8_respectful8: respectful8 gres8.
Proof.
  econstructor; repeat intro.
  - destruct IN; destruct RES; exists clo; eauto.
  - destruct PR; destruct RES; eapply gf_mon with (r:=clo r); eauto.
Qed.

Lemma gfgres8_mon: monotone8 (compose gf gres8).
Proof.
  destruct grespectful8_respectful8; eauto using gf_mon.
Qed.
Hint Resolve gfgres8_mon : paco.

Lemma grespectful8_greatest: forall clo (RES: respectful8 clo), clo <9= gres8.
Proof. eauto. Qed.

Lemma grespectful8_incl: forall r, r <8= gres8 r.
Proof.
  intros; eexists (fun x => x); eauto.
Qed.
Hint Resolve grespectful8_incl.

Lemma grespectful8_compose: forall clo (RES: respectful8 clo) r,
    clo (gres8 r) <8= gres8 r.
Proof.
  intros; eapply grespectful8_greatest with (clo := compose clo gres8);
    eauto using respectful8_compose, grespectful8_respectful8.
Qed.

Lemma grespectful8_incl_rev: forall r,
    gres8 (paco8 (compose gf gres8) r) <8= paco8 (compose gf gres8) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful8_compose, grespectful8_respectful8.
  destruct grespectful8_respectful8; eapply RESPECTFUL0, PR; intros; [apply grespectful8_incl; eauto|].
  punfold PR0.
  eapply gfgres8_mon; eauto; intros; destruct PR1; eauto.
Qed.

Inductive rclo8 clo (r: rel): rel :=
| rclo8_incl
    e0 e1 e2 e3 e4 e5 e6 e7
    (R: r e0 e1 e2 e3 e4 e5 e6 e7):
    @rclo8 clo r e0 e1 e2 e3 e4 e5 e6 e7
| rclo8_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7
    (R': r' <8= rclo8 clo r)
    (CLOR':clo r' e0 e1 e2 e3 e4 e5 e6 e7):
    @rclo8 clo r e0 e1 e2 e3 e4 e5 e6 e7
| rclo8_gf
    r' e0 e1 e2 e3 e4 e5 e6 e7
    (R': r' <8= rclo8 clo r)
    (CLOR':@gf r' e0 e1 e2 e3 e4 e5 e6 e7):
    @rclo8 clo r e0 e1 e2 e3 e4 e5 e6 e7
.
Lemma rclo8_mon clo:
  monotone8 (rclo8 clo).
Proof.
  repeat intro. induction IN; eauto using rclo8.
Qed.
Hint Resolve rclo8_mon: paco.

Lemma rclo8_base
      clo
      (MON: monotone8 clo):
  clo <9= rclo8 clo.
Proof.
  simpl. intros. econstructor 2; eauto.
  eapply MON; eauto using rclo8.
Qed.

Lemma rclo8_step
      (clo: rel -> rel) r:
  clo (rclo8 clo r) <8= rclo8 clo r.
Proof.
  intros. econstructor 2; eauto.
Qed.

Lemma rclo8_rclo8
      clo r
      (MON: monotone8 clo):
  rclo8 clo (rclo8 clo r) <8= rclo8 clo r.
Proof.
  intros. induction PR; eauto using rclo8.
Qed.

Structure weak_respectful8 (clo: rel -> rel) : Prop :=
  weak_respectful8_intro {
      WEAK_MON: monotone8 clo;
      WEAK_RESPECTFUL:
        forall l r (LE: l <8= r) (GF: l <8= gf r),
          clo l <8= gf (rclo8 clo r);
    }.
Hint Constructors weak_respectful8.

Lemma weak_respectful8_respectful8
      clo (RES: weak_respectful8 clo):
  respectful8 (rclo8 clo).
Proof.
  inversion RES. econstructor; eauto with paco. intros.
  induction PR; intros.
  - eapply gf_mon; eauto. intros.
    apply rclo8_incl. auto.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo8_mon; eauto.
    + intros. apply rclo8_rclo8; auto.
  - eapply gf_mon; eauto using rclo8.
Qed.

Lemma upto8_init:
  paco8 (compose gf gres8) bot8 <8= paco8 gf bot8.
Proof.
  apply sound8_is_gf; eauto.
  apply respectful8_is_sound8.
  apply grespectful8_respectful8.
Qed.

Lemma upto8_final:
  paco8 gf <9= paco8 (compose gf gres8).
Proof.
  pcofix CIH. intros. punfold PR. pfold.
  eapply gf_mon; [|apply grespectful8_incl].
  eapply gf_mon; [eauto|]. intros. right. inversion PR0; auto.
Qed.

Lemma upto8_step
      r clo (RES: weak_respectful8 clo):
  clo (paco8 (compose gf gres8) r) <8= paco8 (compose gf gres8) r.
Proof.
  intros. apply grespectful8_incl_rev.
  assert (RES' := weak_respectful8_respectful8 RES).
  eapply grespectful8_greatest. eauto.
  eapply rclo8_base; eauto.
  inversion RES. auto.
Qed.

Lemma upto8_step_under
      r clo (RES: weak_respectful8 clo):
  clo (gres8 r) <8= gres8 r.
Proof.
  intros. apply weak_respectful8_respectful8 in RES; eauto.
  eapply grespectful8_compose; eauto. eauto using rclo8.
Qed.

End Respectful8.

Hint Constructors sound8.
Hint Constructors respectful8.
Hint Constructors gres8.
Hint Resolve gfclo8_mon : paco.
Hint Resolve gfgres8_mon : paco.
Hint Resolve grespectful8_incl.
Hint Resolve rclo8_mon: paco.
Hint Constructors weak_respectful8.

Ltac pupto8_init := eapply upto8_init; eauto with paco.
Ltac pupto8_final := first [eapply upto8_final; eauto with paco | eapply grespectful8_incl].
Ltac pupto8 H := first [eapply upto8_step|eapply upto8_step_under]; [|eapply H|]; eauto with paco.

