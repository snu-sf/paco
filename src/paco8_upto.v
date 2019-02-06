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
Proof.
  intros; destruct H; red; intros.
  eapply gf_mon; [apply IN|intros; eapply MON0; [apply PR|apply LE]].
Qed.
Hint Resolve gfclo8_mon : paco.

Lemma sound8_is_gf: forall clo (UPTO: sound8 clo),
    paco8 (compose gf clo) bot8 <8= paco8 gf bot8.
Proof.
  intros. _punfold PR; [|apply gfclo8_mon, UPTO]. edestruct UPTO.
  eapply (SOUND (paco8 (compose gf clo) bot8)).
  - intros. _punfold PR0; [|apply gfclo8_mon, UPTO].
    eapply (gfclo8_mon UPTO); [apply PR0| intros; destruct PR1; [apply H|destruct H]].
  - pfold. apply PR.
Qed.

Lemma respectful8_is_sound8: respectful8 <1= sound8.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \8/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; [apply MON0|].
  intros. set (rr e0 e1 e2 e3 e4 e5 e6 e7 := exists n, rclo clo n r e0 e1 e2 e3 e4 e5 e6 e7).
  assert (rr x0 x1 x2 x3 x4 x5 x6 x7) by (exists 0; apply PR); clear PR.
  cut (forall n, rclo clo n r <8= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 x4 x5 x6 x7 H; pcofix CIH; intros.
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

Lemma respectful8_compose
      clo0 clo1
      (RES0: respectful8 clo0)
      (RES1: respectful8 clo1):
  respectful8 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; [apply IN|].
    intros. eapply MON1; [apply PR|apply LE].
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; [apply PR0|apply LE].
    + intros. eapply RESPECTFUL1; [apply LE| apply GF| apply PR0].
Qed.

Lemma grespectful8_mon: monotone8 gres8.
Proof.
  red. intros.
  destruct IN; destruct RES; exists clo; [|eapply MON0; [eapply CLO| eapply LE]].
  constructor; [eapply MON0|].
  intros. eapply RESPECTFUL0; [apply LE0|apply GF|apply PR].
Qed.

Lemma grespectful8_respectful8: respectful8 gres8.
Proof.
  econstructor; [apply grespectful8_mon|intros].
  destruct PR; destruct RES; eapply gf_mon with (r:=clo r).
  eapply RESPECTFUL0; [apply LE|apply GF|apply CLO].
  intros. econstructor; [constructor; [apply MON0|apply RESPECTFUL0]|apply PR].
Qed.

Lemma gfgres8_mon: monotone8 (compose gf gres8).
Proof.
  destruct grespectful8_respectful8.
  unfold monotone8. intros. eapply gf_mon; [eapply IN|].
  intros. eapply MON0;[apply PR|apply LE].
Qed.
Hint Resolve gfgres8_mon : paco.

Lemma grespectful8_greatest: forall clo (RES: respectful8 clo), clo <9= gres8.
Proof. intros. econstructor;[apply RES|apply PR]. Qed.

Lemma grespectful8_incl: forall r, r <8= gres8 r.
Proof.
  intros; eexists (fun x => x).
  - econstructor.
    + red; intros; apply LE, IN.
    + intros; apply GF, PR0.
  - apply PR.
Qed.
Hint Resolve grespectful8_incl.

Lemma grespectful8_compose: forall clo (RES: respectful8 clo) r,
    clo (gres8 r) <8= gres8 r.
Proof.
  intros; eapply grespectful8_greatest with (clo := compose clo gres8); [|apply PR].
  apply respectful8_compose; [apply RES|apply grespectful8_respectful8].
Qed.

Lemma grespectful8_incl_rev: forall r,
    gres8 (paco8 (compose gf gres8) r) <8= paco8 (compose gf gres8) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful8_compose, grespectful8_respectful8.
  destruct grespectful8_respectful8; eapply RESPECTFUL0, PR; intros; [apply grespectful8_incl; right; apply CIH, grespectful8_incl, PR0|].
  _punfold PR0; [|apply gfgres8_mon].
  eapply gfgres8_mon; [apply PR0|].
  intros; destruct PR1.
  - left. eapply paco8_mon; [apply H| apply CIH0].
  - right. eapply CIH0, H.
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
  repeat intro. induction IN.
  - econstructor 1. apply LE, R.
  - econstructor 2; [intros; eapply H, PR| eapply CLOR'].
  - econstructor 3; [intros; eapply H, PR| eapply CLOR'].
Qed.
Hint Resolve rclo8_mon: paco.

Lemma rclo8_base
      clo
      (MON: monotone8 clo):
  clo <9= rclo8 clo.
Proof.
  intros. econstructor 2; [intros; apply PR0|].
  eapply MON; [apply PR|intros; constructor; apply PR0].
Qed.

Lemma rclo8_step
      (clo: rel -> rel) r:
  clo (rclo8 clo r) <8= rclo8 clo r.
Proof.
  intros. econstructor 2; [intros; apply PR0|apply PR].
Qed.

Lemma rclo8_rclo8
      clo r
      (MON: monotone8 clo):
  rclo8 clo (rclo8 clo r) <8= rclo8 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
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
  inversion RES. econstructor; [eapply rclo8_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply GF, R|]. intros.
    apply rclo8_incl. apply PR.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo8_mon; [apply R', PR|apply LE].
    + intros. apply rclo8_rclo8;[apply WEAK_MON0|apply PR].
  - eapply gf_mon; [apply CLOR'|].
    intros. eapply rclo8_mon; [apply R', PR| apply LE].
Qed.

Lemma upto8_init:
  paco8 (compose gf gres8) bot8 <8= paco8 gf bot8.
Proof.
  apply sound8_is_gf.
  apply respectful8_is_sound8.
  apply grespectful8_respectful8.
Qed.

Lemma upto8_final:
  paco8 gf <9= paco8 (compose gf gres8).
Proof.
  pcofix CIH. intros. _punfold PR; [|apply gf_mon]. pfold.
  eapply gf_mon; [|apply grespectful8_incl].
  eapply gf_mon; [apply PR|]. intros. right.
  inversion PR0; [apply CIH, H | apply CIH0, H].
Qed.

Lemma upto8_step
      r clo (RES: weak_respectful8 clo):
  clo (paco8 (compose gf gres8) r) <8= paco8 (compose gf gres8) r.
Proof.
  intros. apply grespectful8_incl_rev.
  assert (RES' := weak_respectful8_respectful8 RES).
  eapply grespectful8_greatest; [apply RES'|].
  eapply rclo8_base; [apply RES|].
  inversion RES. apply PR.
Qed.

Lemma upto8_step_under
      r clo (RES: weak_respectful8 clo):
  clo (gres8 r) <8= gres8 r.
Proof.
  intros. apply weak_respectful8_respectful8 in RES.
  eapply grespectful8_compose; [apply RES|].
  econstructor 2; [intros; constructor 1; apply PR0 | apply PR].
Qed.

End Respectful8.

Lemma grespectful8_impl T0 T1 T2 T3 T4 T5 T6 T7 (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r x0 x1 x2 x3 x4 x5 x6 x7
    (PR: gres8 gf r x0 x1 x2 x3 x4 x5 x6 x7)
    (EQ: forall r x0 x1 x2 x3 x4 x5 x6 x7, gf r x0 x1 x2 x3 x4 x5 x6 x7 <-> gf' r x0 x1 x2 x3 x4 x5 x6 x7):
  gres8 gf' r x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  intros. destruct PR. econstructor; [|apply CLO].
  destruct RES. econstructor; [apply MON0|].
  intros. rewrite <-EQ. eapply RESPECTFUL0; [apply LE| |apply PR].
  intros. rewrite EQ. apply GF, PR0.
Qed.

Lemma grespectful8_iff T0 T1 T2 T3 T4 T5 T6 T7 (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r x0 x1 x2 x3 x4 x5 x6 x7
    (EQ: forall r x0 x1 x2 x3 x4 x5 x6 x7, gf r x0 x1 x2 x3 x4 x5 x6 x7 <-> gf' r x0 x1 x2 x3 x4 x5 x6 x7):
  gres8 gf r x0 x1 x2 x3 x4 x5 x6 x7 <-> gres8 gf' r x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  split; intros.
  - eapply grespectful8_impl; [apply H | apply EQ].
  - eapply grespectful8_impl; [apply H | symmetry; apply EQ].
Qed.

Hint Constructors sound8.
Hint Constructors respectful8.
Hint Constructors gres8.
Hint Resolve gfclo8_mon : paco.
Hint Resolve gfgres8_mon : paco.
Hint Resolve grespectful8_incl.
Hint Resolve rclo8_mon: paco.
Hint Constructors weak_respectful8.

Ltac pupto8_init := eapply upto8_init; [eauto with paco|].
Ltac pupto8_final := first [eapply upto8_final; [eauto with paco|] | eapply grespectful8_incl].
Ltac pupto8 H := first [eapply upto8_step|eapply upto8_step_under]; [|eapply H|]; [eauto with paco|].

