Require Export Program.Basics. Open Scope program_scope.
Require Import paco10.
Set Implicit Arguments.

Section Respectful10.

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

Local Notation rel := (rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone10 gf.

Inductive sound10 (clo: rel -> rel): Prop :=
| sound10_intro
    (MON: monotone10 clo)
    (SOUND:
       forall r (PFIX: r <10= gf (clo r)),
         r <10= paco10 gf bot10)
.
Hint Constructors sound10.

Structure respectful10 (clo: rel -> rel) : Prop :=
  respectful10_intro {
      MON: monotone10 clo;
      RESPECTFUL:
        forall l r (LE: l <10= r) (GF: l <10= gf r),
          clo l <10= gf (clo r);
    }.
Hint Constructors respectful10.

Inductive gres10 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 : Prop :=
| gres10_intro
    clo
    (RES: respectful10 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9)
.
Hint Constructors gres10.
Lemma gfclo10_mon: forall clo, sound10 clo -> monotone10 (compose gf clo).
Proof.
  intros; destruct H; red; intros.
  eapply gf_mon; [apply IN|intros; eapply MON0; [apply PR|apply LE]].
Qed.
Hint Resolve gfclo10_mon : paco.

Lemma sound10_is_gf: forall clo (UPTO: sound10 clo),
    paco10 (compose gf clo) bot10 <10= paco10 gf bot10.
Proof.
  intros. _punfold PR; [|apply gfclo10_mon, UPTO]. edestruct UPTO.
  eapply (SOUND (paco10 (compose gf clo) bot10)).
  - intros. _punfold PR0; [|apply gfclo10_mon, UPTO].
    eapply (gfclo10_mon UPTO); [apply PR0| intros; destruct PR1; [apply H|destruct H]].
  - pfold. apply PR.
Qed.

Lemma respectful10_is_sound10: respectful10 <1= sound10.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \10/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; [apply MON0|].
  intros. set (rr e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 := exists n, rclo clo n r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9).
  assert (rr x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) by (exists 0; apply PR); clear PR.
  cut (forall n, rclo clo n r <10= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 H; pcofix CIH; intros.
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

Lemma respectful10_compose
      clo0 clo1
      (RES0: respectful10 clo0)
      (RES1: respectful10 clo1):
  respectful10 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; [apply IN|].
    intros. eapply MON1; [apply PR|apply LE].
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; [apply PR0|apply LE].
    + intros. eapply RESPECTFUL1; [apply LE| apply GF| apply PR0].
Qed.

Lemma grespectful10_mon: monotone10 gres10.
Proof.
  red. intros.
  destruct IN; destruct RES; exists clo; [|eapply MON0; [eapply CLO| eapply LE]].
  constructor; [eapply MON0|].
  intros. eapply RESPECTFUL0; [apply LE0|apply GF|apply PR].
Qed.

Lemma grespectful10_respectful10: respectful10 gres10.
Proof.
  econstructor; [apply grespectful10_mon|intros].
  destruct PR; destruct RES; eapply gf_mon with (r:=clo r).
  eapply RESPECTFUL0; [apply LE|apply GF|apply CLO].
  intros. econstructor; [constructor; [apply MON0|apply RESPECTFUL0]|apply PR].
Qed.

Lemma gfgres10_mon: monotone10 (compose gf gres10).
Proof.
  destruct grespectful10_respectful10.
  unfold monotone10. intros. eapply gf_mon; [eapply IN|].
  intros. eapply MON0;[apply PR|apply LE].
Qed.
Hint Resolve gfgres10_mon : paco.

Lemma grespectful10_greatest: forall clo (RES: respectful10 clo), clo <11= gres10.
Proof. intros. econstructor;[apply RES|apply PR]. Qed.

Lemma grespectful10_incl: forall r, r <10= gres10 r.
Proof.
  intros; eexists (fun x => x).
  - econstructor.
    + red; intros; apply LE, IN.
    + intros; apply GF, PR0.
  - apply PR.
Qed.
Hint Resolve grespectful10_incl.

Lemma grespectful10_compose: forall clo (RES: respectful10 clo) r,
    clo (gres10 r) <10= gres10 r.
Proof.
  intros; eapply grespectful10_greatest with (clo := compose clo gres10); [|apply PR].
  apply respectful10_compose; [apply RES|apply grespectful10_respectful10].
Qed.

Lemma grespectful10_incl_rev: forall r,
    gres10 (paco10 (compose gf gres10) r) <10= paco10 (compose gf gres10) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful10_compose, grespectful10_respectful10.
  destruct grespectful10_respectful10; eapply RESPECTFUL0, PR; intros; [apply grespectful10_incl; right; apply CIH, grespectful10_incl, PR0|].
  _punfold PR0; [|apply gfgres10_mon].
  eapply gfgres10_mon; [apply PR0|].
  intros; destruct PR1.
  - left. eapply paco10_mon; [apply H| apply CIH0].
  - right. eapply CIH0, H.
Qed.

Inductive rclo10 clo (r: rel): rel :=
| rclo10_incl
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9):
    @rclo10 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
| rclo10_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
    (R': r' <10= rclo10 clo r)
    (CLOR':clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9):
    @rclo10 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
| rclo10_gf
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
    (R': r' <10= rclo10 clo r)
    (CLOR':@gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9):
    @rclo10 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
.
Lemma rclo10_mon clo:
  monotone10 (rclo10 clo).
Proof.
  repeat intro. induction IN.
  - econstructor 1. apply LE, R.
  - econstructor 2; [intros; eapply H, PR| eapply CLOR'].
  - econstructor 3; [intros; eapply H, PR| eapply CLOR'].
Qed.
Hint Resolve rclo10_mon: paco.

Lemma rclo10_base
      clo
      (MON: monotone10 clo):
  clo <11= rclo10 clo.
Proof.
  intros. econstructor 2; [intros; apply PR0|].
  eapply MON; [apply PR|intros; constructor; apply PR0].
Qed.

Lemma rclo10_step
      (clo: rel -> rel) r:
  clo (rclo10 clo r) <10= rclo10 clo r.
Proof.
  intros. econstructor 2; [intros; apply PR0|apply PR].
Qed.

Lemma rclo10_rclo10
      clo r
      (MON: monotone10 clo):
  rclo10 clo (rclo10 clo r) <10= rclo10 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
Qed.

Structure weak_respectful10 (clo: rel -> rel) : Prop :=
  weak_respectful10_intro {
      WEAK_MON: monotone10 clo;
      WEAK_RESPECTFUL:
        forall l r (LE: l <10= r) (GF: l <10= gf r),
          clo l <10= gf (rclo10 clo r);
    }.
Hint Constructors weak_respectful10.

Lemma weak_respectful10_respectful10
      clo (RES: weak_respectful10 clo):
  respectful10 (rclo10 clo).
Proof.
  inversion RES. econstructor; [eapply rclo10_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply GF, R|]. intros.
    apply rclo10_incl. apply PR.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo10_mon; [apply R', PR|apply LE].
    + intros. apply rclo10_rclo10;[apply WEAK_MON0|apply PR].
  - eapply gf_mon; [apply CLOR'|].
    intros. eapply rclo10_mon; [apply R', PR| apply LE].
Qed.

Lemma upto10_init:
  paco10 (compose gf gres10) bot10 <10= paco10 gf bot10.
Proof.
  apply sound10_is_gf.
  apply respectful10_is_sound10.
  apply grespectful10_respectful10.
Qed.

Lemma upto10_final:
  paco10 gf <11= paco10 (compose gf gres10).
Proof.
  pcofix CIH. intros. _punfold PR; [|apply gf_mon]. pfold.
  eapply gf_mon; [|apply grespectful10_incl].
  eapply gf_mon; [apply PR|]. intros. right.
  inversion PR0; [apply CIH, H | apply CIH0, H].
Qed.

Lemma upto10_step
      r clo (RES: weak_respectful10 clo):
  clo (paco10 (compose gf gres10) r) <10= paco10 (compose gf gres10) r.
Proof.
  intros. apply grespectful10_incl_rev.
  assert (RES' := weak_respectful10_respectful10 RES).
  eapply grespectful10_greatest; [apply RES'|].
  eapply rclo10_base; [apply RES|].
  inversion RES. apply PR.
Qed.

Lemma upto10_step_under
      r clo (RES: weak_respectful10 clo):
  clo (gres10 r) <10= gres10 r.
Proof.
  intros. apply weak_respectful10_respectful10 in RES.
  eapply grespectful10_compose; [apply RES|].
  econstructor 2; [intros; constructor 1; apply PR0 | apply PR].
Qed.

End Respectful10.

Lemma grespectful10_impl T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    (PR: gres10 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
    (EQ: forall r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9, gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 <-> gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9):
  gres10 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  intros. destruct PR. econstructor; [|apply CLO].
  destruct RES. econstructor; [apply MON0|].
  intros. eapply EQ. eapply RESPECTFUL0; [apply LE| |apply PR].
  intros. eapply EQ. apply GF, PR0.
Qed.

Lemma grespectful10_iff T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    (EQ: forall r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9, gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 <-> gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9):
  gres10 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 <-> gres10 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  split; intros.
  - eapply grespectful10_impl; [apply H | apply EQ].
  - eapply grespectful10_impl; [apply H | split; apply EQ].
Qed.

Hint Constructors sound10.
Hint Constructors respectful10.
Hint Constructors gres10.
Hint Resolve gfclo10_mon : paco.
Hint Resolve gfgres10_mon : paco.
Hint Resolve grespectful10_incl.
Hint Resolve rclo10_mon: paco.
Hint Constructors weak_respectful10.

Ltac pupto10_init := eapply upto10_init; [eauto with paco|].
Ltac pupto10_final := first [eapply upto10_final; [eauto with paco|] | eapply grespectful10_incl].
Ltac pupto10 H := first [eapply upto10_step|eapply upto10_step_under]; [|eapply H|]; [eauto with paco|].

