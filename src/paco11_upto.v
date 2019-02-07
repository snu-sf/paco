Require Import paco11.
Require Import Setoids.Setoid.
Set Implicit Arguments.

Section Respectful11.

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

Local Notation rel := (rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone11 gf.

Inductive sound11 (clo: rel -> rel): Prop :=
| sound11_intro
    (MON: monotone11 clo)
    (SOUND:
       forall r (PFIX: r <11= gf (clo r)),
         r <11= paco11 gf bot11)
.
Hint Constructors sound11.

Structure respectful11 (clo: rel -> rel) : Prop :=
  respectful11_intro {
      MON: monotone11 clo;
      RESPECTFUL:
        forall l r (LE: l <11= r) (GF: l <11= gf r),
          clo l <11= gf (clo r);
    }.
Hint Constructors respectful11.

Inductive gres11 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 : Prop :=
| gres11_intro
    clo
    (RES: respectful11 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)
.
Hint Constructors gres11.
Lemma gfclo11_mon: forall clo, sound11 clo -> monotone11 (compose gf clo).
Proof.
  intros; destruct H; red; intros.
  eapply gf_mon; [apply IN|intros; eapply MON0; [apply PR|apply LE]].
Qed.
Hint Resolve gfclo11_mon : paco.

Lemma sound11_is_gf: forall clo (UPTO: sound11 clo),
    paco11 (compose gf clo) bot11 <11= paco11 gf bot11.
Proof.
  intros. _punfold PR; [|apply gfclo11_mon, UPTO]. edestruct UPTO.
  eapply (SOUND (paco11 (compose gf clo) bot11)).
  - intros. _punfold PR0; [|apply gfclo11_mon, UPTO].
    eapply (gfclo11_mon UPTO); [apply PR0| intros; destruct PR1; [apply H|destruct H]].
  - pfold. apply PR.
Qed.

Lemma respectful11_is_sound11: respectful11 <1= sound11.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \11/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; [apply MON0|].
  intros. set (rr e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 := exists n, rclo clo n r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10).
  assert (rr x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) by (exists 0; apply PR); clear PR.
  cut (forall n, rclo clo n r <11= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 H; pcofix CIH; intros.
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

Lemma respectful11_compose
      clo0 clo1
      (RES0: respectful11 clo0)
      (RES1: respectful11 clo1):
  respectful11 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; [apply IN|].
    intros. eapply MON1; [apply PR|apply LE].
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; [apply PR0|apply LE].
    + intros. eapply RESPECTFUL1; [apply LE| apply GF| apply PR0].
Qed.

Lemma grespectful11_mon: monotone11 gres11.
Proof.
  red. intros.
  destruct IN; destruct RES; exists clo; [|eapply MON0; [eapply CLO| eapply LE]].
  constructor; [eapply MON0|].
  intros. eapply RESPECTFUL0; [apply LE0|apply GF|apply PR].
Qed.

Lemma grespectful11_respectful11: respectful11 gres11.
Proof.
  econstructor; [apply grespectful11_mon|intros].
  destruct PR; destruct RES; eapply gf_mon with (r:=clo r).
  eapply RESPECTFUL0; [apply LE|apply GF|apply CLO].
  intros. econstructor; [constructor; [apply MON0|apply RESPECTFUL0]|apply PR].
Qed.

Lemma gfgres11_mon: monotone11 (compose gf gres11).
Proof.
  destruct grespectful11_respectful11.
  unfold monotone11. intros. eapply gf_mon; [eapply IN|].
  intros. eapply MON0;[apply PR|apply LE].
Qed.
Hint Resolve gfgres11_mon : paco.

Lemma grespectful11_greatest: forall clo (RES: respectful11 clo), clo <12= gres11.
Proof. intros. econstructor;[apply RES|apply PR]. Qed.

Lemma grespectful11_incl: forall r, r <11= gres11 r.
Proof.
  intros; eexists (fun x => x).
  - econstructor.
    + red; intros; apply LE, IN.
    + intros; apply GF, PR0.
  - apply PR.
Qed.
Hint Resolve grespectful11_incl.

Lemma grespectful11_compose: forall clo (RES: respectful11 clo) r,
    clo (gres11 r) <11= gres11 r.
Proof.
  intros; eapply grespectful11_greatest with (clo := compose clo gres11); [|apply PR].
  apply respectful11_compose; [apply RES|apply grespectful11_respectful11].
Qed.

Lemma grespectful11_incl_rev: forall r,
    gres11 (paco11 (compose gf gres11) r) <11= paco11 (compose gf gres11) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful11_compose, grespectful11_respectful11.
  destruct grespectful11_respectful11; eapply RESPECTFUL0, PR; intros; [apply grespectful11_incl; right; apply CIH, grespectful11_incl, PR0|].
  _punfold PR0; [|apply gfgres11_mon].
  eapply gfgres11_mon; [apply PR0|].
  intros; destruct PR1.
  - left. eapply paco11_mon; [apply H| apply CIH0].
  - right. eapply CIH0, H.
Qed.

Inductive rclo11 clo (r: rel): rel :=
| rclo11_incl
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10):
    @rclo11 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
| rclo11_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    (R': r' <11= rclo11 clo r)
    (CLOR':clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10):
    @rclo11 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
| rclo11_gf
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    (R': r' <11= rclo11 clo r)
    (CLOR':@gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10):
    @rclo11 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
.
Lemma rclo11_mon clo:
  monotone11 (rclo11 clo).
Proof.
  repeat intro. induction IN.
  - econstructor 1. apply LE, R.
  - econstructor 2; [intros; eapply H, PR| eapply CLOR'].
  - econstructor 3; [intros; eapply H, PR| eapply CLOR'].
Qed.
Hint Resolve rclo11_mon: paco.

Lemma rclo11_base
      clo
      (MON: monotone11 clo):
  clo <12= rclo11 clo.
Proof.
  intros. econstructor 2; [intros; apply PR0|].
  eapply MON; [apply PR|intros; constructor; apply PR0].
Qed.

Lemma rclo11_step
      (clo: rel -> rel) r:
  clo (rclo11 clo r) <11= rclo11 clo r.
Proof.
  intros. econstructor 2; [intros; apply PR0|apply PR].
Qed.

Lemma rclo11_rclo11
      clo r
      (MON: monotone11 clo):
  rclo11 clo (rclo11 clo r) <11= rclo11 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
Qed.

Structure weak_respectful11 (clo: rel -> rel) : Prop :=
  weak_respectful11_intro {
      WEAK_MON: monotone11 clo;
      WEAK_RESPECTFUL:
        forall l r (LE: l <11= r) (GF: l <11= gf r),
          clo l <11= gf (rclo11 clo r);
    }.
Hint Constructors weak_respectful11.

Lemma weak_respectful11_respectful11
      clo (RES: weak_respectful11 clo):
  respectful11 (rclo11 clo).
Proof.
  inversion RES. econstructor; [eapply rclo11_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply GF, R|]. intros.
    apply rclo11_incl. apply PR.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo11_mon; [apply R', PR|apply LE].
    + intros. apply rclo11_rclo11;[apply WEAK_MON0|apply PR].
  - eapply gf_mon; [apply CLOR'|].
    intros. eapply rclo11_mon; [apply R', PR| apply LE].
Qed.

Lemma upto11_init:
  paco11 (compose gf gres11) bot11 <11= paco11 gf bot11.
Proof.
  apply sound11_is_gf.
  apply respectful11_is_sound11.
  apply grespectful11_respectful11.
Qed.

Lemma upto11_final:
  paco11 gf <12= paco11 (compose gf gres11).
Proof.
  pcofix CIH. intros. _punfold PR; [|apply gf_mon]. pfold.
  eapply gf_mon; [|apply grespectful11_incl].
  eapply gf_mon; [apply PR|]. intros. right.
  inversion PR0; [apply CIH, H | apply CIH0, H].
Qed.

Lemma upto11_step
      r clo (RES: weak_respectful11 clo):
  clo (paco11 (compose gf gres11) r) <11= paco11 (compose gf gres11) r.
Proof.
  intros. apply grespectful11_incl_rev.
  assert (RES' := weak_respectful11_respectful11 RES).
  eapply grespectful11_greatest; [apply RES'|].
  eapply rclo11_base; [apply RES|].
  inversion RES. apply PR.
Qed.

Lemma upto11_step_under
      r clo (RES: weak_respectful11 clo):
  clo (gres11 r) <11= gres11 r.
Proof.
  intros. apply weak_respectful11_respectful11 in RES.
  eapply grespectful11_compose; [apply RES|].
  econstructor 2; [intros; constructor 1; apply PR0 | apply PR].
Qed.

End Respectful11.

Lemma grespectful11_impl T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    (PR: gres11 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
    (EQ: forall r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 <-> gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10):
  gres11 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  intros. destruct PR. econstructor; [|apply CLO].
  destruct RES. econstructor; [apply MON0|].
  intros. rewrite <- EQ. eapply RESPECTFUL0; [apply LE| |apply PR].
  intros. rewrite EQ. apply GF, PR0.
Qed.

Lemma grespectful11_iff T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    (EQ: forall r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 <-> gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10):
  gres11 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 <-> gres11 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  split; intros.
  - eapply grespectful11_impl; [apply H | apply EQ].
  - eapply grespectful11_impl; [apply H | symmetry; apply EQ].
Qed.

Hint Constructors sound11.
Hint Constructors respectful11.
Hint Constructors gres11.
Hint Resolve gfclo11_mon : paco.
Hint Resolve gfgres11_mon : paco.
Hint Resolve grespectful11_incl.
Hint Resolve rclo11_mon: paco.
Hint Constructors weak_respectful11.

Ltac pupto11_init := eapply upto11_init; [eauto with paco|].
Ltac pupto11_final := first [eapply upto11_final; [eauto with paco|] | eapply grespectful11_incl].
Ltac pupto11 H := first [eapply upto11_step|eapply upto11_step_under]; [|eapply H|]; [eauto with paco|].

