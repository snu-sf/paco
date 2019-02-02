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
Proof.
  intros; destruct H; red; intros.
  eapply gf_mon; [apply IN|intros; eapply MON0; [apply PR|apply LE]].
Qed.
Hint Resolve gfclo9_mon : paco.

Lemma sound9_is_gf: forall clo (UPTO: sound9 clo),
    paco9 (compose gf clo) bot9 <9= paco9 gf bot9.
Proof.
  intros. _punfold PR; [|apply gfclo9_mon, UPTO]. edestruct UPTO.
  eapply (SOUND (paco9 (compose gf clo) bot9)).
  - intros. _punfold PR0; [|apply gfclo9_mon, UPTO].
    eapply (gfclo9_mon UPTO); [apply PR0| intros; destruct PR1; [apply H|destruct H]].
  - pfold. apply PR.
Qed.

Lemma respectful9_is_sound9: respectful9 <1= sound9.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \9/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; [apply MON0|].
  intros. set (rr e0 e1 e2 e3 e4 e5 e6 e7 e8 := exists n, rclo clo n r e0 e1 e2 e3 e4 e5 e6 e7 e8).
  assert (rr x0 x1 x2 x3 x4 x5 x6 x7 x8) by (exists 0; apply PR); clear PR.
  cut (forall n, rclo clo n r <9= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 H; pcofix CIH; intros.
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

Lemma respectful9_compose
      clo0 clo1
      (RES0: respectful9 clo0)
      (RES1: respectful9 clo1):
  respectful9 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; [apply IN|].
    intros. eapply MON1; [apply PR|apply LE].
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; [apply PR0|apply LE].
    + intros. eapply RESPECTFUL1; [apply LE| apply GF| apply PR0].
Qed.

Lemma grespectful9_respectful9: respectful9 gres9.
Proof.
  econstructor; repeat intro.
  - destruct IN; destruct RES; exists clo; [|eapply MON0; [eapply CLO| eapply LE]].
    constructor; [eapply MON0|].
    intros. eapply RESPECTFUL0; [apply LE0|apply GF|apply PR].
  - destruct PR; destruct RES; eapply gf_mon with (r:=clo r).
    eapply RESPECTFUL0; [apply LE|apply GF|apply CLO].
    intros. econstructor; [constructor; [apply MON0|apply RESPECTFUL0]|apply PR].
Qed.

Lemma gfgres9_mon: monotone9 (compose gf gres9).
Proof.
  destruct grespectful9_respectful9.
  unfold monotone9. intros. eapply gf_mon; [eapply IN|].
  intros. eapply MON0;[apply PR|apply LE].
Qed.
Hint Resolve gfgres9_mon : paco.

Lemma grespectful9_greatest: forall clo (RES: respectful9 clo), clo <10= gres9.
Proof. intros. econstructor;[apply RES|apply PR]. Qed.

Lemma grespectful9_incl: forall r, r <9= gres9 r.
Proof.
  intros; eexists (fun x => x).
  - econstructor.
    + red; intros; apply LE, IN.
    + intros; apply GF, PR0.
  - apply PR.
Qed.
Hint Resolve grespectful9_incl.

Lemma grespectful9_compose: forall clo (RES: respectful9 clo) r,
    clo (gres9 r) <9= gres9 r.
Proof.
  intros; eapply grespectful9_greatest with (clo := compose clo gres9); [|apply PR].
  apply respectful9_compose; [apply RES|apply grespectful9_respectful9].
Qed.

Lemma grespectful9_incl_rev: forall r,
    gres9 (paco9 (compose gf gres9) r) <9= paco9 (compose gf gres9) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful9_compose, grespectful9_respectful9.
  destruct grespectful9_respectful9; eapply RESPECTFUL0, PR; intros; [apply grespectful9_incl; right; apply CIH, grespectful9_incl, PR0|].
  _punfold PR0; [|apply gfgres9_mon].
  eapply gfgres9_mon; [apply PR0|].
  intros; destruct PR1.
  - left. eapply paco9_mon; [apply H| apply CIH0].
  - right. eapply CIH0, H.
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
  repeat intro. induction IN.
  - econstructor 1. apply LE, R.
  - econstructor 2; [intros; eapply H, PR| eapply CLOR'].
  - econstructor 3; [intros; eapply H, PR| eapply CLOR'].
Qed.
Hint Resolve rclo9_mon: paco.

Lemma rclo9_base
      clo
      (MON: monotone9 clo):
  clo <10= rclo9 clo.
Proof.
  intros. econstructor 2; [intros; apply PR0|].
  eapply MON; [apply PR|intros; constructor; apply PR0].
Qed.

Lemma rclo9_step
      (clo: rel -> rel) r:
  clo (rclo9 clo r) <9= rclo9 clo r.
Proof.
  intros. econstructor 2; [intros; apply PR0|apply PR].
Qed.

Lemma rclo9_rclo9
      clo r
      (MON: monotone9 clo):
  rclo9 clo (rclo9 clo r) <9= rclo9 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
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
  inversion RES. econstructor; [eapply rclo9_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply GF, R|]. intros.
    apply rclo9_incl. apply PR.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo9_mon; [apply R', PR|apply LE].
    + intros. apply rclo9_rclo9;[apply WEAK_MON0|apply PR].
  - eapply gf_mon; [apply CLOR'|].
    intros. eapply rclo9_mon; [apply R', PR| apply LE].
Qed.

Lemma upto9_init:
  paco9 (compose gf gres9) bot9 <9= paco9 gf bot9.
Proof.
  apply sound9_is_gf.
  apply respectful9_is_sound9.
  apply grespectful9_respectful9.
Qed.

Lemma upto9_final:
  paco9 gf <10= paco9 (compose gf gres9).
Proof.
  pcofix CIH. intros. _punfold PR; [|apply gf_mon]. pfold.
  eapply gf_mon; [|apply grespectful9_incl].
  eapply gf_mon; [apply PR|]. intros. right.
  inversion PR0; [apply CIH, H | apply CIH0, H].
Qed.

Lemma upto9_step
      r clo (RES: weak_respectful9 clo):
  clo (paco9 (compose gf gres9) r) <9= paco9 (compose gf gres9) r.
Proof.
  intros. apply grespectful9_incl_rev.
  assert (RES' := weak_respectful9_respectful9 RES).
  eapply grespectful9_greatest; [apply RES'|].
  eapply rclo9_base; [apply RES|].
  inversion RES. apply PR.
Qed.

Lemma upto9_step_under
      r clo (RES: weak_respectful9 clo):
  clo (gres9 r) <9= gres9 r.
Proof.
  intros. apply weak_respectful9_respectful9 in RES.
  eapply grespectful9_compose; [apply RES|].
  econstructor 2; [intros; constructor 1; apply PR0 | apply PR].
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

Ltac pupto9_init := eapply upto9_init; [eauto with paco|].
Ltac pupto9_final := first [eapply upto9_final; [eauto with paco|] | eapply grespectful9_incl].
Ltac pupto9 H := first [eapply upto9_step|eapply upto9_step_under]; [eauto with paco|eapply H|].

