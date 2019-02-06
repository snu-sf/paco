Require Import paco7.
Require Export Program.
Set Implicit Arguments.

Section Respectful7.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.

Local Notation rel := (rel7 T0 T1 T2 T3 T4 T5 T6).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone7 gf.

Inductive sound7 (clo: rel -> rel): Prop :=
| sound7_intro
    (MON: monotone7 clo)
    (SOUND:
       forall r (PFIX: r <7= gf (clo r)),
         r <7= paco7 gf bot7)
.
Hint Constructors sound7.

Structure respectful7 (clo: rel -> rel) : Prop :=
  respectful7_intro {
      MON: monotone7 clo;
      RESPECTFUL:
        forall l r (LE: l <7= r) (GF: l <7= gf r),
          clo l <7= gf (clo r);
    }.
Hint Constructors respectful7.

Inductive gres7 (r: rel) e0 e1 e2 e3 e4 e5 e6 : Prop :=
| gres7_intro
    clo
    (RES: respectful7 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6)
.
Hint Constructors gres7.
Lemma gfclo7_mon: forall clo, sound7 clo -> monotone7 (compose gf clo).
Proof.
  intros; destruct H; red; intros.
  eapply gf_mon; [apply IN|intros; eapply MON0; [apply PR|apply LE]].
Qed.
Hint Resolve gfclo7_mon : paco.

Lemma sound7_is_gf: forall clo (UPTO: sound7 clo),
    paco7 (compose gf clo) bot7 <7= paco7 gf bot7.
Proof.
  intros. _punfold PR; [|apply gfclo7_mon, UPTO]. edestruct UPTO.
  eapply (SOUND (paco7 (compose gf clo) bot7)).
  - intros. _punfold PR0; [|apply gfclo7_mon, UPTO].
    eapply (gfclo7_mon UPTO); [apply PR0| intros; destruct PR1; [apply H|destruct H]].
  - pfold. apply PR.
Qed.

Lemma respectful7_is_sound7: respectful7 <1= sound7.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \7/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; [apply MON0|].
  intros. set (rr e0 e1 e2 e3 e4 e5 e6 := exists n, rclo clo n r e0 e1 e2 e3 e4 e5 e6).
  assert (rr x0 x1 x2 x3 x4 x5 x6) by (exists 0; apply PR); clear PR.
  cut (forall n, rclo clo n r <7= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 x4 x5 x6 H; pcofix CIH; intros.
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

Lemma respectful7_compose
      clo0 clo1
      (RES0: respectful7 clo0)
      (RES1: respectful7 clo1):
  respectful7 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; [apply IN|].
    intros. eapply MON1; [apply PR|apply LE].
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; [apply PR0|apply LE].
    + intros. eapply RESPECTFUL1; [apply LE| apply GF| apply PR0].
Qed.

Lemma grespectful7_mon: monotone7 gres7.
Proof.
  red. intros.
  destruct IN; destruct RES; exists clo; [|eapply MON0; [eapply CLO| eapply LE]].
  constructor; [eapply MON0|].
  intros. eapply RESPECTFUL0; [apply LE0|apply GF|apply PR].
Qed.

Lemma grespectful7_respectful7: respectful7 gres7.
Proof.
  econstructor; [apply grespectful7_mon|intros].
  destruct PR; destruct RES; eapply gf_mon with (r:=clo r).
  eapply RESPECTFUL0; [apply LE|apply GF|apply CLO].
  intros. econstructor; [constructor; [apply MON0|apply RESPECTFUL0]|apply PR].
Qed.

Lemma gfgres7_mon: monotone7 (compose gf gres7).
Proof.
  destruct grespectful7_respectful7.
  unfold monotone7. intros. eapply gf_mon; [eapply IN|].
  intros. eapply MON0;[apply PR|apply LE].
Qed.
Hint Resolve gfgres7_mon : paco.

Lemma grespectful7_greatest: forall clo (RES: respectful7 clo), clo <8= gres7.
Proof. intros. econstructor;[apply RES|apply PR]. Qed.

Lemma grespectful7_incl: forall r, r <7= gres7 r.
Proof.
  intros; eexists (fun x => x).
  - econstructor.
    + red; intros; apply LE, IN.
    + intros; apply GF, PR0.
  - apply PR.
Qed.
Hint Resolve grespectful7_incl.

Lemma grespectful7_compose: forall clo (RES: respectful7 clo) r,
    clo (gres7 r) <7= gres7 r.
Proof.
  intros; eapply grespectful7_greatest with (clo := compose clo gres7); [|apply PR].
  apply respectful7_compose; [apply RES|apply grespectful7_respectful7].
Qed.

Lemma grespectful7_incl_rev: forall r,
    gres7 (paco7 (compose gf gres7) r) <7= paco7 (compose gf gres7) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful7_compose, grespectful7_respectful7.
  destruct grespectful7_respectful7; eapply RESPECTFUL0, PR; intros; [apply grespectful7_incl; right; apply CIH, grespectful7_incl, PR0|].
  _punfold PR0; [|apply gfgres7_mon].
  eapply gfgres7_mon; [apply PR0|].
  intros; destruct PR1.
  - left. eapply paco7_mon; [apply H| apply CIH0].
  - right. eapply CIH0, H.
Qed.

Inductive rclo7 clo (r: rel): rel :=
| rclo7_incl
    e0 e1 e2 e3 e4 e5 e6
    (R: r e0 e1 e2 e3 e4 e5 e6):
    @rclo7 clo r e0 e1 e2 e3 e4 e5 e6
| rclo7_step'
    r' e0 e1 e2 e3 e4 e5 e6
    (R': r' <7= rclo7 clo r)
    (CLOR':clo r' e0 e1 e2 e3 e4 e5 e6):
    @rclo7 clo r e0 e1 e2 e3 e4 e5 e6
| rclo7_gf
    r' e0 e1 e2 e3 e4 e5 e6
    (R': r' <7= rclo7 clo r)
    (CLOR':@gf r' e0 e1 e2 e3 e4 e5 e6):
    @rclo7 clo r e0 e1 e2 e3 e4 e5 e6
.
Lemma rclo7_mon clo:
  monotone7 (rclo7 clo).
Proof.
  repeat intro. induction IN.
  - econstructor 1. apply LE, R.
  - econstructor 2; [intros; eapply H, PR| eapply CLOR'].
  - econstructor 3; [intros; eapply H, PR| eapply CLOR'].
Qed.
Hint Resolve rclo7_mon: paco.

Lemma rclo7_base
      clo
      (MON: monotone7 clo):
  clo <8= rclo7 clo.
Proof.
  intros. econstructor 2; [intros; apply PR0|].
  eapply MON; [apply PR|intros; constructor; apply PR0].
Qed.

Lemma rclo7_step
      (clo: rel -> rel) r:
  clo (rclo7 clo r) <7= rclo7 clo r.
Proof.
  intros. econstructor 2; [intros; apply PR0|apply PR].
Qed.

Lemma rclo7_rclo7
      clo r
      (MON: monotone7 clo):
  rclo7 clo (rclo7 clo r) <7= rclo7 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
Qed.

Structure weak_respectful7 (clo: rel -> rel) : Prop :=
  weak_respectful7_intro {
      WEAK_MON: monotone7 clo;
      WEAK_RESPECTFUL:
        forall l r (LE: l <7= r) (GF: l <7= gf r),
          clo l <7= gf (rclo7 clo r);
    }.
Hint Constructors weak_respectful7.

Lemma weak_respectful7_respectful7
      clo (RES: weak_respectful7 clo):
  respectful7 (rclo7 clo).
Proof.
  inversion RES. econstructor; [eapply rclo7_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply GF, R|]. intros.
    apply rclo7_incl. apply PR.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo7_mon; [apply R', PR|apply LE].
    + intros. apply rclo7_rclo7;[apply WEAK_MON0|apply PR].
  - eapply gf_mon; [apply CLOR'|].
    intros. eapply rclo7_mon; [apply R', PR| apply LE].
Qed.

Lemma upto7_init:
  paco7 (compose gf gres7) bot7 <7= paco7 gf bot7.
Proof.
  apply sound7_is_gf.
  apply respectful7_is_sound7.
  apply grespectful7_respectful7.
Qed.

Lemma upto7_final:
  paco7 gf <8= paco7 (compose gf gres7).
Proof.
  pcofix CIH. intros. _punfold PR; [|apply gf_mon]. pfold.
  eapply gf_mon; [|apply grespectful7_incl].
  eapply gf_mon; [apply PR|]. intros. right.
  inversion PR0; [apply CIH, H | apply CIH0, H].
Qed.

Lemma upto7_step
      r clo (RES: weak_respectful7 clo):
  clo (paco7 (compose gf gres7) r) <7= paco7 (compose gf gres7) r.
Proof.
  intros. apply grespectful7_incl_rev.
  assert (RES' := weak_respectful7_respectful7 RES).
  eapply grespectful7_greatest; [apply RES'|].
  eapply rclo7_base; [apply RES|].
  inversion RES. apply PR.
Qed.

Lemma upto7_step_under
      r clo (RES: weak_respectful7 clo):
  clo (gres7 r) <7= gres7 r.
Proof.
  intros. apply weak_respectful7_respectful7 in RES.
  eapply grespectful7_compose; [apply RES|].
  econstructor 2; [intros; constructor 1; apply PR0 | apply PR].
Qed.

End Respectful7.

Lemma grespectful7_impl T0 T1 T2 T3 T4 T5 T6 (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) r x0 x1 x2 x3 x4 x5 x6
    (PR: gres7 gf r x0 x1 x2 x3 x4 x5 x6)
    (EQ: forall r x0 x1 x2 x3 x4 x5 x6, gf r x0 x1 x2 x3 x4 x5 x6 <-> gf' r x0 x1 x2 x3 x4 x5 x6):
  gres7 gf' r x0 x1 x2 x3 x4 x5 x6.
Proof.
  intros. destruct PR. econstructor; [|apply CLO].
  destruct RES. econstructor; [apply MON0|].
  intros. rewrite <-EQ. eapply RESPECTFUL0; [apply LE| |apply PR].
  intros. rewrite EQ. apply GF, PR0.
Qed.

Lemma grespectful7_iff T0 T1 T2 T3 T4 T5 T6 (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) r x0 x1 x2 x3 x4 x5 x6
    (EQ: forall r x0 x1 x2 x3 x4 x5 x6, gf r x0 x1 x2 x3 x4 x5 x6 <-> gf' r x0 x1 x2 x3 x4 x5 x6):
  gres7 gf r x0 x1 x2 x3 x4 x5 x6 <-> gres7 gf' r x0 x1 x2 x3 x4 x5 x6.
Proof.
  split; intros.
  - eapply grespectful7_impl; [apply H | apply EQ].
  - eapply grespectful7_impl; [apply H | symmetry; apply EQ].
Qed.

Hint Constructors sound7.
Hint Constructors respectful7.
Hint Constructors gres7.
Hint Resolve gfclo7_mon : paco.
Hint Resolve gfgres7_mon : paco.
Hint Resolve grespectful7_incl.
Hint Resolve rclo7_mon: paco.
Hint Constructors weak_respectful7.

Ltac pupto7_init := eapply upto7_init; [eauto with paco|].
Ltac pupto7_final := first [eapply upto7_final; [eauto with paco|] | eapply grespectful7_incl].
Ltac pupto7 H := first [eapply upto7_step|eapply upto7_step_under]; [|eapply H|]; [eauto with paco|].

