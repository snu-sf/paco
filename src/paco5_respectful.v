Require Import paco5.
Require Export Program.
Set Implicit Arguments.

Section Respectful5.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.

Local Notation rel := (rel5 T0 T1 T2 T3 T4).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone5 gf.

Inductive sound5 (clo: rel -> rel): Prop :=
| sound5_intro
    (MON: monotone5 clo)
    (SOUND:
       forall r (PFIX: r <5= gf (clo r)),
         r <5= paco5 gf bot5)
.
Hint Constructors sound5.

Structure respectful5 (clo: rel -> rel) : Prop :=
  respectful5_intro {
      MON: monotone5 clo;
      RESPECTFUL:
        forall l r (LE: l <5= r) (GF: l <5= gf r),
          clo l <5= gf (clo r);
    }.
Hint Constructors respectful5.

Inductive gres5 (r: rel) e0 e1 e2 e3 e4 : Prop :=
| gres5_intro
    clo
    (RES: respectful5 clo)
    (CLO: clo r e0 e1 e2 e3 e4)
.
Hint Constructors gres5.
Lemma gfclo5_mon: forall clo, sound5 clo -> monotone5 (compose gf clo).
Proof. intros; destruct H; eauto using gf_mon. Qed.
Hint Resolve gfclo5_mon : paco.

Lemma sound5_is_gf: forall clo (UPTO: sound5 clo),
    paco5 (compose gf clo) bot5 <5= paco5 gf bot5.
Proof.
  intros. punfold PR. edestruct UPTO.
  eapply (SOUND (paco5 (compose gf clo) bot5)).
  - intros. punfold PR0.
    eapply (gfclo5_mon UPTO); [apply PR0| intros; destruct PR1; [apply H|destruct H]].
  - pfold. apply PR.
Qed.

Lemma respectful5_is_sound5: respectful5 <1= sound5.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \5/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; [apply MON0|].
  intros. set (rr e0 e1 e2 e3 e4 := exists n, rclo clo n r e0 e1 e2 e3 e4).
  assert (rr x0 x1 x2 x3 x4) by (exists 0; apply PR); clear PR.
  cut (forall n, rclo clo n r <5= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 x4 H; pcofix CIH; intros.
    unfold rr in *; destruct H0.
    pfold. eapply gf_mon.
    - apply X. apply H.
    - intros. right. apply CIH. exists (S x). apply PR.
  }
  induction n; intros; simpl in *.
  - eapply gf_mon.
    + clear RESPECTFUL0. eapply PFIX, PR.
    + intros. right. eapply PR0.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H0|]. intros. clear - PR. auto.
    + eapply gf_mon; [eapply RESPECTFUL0; [|apply IHn|]|]; instantiate; simpl; auto.
Qed.

Lemma respectful5_compose
      clo0 clo1
      (RES0: respectful5 clo0)
      (RES1: respectful5 clo1):
  respectful5 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; [apply IN|].
    intros. eapply MON1; [apply PR|apply LE].
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; [apply PR0|apply LE].
    + intros. eapply RESPECTFUL1; [apply LE| apply GF| apply PR0].
Qed.

Lemma grespectful5_respectful5: respectful5 gres5.
Proof.
  econstructor; repeat intro.
  - destruct IN; destruct RES; exists clo; [|eapply MON0; [eapply CLO| eapply LE]].
    constructor; [eapply MON0|].
    intros. eapply RESPECTFUL0; [apply LE0|apply GF|apply PR].
  - destruct PR; destruct RES; eapply gf_mon with (r:=clo r).
    eapply RESPECTFUL0; [apply LE|apply GF|apply CLO].
    intros. econstructor; [constructor; [apply MON0|apply RESPECTFUL0]|apply PR].
Qed.

Lemma gfgres5_mon: monotone5 (compose gf gres5).
Proof.
  destruct grespectful5_respectful5.
  unfold monotone5. intros. eapply gf_mon; [eapply IN|].
  intros. eapply MON0;[apply PR|apply LE].
Qed.
Hint Resolve gfgres5_mon : paco.

Lemma grespectful5_greatest: forall clo (RES: respectful5 clo), clo <6= gres5.
Proof. intros. econstructor;[apply RES|apply PR]. Qed.

Lemma grespectful5_incl: forall r, r <5= gres5 r.
Proof.
  intros; eexists (fun x => x); eauto.
Qed.
Hint Resolve grespectful5_incl.

Lemma grespectful5_compose: forall clo (RES: respectful5 clo) r,
    clo (gres5 r) <5= gres5 r.
Proof.
  intros; eapply grespectful5_greatest with (clo := compose clo gres5); [|apply PR].
  apply respectful5_compose; [apply RES|apply grespectful5_respectful5].
Qed.

Lemma grespectful5_incl_rev: forall r,
    gres5 (paco5 (compose gf gres5) r) <5= paco5 (compose gf gres5) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful5_compose, grespectful5_respectful5.
  destruct grespectful5_respectful5; eapply RESPECTFUL0, PR; intros; [apply grespectful5_incl; auto|].
  punfold PR0.
  eapply gfgres5_mon; [apply PR0|].
  intros; destruct PR1.
  - left. eapply paco5_mon; [apply H| apply CIH0].
  - right. eapply CIH0, H.
Qed.

Inductive rclo5 clo (r: rel): rel :=
| rclo5_incl
    e0 e1 e2 e3 e4
    (R: r e0 e1 e2 e3 e4):
    @rclo5 clo r e0 e1 e2 e3 e4
| rclo5_step'
    r' e0 e1 e2 e3 e4
    (R': r' <5= rclo5 clo r)
    (CLOR':clo r' e0 e1 e2 e3 e4):
    @rclo5 clo r e0 e1 e2 e3 e4
| rclo5_gf
    r' e0 e1 e2 e3 e4
    (R': r' <5= rclo5 clo r)
    (CLOR':@gf r' e0 e1 e2 e3 e4):
    @rclo5 clo r e0 e1 e2 e3 e4
.
Lemma rclo5_mon clo:
  monotone5 (rclo5 clo).
Proof.
  repeat intro. induction IN.
  - econstructor 1. apply LE, R.
  - econstructor 2; [intros; eapply H, PR| eapply CLOR'].
  - econstructor 3; [intros; eapply H, PR| eapply CLOR'].
Qed.

Lemma rclo5_base
      clo
      (MON: monotone5 clo):
  clo <6= rclo5 clo.
Proof.
  simpl. intros. econstructor 2; [eauto|].
  eapply MON; [apply PR|intros; constructor; apply PR0].
Qed.

Lemma rclo5_step
      (clo: rel -> rel) r:
  clo (rclo5 clo r) <5= rclo5 clo r.
Proof.
  intros. econstructor 2; eauto.
Qed.

Lemma rclo5_rclo5
      clo r
      (MON: monotone5 clo):
  rclo5 clo (rclo5 clo r) <5= rclo5 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
Qed.

Structure weak_respectful5 (clo: rel -> rel) : Prop :=
  weak_respectful5_intro {
      WEAK_MON: monotone5 clo;
      WEAK_RESPECTFUL:
        forall l r (LE: l <5= r) (GF: l <5= gf r),
          clo l <5= gf (rclo5 clo r);
    }.
Hint Constructors weak_respectful5.

Lemma weak_respectful5_respectful5
      clo (RES: weak_respectful5 clo):
  respectful5 (rclo5 clo).
Proof.
  inversion RES. econstructor; [eapply rclo5_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply GF, R|]. intros.
    apply rclo5_incl. apply PR.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo5_mon; [apply R', PR|apply LE].
    + intros. apply rclo5_rclo5;[apply WEAK_MON0|apply PR].
  - eapply gf_mon; [apply CLOR'|].
    intros. eapply rclo5_mon; [apply R', PR| apply LE].
Qed.

Lemma upto5_init:
  paco5 (compose gf gres5) bot5 <5= paco5 gf bot5.
Proof.
  apply sound5_is_gf.
  apply respectful5_is_sound5.
  apply grespectful5_respectful5.
Qed.

Lemma upto5_final:
  paco5 gf <6= paco5 (compose gf gres5).
Proof.
  pcofix CIH. intros. punfold PR. pfold.
  eapply gf_mon; [|apply grespectful5_incl].
  eapply gf_mon; [apply PR|]. intros. right.
  inversion PR0; [apply CIH, H | apply CIH0, H].
Qed.

Lemma upto5_step
      r clo (RES: weak_respectful5 clo):
  clo (paco5 (compose gf gres5) r) <5= paco5 (compose gf gres5) r.
Proof.
  intros. apply grespectful5_incl_rev.
  assert (RES' := weak_respectful5_respectful5 RES).
  eapply grespectful5_greatest; [apply RES'|].
  eapply rclo5_base; [apply RES|].
  inversion RES. apply PR.
Qed.

Lemma upto5_step_under
      r clo (RES: weak_respectful5 clo):
  clo (gres5 r) <5= gres5 r.
Proof.
  intros. apply weak_respectful5_respectful5 in RES.
  eapply grespectful5_compose; [apply RES|].
  econstructor 2; [intros; constructor 1; apply PR0 | apply PR].
Qed.

End Respectful5.

Hint Constructors sound5.
Hint Constructors respectful5.
Hint Constructors gres5.
Hint Resolve gfclo5_mon : paco.
Hint Resolve gfgres5_mon : paco.
Hint Resolve grespectful5_incl.
Hint Resolve rclo5_mon: paco.
Hint Constructors weak_respectful5.

Ltac pupto5_init := eapply upto5_init; eauto with paco.
Ltac pupto5_final := first [eapply upto5_final; eauto with paco | eapply grespectful5_incl].
Ltac pupto5 H := first [eapply upto5_step|eapply upto5_step_under]; [|eapply H|]; eauto with paco.

