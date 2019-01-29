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
  eapply (SOUND (paco5 (compose gf clo) bot5)); [|eauto].
  intros. punfold PR0.
  eapply (gfclo5_mon UPTO); eauto. intros. destruct PR1; eauto. contradiction.
Qed.

Lemma respectful5_is_sound5: respectful5 <1= sound5.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \5/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; eauto.
  intros. set (rr e0 e1 e2 e3 e4 := exists n, rclo clo n r e0 e1 e2 e3 e4).
  assert (rr x0 x1 x2 x3 x4) by (exists 0; eauto); clear PR.
  cut (forall n, rclo clo n r <5= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 x4 H; pcofix CIH; intros.
    unfold rr in *; destruct H0; eauto 10 using gf_mon. }
  induction n; intros; [simpl; eauto using gf_mon|].
  simpl in *; destruct PR; [eauto using gf_mon|].
  eapply gf_mon; [eapply RESPECTFUL0; [|apply IHn|]|]; instantiate; simpl; eauto.
Qed.

Lemma respectful5_compose
      clo0 clo1
      (RES0: respectful5 clo0)
      (RES1: respectful5 clo1):
  respectful5 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; eauto.
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; eauto.
    + intros. eapply RESPECTFUL1; eauto.
Qed.

Lemma grespectful5_respectful5: respectful5 gres5.
Proof.
  econstructor; repeat intro.
  - destruct IN; destruct RES; exists clo; eauto.
  - destruct PR; destruct RES; eapply gf_mon with (r:=clo r); eauto.
Qed.

Lemma gfgres5_mon: monotone5 (compose gf gres5).
Proof.
  destruct grespectful5_respectful5; eauto using gf_mon.
Qed.
Hint Resolve gfgres5_mon : paco.

Lemma grespectful5_greatest: forall clo (RES: respectful5 clo), clo <6= gres5.
Proof. eauto. Qed.

Lemma grespectful5_incl: forall r, r <5= gres5 r.
Proof.
  intros; eexists (fun x => x); eauto.
Qed.
Hint Resolve grespectful5_incl.

Lemma grespectful5_compose: forall clo (RES: respectful5 clo) r,
    clo (gres5 r) <5= gres5 r.
Proof.
  intros; eapply grespectful5_greatest with (clo := compose clo gres5);
    eauto using respectful5_compose, grespectful5_respectful5.
Qed.

Lemma grespectful5_incl_rev: forall r,
    gres5 (paco5 (compose gf gres5) r) <5= paco5 (compose gf gres5) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful5_compose, grespectful5_respectful5.
  destruct grespectful5_respectful5; eapply RESPECTFUL0, PR; intros; [apply grespectful5_incl; eauto|].
  punfold PR0.
  eapply gfgres5_mon; eauto; intros; destruct PR1; eauto.
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
  repeat intro. induction IN; eauto using rclo5.
Qed.
Hint Resolve rclo5_mon: paco.

Lemma rclo5_base
      clo
      (MON: monotone5 clo):
  clo <6= rclo5 clo.
Proof.
  simpl. intros. econstructor 2; eauto.
  eapply MON; eauto using rclo5.
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
  intros. induction PR; eauto using rclo5.
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
  inversion RES. econstructor; eauto with paco. intros.
  induction PR; intros.
  - eapply gf_mon; eauto. intros.
    apply rclo5_incl. auto.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo5_mon; eauto.
    + intros. apply rclo5_rclo5; auto.
  - eapply gf_mon; eauto using rclo5.
Qed.

Lemma upto5_init:
  paco5 (compose gf gres5) bot5 <5= paco5 gf bot5.
Proof.
  apply sound5_is_gf; eauto.
  apply respectful5_is_sound5.
  apply grespectful5_respectful5.
Qed.

Lemma upto5_final:
  paco5 gf <6= paco5 (compose gf gres5).
Proof.
  pcofix CIH. intros. punfold PR. pfold.
  eapply gf_mon; [|apply grespectful5_incl].
  eapply gf_mon; [eauto|]. intros. right. inversion PR0; auto.
Qed.

Lemma upto5_step
      r clo (RES: weak_respectful5 clo):
  clo (paco5 (compose gf gres5) r) <5= paco5 (compose gf gres5) r.
Proof.
  intros. apply grespectful5_incl_rev.
  assert (RES' := weak_respectful5_respectful5 RES).
  eapply grespectful5_greatest. eauto.
  eapply rclo5_base; eauto.
  inversion RES. auto.
Qed.

Lemma upto5_step_under
      r clo (RES: weak_respectful5 clo):
  clo (gres5 r) <5= gres5 r.
Proof.
  intros. apply weak_respectful5_respectful5 in RES; eauto.
  eapply grespectful5_compose; eauto. eauto using rclo5.
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

