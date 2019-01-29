Require Import paco3.
Require Export Program.
Set Implicit Arguments.

Section Respectful3.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.

Local Notation rel := (rel3 T0 T1 T2).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone3 gf.

Inductive sound3 (clo: rel -> rel): Prop :=
| sound3_intro
    (MON: monotone3 clo)
    (SOUND:
       forall r (PFIX: r <3= gf (clo r)),
         r <3= paco3 gf bot3)
.
Hint Constructors sound3.

Structure respectful3 (clo: rel -> rel) : Prop :=
  respectful3_intro {
      MON: monotone3 clo;
      RESPECTFUL:
        forall l r (LE: l <3= r) (GF: l <3= gf r),
          clo l <3= gf (clo r);
    }.
Hint Constructors respectful3.

Inductive gres3 (r: rel) e0 e1 e2 : Prop :=
| gres3_intro
    clo
    (RES: respectful3 clo)
    (CLO: clo r e0 e1 e2)
.
Hint Constructors gres3.
Lemma gfclo3_mon: forall clo, sound3 clo -> monotone3 (compose gf clo).
Proof. intros; destruct H; eauto using gf_mon. Qed.
Hint Resolve gfclo3_mon : paco.

Lemma sound3_is_gf: forall clo (UPTO: sound3 clo),
    paco3 (compose gf clo) bot3 <3= paco3 gf bot3.
Proof.
  intros. punfold PR. edestruct UPTO.
  eapply (SOUND (paco3 (compose gf clo) bot3)); [|eauto].
  intros. punfold PR0.
  eapply (gfclo3_mon UPTO); eauto. intros. destruct PR1; eauto. contradiction.
Qed.

Lemma respectful3_is_sound3: respectful3 <1= sound3.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \3/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; eauto.
  intros. set (rr e0 e1 e2 := exists n, rclo clo n r e0 e1 e2).
  assert (rr x0 x1 x2) by (exists 0; eauto); clear PR.
  cut (forall n, rclo clo n r <3= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 H; pcofix CIH; intros.
    unfold rr in *; destruct H0; eauto 10 using gf_mon. }
  induction n; intros; [simpl; eauto using gf_mon|].
  simpl in *; destruct PR; [eauto using gf_mon|].
  eapply gf_mon; [eapply RESPECTFUL0; [|apply IHn|]|]; instantiate; simpl; eauto.
Qed.

Lemma respectful3_compose
      clo0 clo1
      (RES0: respectful3 clo0)
      (RES1: respectful3 clo1):
  respectful3 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; eauto.
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; eauto.
    + intros. eapply RESPECTFUL1; eauto.
Qed.

Lemma grespectful3_respectful3: respectful3 gres3.
Proof.
  econstructor; repeat intro.
  - destruct IN; destruct RES; exists clo; eauto.
  - destruct PR; destruct RES; eapply gf_mon with (r:=clo r); eauto.
Qed.

Lemma gfgres3_mon: monotone3 (compose gf gres3).
Proof.
  destruct grespectful3_respectful3; eauto using gf_mon.
Qed.
Hint Resolve gfgres3_mon : paco.

Lemma grespectful3_greatest: forall clo (RES: respectful3 clo), clo <4= gres3.
Proof. eauto. Qed.

Lemma grespectful3_incl: forall r, r <3= gres3 r.
Proof.
  intros; eexists (fun x => x); eauto.
Qed.
Hint Resolve grespectful3_incl.

Lemma grespectful3_compose: forall clo (RES: respectful3 clo) r,
    clo (gres3 r) <3= gres3 r.
Proof.
  intros; eapply grespectful3_greatest with (clo := compose clo gres3);
    eauto using respectful3_compose, grespectful3_respectful3.
Qed.

Lemma grespectful3_incl_rev: forall r,
    gres3 (paco3 (compose gf gres3) r) <3= paco3 (compose gf gres3) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful3_compose, grespectful3_respectful3.
  destruct grespectful3_respectful3; eapply RESPECTFUL0, PR; intros; [apply grespectful3_incl; eauto|].
  punfold PR0.
  eapply gfgres3_mon; eauto; intros; destruct PR1; eauto.
Qed.

Inductive rclo3 clo (r: rel): rel :=
| rclo3_incl
    e0 e1 e2
    (R: r e0 e1 e2):
    @rclo3 clo r e0 e1 e2
| rclo3_step'
    r' e0 e1 e2
    (R': r' <3= rclo3 clo r)
    (CLOR':clo r' e0 e1 e2):
    @rclo3 clo r e0 e1 e2
| rclo3_gf
    r' e0 e1 e2
    (R': r' <3= rclo3 clo r)
    (CLOR':@gf r' e0 e1 e2):
    @rclo3 clo r e0 e1 e2
.
Lemma rclo3_mon clo:
  monotone3 (rclo3 clo).
Proof.
  repeat intro. induction IN; eauto using rclo3.
Qed.
Hint Resolve rclo3_mon: paco.

Lemma rclo3_base
      clo
      (MON: monotone3 clo):
  clo <4= rclo3 clo.
Proof.
  simpl. intros. econstructor 2; eauto.
  eapply MON; eauto using rclo3.
Qed.

Lemma rclo3_step
      (clo: rel -> rel) r:
  clo (rclo3 clo r) <3= rclo3 clo r.
Proof.
  intros. econstructor 2; eauto.
Qed.

Lemma rclo3_rclo3
      clo r
      (MON: monotone3 clo):
  rclo3 clo (rclo3 clo r) <3= rclo3 clo r.
Proof.
  intros. induction PR; eauto using rclo3.
Qed.

Structure weak_respectful3 (clo: rel -> rel) : Prop :=
  weak_respectful3_intro {
      WEAK_MON: monotone3 clo;
      WEAK_RESPECTFUL:
        forall l r (LE: l <3= r) (GF: l <3= gf r),
          clo l <3= gf (rclo3 clo r);
    }.
Hint Constructors weak_respectful3.

Lemma weak_respectful3_respectful3
      clo (RES: weak_respectful3 clo):
  respectful3 (rclo3 clo).
Proof.
  inversion RES. econstructor; eauto with paco. intros.
  induction PR; intros.
  - eapply gf_mon; eauto. intros.
    apply rclo3_incl. auto.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo3_mon; eauto.
    + intros. apply rclo3_rclo3; auto.
  - eapply gf_mon; eauto using rclo3.
Qed.

Lemma upto3_init:
  paco3 (compose gf gres3) bot3 <3= paco3 gf bot3.
Proof.
  apply sound3_is_gf; eauto.
  apply respectful3_is_sound3.
  apply grespectful3_respectful3.
Qed.

Lemma upto3_final:
  paco3 gf <4= paco3 (compose gf gres3).
Proof.
  pcofix CIH. intros. punfold PR. pfold.
  eapply gf_mon; [|apply grespectful3_incl].
  eapply gf_mon; [eauto|]. intros. right. inversion PR0; auto.
Qed.

Lemma upto3_step
      r clo (RES: weak_respectful3 clo):
  clo (paco3 (compose gf gres3) r) <3= paco3 (compose gf gres3) r.
Proof.
  intros. apply grespectful3_incl_rev.
  assert (RES' := weak_respectful3_respectful3 RES).
  eapply grespectful3_greatest. eauto.
  eapply rclo3_base; eauto.
  inversion RES. auto.
Qed.

Lemma upto3_step_under
      r clo (RES: weak_respectful3 clo):
  clo (gres3 r) <3= gres3 r.
Proof.
  intros. apply weak_respectful3_respectful3 in RES; eauto.
  eapply grespectful3_compose; eauto. eauto using rclo3.
Qed.

End Respectful3.

Hint Constructors sound3.
Hint Constructors respectful3.
Hint Constructors gres3.
Hint Resolve gfclo3_mon : paco.
Hint Resolve gfgres3_mon : paco.
Hint Resolve grespectful3_incl.
Hint Resolve rclo3_mon: paco.
Hint Constructors weak_respectful3.

Ltac pupto3_init := eapply upto3_init; eauto with paco.
Ltac pupto3_final := first [eapply upto3_final; eauto with paco | eapply grespectful3_incl].
Ltac pupto3 H := first [eapply upto3_step|eapply upto3_step_under]; [|eapply H|]; eauto with paco.

