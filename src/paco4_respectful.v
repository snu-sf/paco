Require Import paco4.
Require Export Program.
Set Implicit Arguments.

Section Respectful4.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.

Local Notation rel := (rel4 T0 T1 T2 T3).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone4 gf.

Inductive sound4 (clo: rel -> rel): Prop :=
| sound4_intro
    (MON: monotone4 clo)
    (SOUND:
       forall r (PFIX: r <4= gf (clo r)),
         r <4= paco4 gf bot4)
.
Hint Constructors sound4.

Structure respectful4 (clo: rel -> rel) : Prop :=
  respectful4_intro {
      MON: monotone4 clo;
      RESPECTFUL:
        forall l r (LE: l <4= r) (GF: l <4= gf r),
          clo l <4= gf (clo r);
    }.
Hint Constructors respectful4.

Inductive gres4 (r: rel) e0 e1 e2 e3 : Prop :=
| gres4_intro
    clo
    (RES: respectful4 clo)
    (CLO: clo r e0 e1 e2 e3)
.
Hint Constructors gres4.
Lemma gfclo4_mon: forall clo, sound4 clo -> monotone4 (compose gf clo).
Proof. intros; destruct H; eauto using gf_mon. Qed.
Hint Resolve gfclo4_mon : paco.

Lemma sound4_is_gf: forall clo (UPTO: sound4 clo),
    paco4 (compose gf clo) bot4 <4= paco4 gf bot4.
Proof.
  intros. punfold PR. edestruct UPTO.
  eapply (SOUND (paco4 (compose gf clo) bot4)); [|eauto].
  intros. punfold PR0.
  eapply (gfclo4_mon UPTO); eauto. intros. destruct PR1; eauto. contradiction.
Qed.

Lemma respectful4_is_sound4: respectful4 <1= sound4.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \4/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; eauto.
  intros. set (rr e0 e1 e2 e3 := exists n, rclo clo n r e0 e1 e2 e3).
  assert (rr x0 x1 x2 x3) by (exists 0; eauto); clear PR.
  cut (forall n, rclo clo n r <4= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 H; pcofix CIH; intros.
    unfold rr in *; destruct H0; eauto 10 using gf_mon. }
  induction n; intros; [simpl; eauto using gf_mon|].
  simpl in *; destruct PR; [eauto using gf_mon|].
  eapply gf_mon; [eapply RESPECTFUL0; [|apply IHn|]|]; instantiate; simpl; eauto.
Qed.

Lemma respectful4_compose
      clo0 clo1
      (RES0: respectful4 clo0)
      (RES1: respectful4 clo1):
  respectful4 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; eauto.
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; eauto.
    + intros. eapply RESPECTFUL1; eauto.
Qed.

Lemma grespectful4_respectful4: respectful4 gres4.
Proof.
  econstructor; repeat intro.
  - destruct IN; destruct RES; exists clo; eauto.
  - destruct PR; destruct RES; eapply gf_mon with (r:=clo r); eauto.
Qed.

Lemma gfgres4_mon: monotone4 (compose gf gres4).
Proof.
  destruct grespectful4_respectful4; eauto using gf_mon.
Qed.
Hint Resolve gfgres4_mon : paco.

Lemma grespectful4_greatest: forall clo (RES: respectful4 clo), clo <5= gres4.
Proof. eauto. Qed.

Lemma grespectful4_incl: forall r, r <4= gres4 r.
Proof.
  intros; eexists (fun x => x); eauto.
Qed.
Hint Resolve grespectful4_incl.

Lemma grespectful4_compose: forall clo (RES: respectful4 clo) r,
    clo (gres4 r) <4= gres4 r.
Proof.
  intros; eapply grespectful4_greatest with (clo := compose clo gres4);
    eauto using respectful4_compose, grespectful4_respectful4.
Qed.

Lemma grespectful4_incl_rev: forall r,
    gres4 (paco4 (compose gf gres4) r) <4= paco4 (compose gf gres4) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful4_compose, grespectful4_respectful4.
  destruct grespectful4_respectful4; eapply RESPECTFUL0, PR; intros; [apply grespectful4_incl; eauto|].
  punfold PR0.
  eapply gfgres4_mon; eauto; intros; destruct PR1; eauto.
Qed.

Inductive rclo4 clo (r: rel): rel :=
| rclo4_incl
    e0 e1 e2 e3
    (R: r e0 e1 e2 e3):
    @rclo4 clo r e0 e1 e2 e3
| rclo4_step'
    r' e0 e1 e2 e3
    (R': r' <4= rclo4 clo r)
    (CLOR':clo r' e0 e1 e2 e3):
    @rclo4 clo r e0 e1 e2 e3
| rclo4_gf
    r' e0 e1 e2 e3
    (R': r' <4= rclo4 clo r)
    (CLOR':@gf r' e0 e1 e2 e3):
    @rclo4 clo r e0 e1 e2 e3
.
Lemma rclo4_mon clo:
  monotone4 (rclo4 clo).
Proof.
  repeat intro. induction IN; eauto using rclo4.
Qed.
Hint Resolve rclo4_mon: paco.

Lemma rclo4_base
      clo
      (MON: monotone4 clo):
  clo <5= rclo4 clo.
Proof.
  simpl. intros. econstructor 2; eauto.
  eapply MON; eauto using rclo4.
Qed.

Lemma rclo4_step
      (clo: rel -> rel) r:
  clo (rclo4 clo r) <4= rclo4 clo r.
Proof.
  intros. econstructor 2; eauto.
Qed.

Lemma rclo4_rclo4
      clo r
      (MON: monotone4 clo):
  rclo4 clo (rclo4 clo r) <4= rclo4 clo r.
Proof.
  intros. induction PR; eauto using rclo4.
Qed.

Structure weak_respectful4 (clo: rel -> rel) : Prop :=
  weak_respectful4_intro {
      WEAK_MON: monotone4 clo;
      WEAK_RESPECTFUL:
        forall l r (LE: l <4= r) (GF: l <4= gf r),
          clo l <4= gf (rclo4 clo r);
    }.
Hint Constructors weak_respectful4.

Lemma weak_respectful4_respectful4
      clo (RES: weak_respectful4 clo):
  respectful4 (rclo4 clo).
Proof.
  inversion RES. econstructor; eauto with paco. intros.
  induction PR; intros.
  - eapply gf_mon; eauto. intros.
    apply rclo4_incl. auto.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo4_mon; eauto.
    + intros. apply rclo4_rclo4; auto.
  - eapply gf_mon; eauto using rclo4.
Qed.

Lemma upto4_init:
  paco4 (compose gf gres4) bot4 <4= paco4 gf bot4.
Proof.
  apply sound4_is_gf; eauto.
  apply respectful4_is_sound4.
  apply grespectful4_respectful4.
Qed.

Lemma upto4_final:
  paco4 gf <5= paco4 (compose gf gres4).
Proof.
  pcofix CIH. intros. punfold PR. pfold.
  eapply gf_mon; [|apply grespectful4_incl].
  eapply gf_mon; [eauto|]. intros. right. inversion PR0; auto.
Qed.

Lemma upto4_step
      r clo (RES: weak_respectful4 clo):
  clo (paco4 (compose gf gres4) r) <4= paco4 (compose gf gres4) r.
Proof.
  intros. apply grespectful4_incl_rev.
  assert (RES' := weak_respectful4_respectful4 RES).
  eapply grespectful4_greatest. eauto.
  eapply rclo4_base; eauto.
  inversion RES. auto.
Qed.

Lemma upto4_step_under
      r clo (RES: weak_respectful4 clo):
  clo (gres4 r) <4= gres4 r.
Proof.
  intros. apply weak_respectful4_respectful4 in RES; eauto.
  eapply grespectful4_compose; eauto. eauto using rclo4.
Qed.

End Respectful4.

Hint Constructors sound4.
Hint Constructors respectful4.
Hint Constructors gres4.
Hint Resolve gfclo4_mon : paco.
Hint Resolve gfgres4_mon : paco.
Hint Resolve grespectful4_incl.
Hint Resolve rclo4_mon: paco.
Hint Constructors weak_respectful4.

Ltac pupto4_init := eapply upto4_init; eauto with paco.
Ltac pupto4_final := first [eapply upto4_final; eauto with paco | eapply grespectful4_incl].
Ltac pupto4 H := first [eapply upto4_step|eapply upto4_step_under]; [|eapply H|]; eauto with paco.

