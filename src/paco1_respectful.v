Require Import paco1.
Require Export Program.
Set Implicit Arguments.

Section Respectful1.

Variable T0 : Type.

Local Notation rel := (rel1 T0).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone1 gf.

Inductive sound1 (clo: rel -> rel): Prop :=
| sound1_intro
    (MON: monotone1 clo)
    (SOUND:
       forall r (PFIX: r <1= gf (clo r)),
         r <1= paco1 gf bot1)
.
Hint Constructors sound1.

Structure respectful1 (clo: rel -> rel) : Prop :=
  respectful1_intro {
      MON: monotone1 clo;
      RESPECTFUL:
        forall l r (LE: l <1= r) (GF: l <1= gf r),
          clo l <1= gf (clo r);
    }.
Hint Constructors respectful1.

Inductive gres1 (r: rel) e0 : Prop :=
| gres1_intro
    clo
    (RES: respectful1 clo)
    (CLO: clo r e0)
.
Hint Constructors gres1.
Lemma gfclo1_mon: forall clo, sound1 clo -> monotone1 (compose gf clo).
Proof. intros; destruct H; eauto using gf_mon. Qed.
Hint Resolve gfclo1_mon : paco.

Lemma sound1_is_gf: forall clo (UPTO: sound1 clo),
    paco1 (compose gf clo) bot1 <1= paco1 gf bot1.
Proof.
  intros. punfold PR. edestruct UPTO.
  eapply (SOUND (paco1 (compose gf clo) bot1)); [|eauto].
  intros. punfold PR0.
  eapply (gfclo1_mon UPTO); eauto. intros. destruct PR1; eauto. contradiction.
Qed.

Lemma respectful1_is_sound1: respectful1 <1= sound1.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \1/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; eauto.
  intros. set (rr e0 := exists n, rclo clo n r e0).
  assert (rr x0) by (exists 0; eauto); clear PR.
  cut (forall n, rclo clo n r <1= gf (rclo clo (S n) r)).
  { intro X; revert x0 H; pcofix CIH; intros.
    unfold rr in *; destruct H0; eauto 10 using gf_mon. }
  induction n; intros; [simpl; eauto using gf_mon|].
  simpl in *; destruct PR; [eauto using gf_mon|].
  eapply gf_mon; [eapply RESPECTFUL0; [|apply IHn|]|]; instantiate; simpl; eauto.
Qed.

Lemma respectful1_compose
      clo0 clo1
      (RES0: respectful1 clo0)
      (RES1: respectful1 clo1):
  respectful1 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; eauto.
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; eauto.
    + intros. eapply RESPECTFUL1; eauto.
Qed.

Lemma grespectful1_respectful1: respectful1 gres1.
Proof.
  econstructor; repeat intro.
  - destruct IN; destruct RES; exists clo; eauto.
  - destruct PR; destruct RES; eapply gf_mon with (r:=clo r); eauto.
Qed.

Lemma gfgres1_mon: monotone1 (compose gf gres1).
Proof.
  destruct grespectful1_respectful1; eauto using gf_mon.
Qed.
Hint Resolve gfgres1_mon : paco.

Lemma grespectful1_greatest: forall clo (RES: respectful1 clo), clo <2= gres1.
Proof. eauto. Qed.

Lemma grespectful1_incl: forall r, r <1= gres1 r.
Proof.
  intros; eexists (fun x => x); eauto.
Qed.
Hint Resolve grespectful1_incl.

Lemma grespectful1_compose: forall clo (RES: respectful1 clo) r,
    clo (gres1 r) <1= gres1 r.
Proof.
  intros; eapply grespectful1_greatest with (clo := compose clo gres1);
    eauto using respectful1_compose, grespectful1_respectful1.
Qed.

Lemma grespectful1_incl_rev: forall r,
    gres1 (paco1 (compose gf gres1) r) <1= paco1 (compose gf gres1) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful1_compose, grespectful1_respectful1.
  destruct grespectful1_respectful1; eapply RESPECTFUL0, PR; intros; [apply grespectful1_incl; eauto|].
  punfold PR0.
  eapply gfgres1_mon; eauto; intros; destruct PR1; eauto.
Qed.

Inductive rclo1 clo (r: rel): rel :=
| rclo1_incl
    e0
    (R: r e0):
    @rclo1 clo r e0
| rclo1_step'
    r' e0
    (R': r' <1= rclo1 clo r)
    (CLOR':clo r' e0):
    @rclo1 clo r e0
| rclo1_gf
    r' e0
    (R': r' <1= rclo1 clo r)
    (CLOR':@gf r' e0):
    @rclo1 clo r e0
.
Lemma rclo1_mon clo:
  monotone1 (rclo1 clo).
Proof.
  repeat intro. induction IN; eauto using rclo1.
Qed.
Hint Resolve rclo1_mon: paco.

Lemma rclo1_base
      clo
      (MON: monotone1 clo):
  clo <2= rclo1 clo.
Proof.
  simpl. intros. econstructor 2; eauto.
  eapply MON; eauto using rclo1.
Qed.

Lemma rclo1_step
      (clo: rel -> rel) r:
  clo (rclo1 clo r) <1= rclo1 clo r.
Proof.
  intros. econstructor 2; eauto.
Qed.

Lemma rclo1_rclo1
      clo r
      (MON: monotone1 clo):
  rclo1 clo (rclo1 clo r) <1= rclo1 clo r.
Proof.
  intros. induction PR; eauto using rclo1.
Qed.

Structure weak_respectful1 (clo: rel -> rel) : Prop :=
  weak_respectful1_intro {
      WEAK_MON: monotone1 clo;
      WEAK_RESPECTFUL:
        forall l r (LE: l <1= r) (GF: l <1= gf r),
          clo l <1= gf (rclo1 clo r);
    }.
Hint Constructors weak_respectful1.

Lemma weak_respectful1_respectful1
      clo (RES: weak_respectful1 clo):
  respectful1 (rclo1 clo).
Proof.
  inversion RES. econstructor; eauto with paco. intros.
  induction PR; intros.
  - eapply gf_mon; eauto. intros.
    apply rclo1_incl. auto.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo1_mon; eauto.
    + intros. apply rclo1_rclo1; auto.
  - eapply gf_mon; eauto using rclo1.
Qed.

Lemma upto1_init:
  paco1 (compose gf gres1) bot1 <1= paco1 gf bot1.
Proof.
  apply sound1_is_gf; eauto.
  apply respectful1_is_sound1.
  apply grespectful1_respectful1.
Qed.

Lemma upto1_final:
  paco1 gf <2= paco1 (compose gf gres1).
Proof.
  pcofix CIH. intros. punfold PR. pfold.
  eapply gf_mon; [|apply grespectful1_incl].
  eapply gf_mon; [eauto|]. intros. right. inversion PR0; auto.
Qed.

Lemma upto1_step
      r clo (RES: weak_respectful1 clo):
  clo (paco1 (compose gf gres1) r) <1= paco1 (compose gf gres1) r.
Proof.
  intros. apply grespectful1_incl_rev.
  assert (RES' := weak_respectful1_respectful1 RES).
  eapply grespectful1_greatest. eauto.
  eapply rclo1_base; eauto.
  inversion RES. auto.
Qed.

Lemma upto1_step_under
      r clo (RES: weak_respectful1 clo):
  clo (gres1 r) <1= gres1 r.
Proof.
  intros. apply weak_respectful1_respectful1 in RES; eauto.
  eapply grespectful1_compose; eauto. eauto using rclo1.
Qed.

End Respectful1.

Hint Constructors sound1.
Hint Constructors respectful1.
Hint Constructors gres1.
Hint Resolve gfclo1_mon : paco.
Hint Resolve gfgres1_mon : paco.
Hint Resolve grespectful1_incl.
Hint Resolve rclo1_mon: paco.
Hint Constructors weak_respectful1.

Ltac pupto1_init := eapply upto1_init; eauto with paco.
Ltac pupto1_final := first [eapply upto1_final; eauto with paco | eapply grespectful1_incl].
Ltac pupto1 H := first [eapply upto1_step|eapply upto1_step_under]; [|eapply H|]; eauto with paco.

