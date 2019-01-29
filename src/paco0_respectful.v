Require Import paco0.
Require Export Program.
Set Implicit Arguments.

Section Respectful0.


Local Notation rel := (rel0).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone0 gf.

Inductive sound0 (clo: rel -> rel): Prop :=
| sound0_intro
    (MON: monotone0 clo)
    (SOUND:
       forall r (PFIX: r <0= gf (clo r)),
         r <0= paco0 gf bot0)
.
Hint Constructors sound0.

Structure respectful0 (clo: rel -> rel) : Prop :=
  respectful0_intro {
      MON: monotone0 clo;
      RESPECTFUL:
        forall l r (LE: l <0= r) (GF: l <0= gf r),
          clo l <0= gf (clo r);
    }.
Hint Constructors respectful0.

Inductive gres0 (r: rel) : Prop :=
| gres0_intro
    clo
    (RES: respectful0 clo)
    (CLO: clo r)
.
Hint Constructors gres0.
Lemma gfclo0_mon: forall clo, sound0 clo -> monotone0 (compose gf clo).
Proof. intros; destruct H; eauto using gf_mon. Qed.
Hint Resolve gfclo0_mon : paco.

Lemma sound0_is_gf: forall clo (UPTO: sound0 clo),
    paco0 (compose gf clo) bot0 <0= paco0 gf bot0.
Proof.
  intros. punfold PR. edestruct UPTO.
  eapply (SOUND (paco0 (compose gf clo) bot0)); [|eauto].
  intros. punfold PR0.

Qed.

Lemma respectful0_is_sound0: respectful0 <1= sound0.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \0/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; eauto.
  intros. set (rr := exists n, rclo clo n r).
  assert (rr) by (exists 0; eauto); clear PR.
  cut (forall n, rclo clo n r <0= gf (rclo clo (S n) r)).
  { intro X; revert H; pcofix CIH; intros.
    unfold rr in *; destruct H0; eauto 10 using gf_mon. }
  induction n; intros; [simpl; eauto using gf_mon|].
  simpl in *; destruct PR; [eauto using gf_mon|].
  eapply gf_mon; [eapply RESPECTFUL0; [|apply IHn|]|]; instantiate; simpl; eauto.
Qed.

Lemma respectful0_compose
      clo0 clo1
      (RES0: respectful0 clo0)
      (RES1: respectful0 clo1):
  respectful0 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; eauto.
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; eauto.
    + intros. eapply RESPECTFUL1; eauto.
Qed.

Lemma grespectful0_respectful0: respectful0 gres0.
Proof.
  econstructor; repeat intro.
  - destruct IN; destruct RES; exists clo; eauto.
  - destruct PR; destruct RES; eapply gf_mon with (r:=clo r); eauto.
Qed.

Lemma gfgres0_mon: monotone0 (compose gf gres0).
Proof.
  destruct grespectful0_respectful0; eauto using gf_mon.
Qed.
Hint Resolve gfgres0_mon : paco.

Lemma grespectful0_greatest: forall clo (RES: respectful0 clo), clo <1= gres0.
Proof. eauto. Qed.

Lemma grespectful0_incl: forall r, r <0= gres0 r.
Proof.
  intros; eexists (fun x => x); eauto.
Qed.
Hint Resolve grespectful0_incl.

Lemma grespectful0_compose: forall clo (RES: respectful0 clo) r,
    clo (gres0 r) <0= gres0 r.
Proof.
  intros; eapply grespectful0_greatest with (clo := compose clo gres0);
    eauto using respectful0_compose, grespectful0_respectful0.
Qed.

Lemma grespectful0_incl_rev: forall r,
    gres0 (paco0 (compose gf gres0) r) <0= paco0 (compose gf gres0) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful0_compose, grespectful0_respectful0.
  destruct grespectful0_respectful0; eapply RESPECTFUL0, PR; intros; [apply grespectful0_incl; eauto|].
  punfold PR0.
  eapply gfgres0_mon; eauto; intros; destruct PR1; eauto.
Qed.

Inductive rclo0 clo (r: rel): rel :=
| rclo0_incl
   
    (R: r):
    @rclo0 clo r
| rclo0_step'
    r'
    (R': r' <0= rclo0 clo r)
    (CLOR':clo r'):
    @rclo0 clo r
| rclo0_gf
    r'
    (R': r' <0= rclo0 clo r)
    (CLOR':@gf r'):
    @rclo0 clo r
.
Lemma rclo0_mon clo:
  monotone0 (rclo0 clo).
Proof.
  repeat intro. induction IN; eauto using rclo0.
Qed.
Hint Resolve rclo0_mon: paco.

Lemma rclo0_base
      clo
      (MON: monotone0 clo):
  clo <1= rclo0 clo.
Proof.
  simpl. intros. econstructor 2; eauto.
  eapply MON; eauto using rclo0.
Qed.

Lemma rclo0_step
      (clo: rel -> rel) r:
  clo (rclo0 clo r) <0= rclo0 clo r.
Proof.
  intros. econstructor 2; eauto.
Qed.

Lemma rclo0_rclo0
      clo r
      (MON: monotone0 clo):
  rclo0 clo (rclo0 clo r) <0= rclo0 clo r.
Proof.
  intros. induction PR; eauto using rclo0.
Qed.

Structure weak_respectful0 (clo: rel -> rel) : Prop :=
  weak_respectful0_intro {
      WEAK_MON: monotone0 clo;
      WEAK_RESPECTFUL:
        forall l r (LE: l <0= r) (GF: l <0= gf r),
          clo l <0= gf (rclo0 clo r);
    }.
Hint Constructors weak_respectful0.

Lemma weak_respectful0_respectful0
      clo (RES: weak_respectful0 clo):
  respectful0 (rclo0 clo).
Proof.
  inversion RES. econstructor; eauto with paco. intros.
  induction PR; intros.
  - eapply gf_mon; eauto. intros.
    apply rclo0_incl. auto.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo0_mon; eauto.
    + intros. apply rclo0_rclo0; auto.
  - eapply gf_mon; eauto using rclo0.
Qed.

Lemma upto0_init:
  paco0 (compose gf gres0) bot0 <0= paco0 gf bot0.
Proof.
  apply sound0_is_gf; eauto.
  apply respectful0_is_sound0.
  apply grespectful0_respectful0.
Qed.

Lemma upto0_final:
  paco0 gf <1= paco0 (compose gf gres0).
Proof.
  pcofix CIH. intros. punfold PR. pfold.
  eapply gf_mon; [|apply grespectful0_incl].
  eapply gf_mon; [eauto|]. intros. right. inversion PR0; auto.
Qed.

Lemma upto0_step
      r clo (RES: weak_respectful0 clo):
  clo (paco0 (compose gf gres0) r) <0= paco0 (compose gf gres0) r.
Proof.
  intros. apply grespectful0_incl_rev.
  assert (RES' := weak_respectful0_respectful0 RES).
  eapply grespectful0_greatest. eauto.
  eapply rclo0_base; eauto.
  inversion RES. auto.
Qed.

Lemma upto0_step_under
      r clo (RES: weak_respectful0 clo):
  clo (gres0 r) <0= gres0 r.
Proof.
  intros. apply weak_respectful0_respectful0 in RES; eauto.
  eapply grespectful0_compose; eauto. eauto using rclo0.
Qed.

End Respectful0.

Hint Constructors sound0.
Hint Constructors respectful0.
Hint Constructors gres0.
Hint Resolve gfclo0_mon : paco.
Hint Resolve gfgres0_mon : paco.
Hint Resolve grespectful0_incl.
Hint Resolve rclo0_mon: paco.
Hint Constructors weak_respectful0.

Ltac pupto0_init := eapply upto0_init; eauto with paco.
Ltac pupto0_final := first [eapply upto0_final; eauto with paco | eapply grespectful0_incl].
Ltac pupto0 H := first [eapply upto0_step|eapply upto0_step_under]; [|eapply H|]; eauto with paco.

