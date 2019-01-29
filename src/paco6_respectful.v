Require Import paco6.
Require Export Program.
Set Implicit Arguments.

Section Respectful6.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.

Local Notation rel := (rel6 T0 T1 T2 T3 T4 T5).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone6 gf.

Inductive sound6 (clo: rel -> rel): Prop :=
| sound6_intro
    (MON: monotone6 clo)
    (SOUND:
       forall r (PFIX: r <6= gf (clo r)),
         r <6= paco6 gf bot6)
.
Hint Constructors sound6.

Structure respectful6 (clo: rel -> rel) : Prop :=
  respectful6_intro {
      MON: monotone6 clo;
      RESPECTFUL:
        forall l r (LE: l <6= r) (GF: l <6= gf r),
          clo l <6= gf (clo r);
    }.
Hint Constructors respectful6.

Inductive gres6 (r: rel) e0 e1 e2 e3 e4 e5 : Prop :=
| gres6_intro
    clo
    (RES: respectful6 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5)
.
Hint Constructors gres6.
Lemma gfclo6_mon: forall clo, sound6 clo -> monotone6 (compose gf clo).
Proof. intros; destruct H; eauto using gf_mon. Qed.
Hint Resolve gfclo6_mon : paco.

Lemma sound6_is_gf: forall clo (UPTO: sound6 clo),
    paco6 (compose gf clo) bot6 <6= paco6 gf bot6.
Proof.
  intros. punfold PR. edestruct UPTO.
  eapply (SOUND (paco6 (compose gf clo) bot6)); [|eauto].
  intros. punfold PR0.
  eapply (gfclo6_mon UPTO); eauto. intros. destruct PR1; eauto. contradiction.
Qed.

Lemma respectful6_is_sound6: respectful6 <1= sound6.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \6/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; eauto.
  intros. set (rr e0 e1 e2 e3 e4 e5 := exists n, rclo clo n r e0 e1 e2 e3 e4 e5).
  assert (rr x0 x1 x2 x3 x4 x5) by (exists 0; eauto); clear PR.
  cut (forall n, rclo clo n r <6= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 x4 x5 H; pcofix CIH; intros.
    unfold rr in *; destruct H0; eauto 10 using gf_mon. }
  induction n; intros; [simpl; eauto using gf_mon|].
  simpl in *; destruct PR; [eauto using gf_mon|].
  eapply gf_mon; [eapply RESPECTFUL0; [|apply IHn|]|]; instantiate; simpl; eauto.
Qed.

Lemma respectful6_compose
      clo0 clo1
      (RES0: respectful6 clo0)
      (RES1: respectful6 clo1):
  respectful6 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; eauto.
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; eauto.
    + intros. eapply RESPECTFUL1; eauto.
Qed.

Lemma grespectful6_respectful6: respectful6 gres6.
Proof.
  econstructor; repeat intro.
  - destruct IN; destruct RES; exists clo; eauto.
  - destruct PR; destruct RES; eapply gf_mon with (r:=clo r); eauto.
Qed.

Lemma gfgres6_mon: monotone6 (compose gf gres6).
Proof.
  destruct grespectful6_respectful6; eauto using gf_mon.
Qed.
Hint Resolve gfgres6_mon : paco.

Lemma grespectful6_greatest: forall clo (RES: respectful6 clo), clo <7= gres6.
Proof. eauto. Qed.

Lemma grespectful6_incl: forall r, r <6= gres6 r.
Proof.
  intros; eexists (fun x => x); eauto.
Qed.
Hint Resolve grespectful6_incl.

Lemma grespectful6_compose: forall clo (RES: respectful6 clo) r,
    clo (gres6 r) <6= gres6 r.
Proof.
  intros; eapply grespectful6_greatest with (clo := compose clo gres6);
    eauto using respectful6_compose, grespectful6_respectful6.
Qed.

Lemma grespectful6_incl_rev: forall r,
    gres6 (paco6 (compose gf gres6) r) <6= paco6 (compose gf gres6) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful6_compose, grespectful6_respectful6.
  destruct grespectful6_respectful6; eapply RESPECTFUL0, PR; intros; [apply grespectful6_incl; eauto|].
  punfold PR0.
  eapply gfgres6_mon; eauto; intros; destruct PR1; eauto.
Qed.

Inductive rclo6 clo (r: rel): rel :=
| rclo6_incl
    e0 e1 e2 e3 e4 e5
    (R: r e0 e1 e2 e3 e4 e5):
    @rclo6 clo r e0 e1 e2 e3 e4 e5
| rclo6_step'
    r' e0 e1 e2 e3 e4 e5
    (R': r' <6= rclo6 clo r)
    (CLOR':clo r' e0 e1 e2 e3 e4 e5):
    @rclo6 clo r e0 e1 e2 e3 e4 e5
| rclo6_gf
    r' e0 e1 e2 e3 e4 e5
    (R': r' <6= rclo6 clo r)
    (CLOR':@gf r' e0 e1 e2 e3 e4 e5):
    @rclo6 clo r e0 e1 e2 e3 e4 e5
.
Lemma rclo6_mon clo:
  monotone6 (rclo6 clo).
Proof.
  repeat intro. induction IN; eauto using rclo6.
Qed.
Hint Resolve rclo6_mon: paco.

Lemma rclo6_base
      clo
      (MON: monotone6 clo):
  clo <7= rclo6 clo.
Proof.
  simpl. intros. econstructor 2; eauto.
  eapply MON; eauto using rclo6.
Qed.

Lemma rclo6_step
      (clo: rel -> rel) r:
  clo (rclo6 clo r) <6= rclo6 clo r.
Proof.
  intros. econstructor 2; eauto.
Qed.

Lemma rclo6_rclo6
      clo r
      (MON: monotone6 clo):
  rclo6 clo (rclo6 clo r) <6= rclo6 clo r.
Proof.
  intros. induction PR; eauto using rclo6.
Qed.

Structure weak_respectful6 (clo: rel -> rel) : Prop :=
  weak_respectful6_intro {
      WEAK_MON: monotone6 clo;
      WEAK_RESPECTFUL:
        forall l r (LE: l <6= r) (GF: l <6= gf r),
          clo l <6= gf (rclo6 clo r);
    }.
Hint Constructors weak_respectful6.

Lemma weak_respectful6_respectful6
      clo (RES: weak_respectful6 clo):
  respectful6 (rclo6 clo).
Proof.
  inversion RES. econstructor; eauto with paco. intros.
  induction PR; intros.
  - eapply gf_mon; eauto. intros.
    apply rclo6_incl. auto.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo6_mon; eauto.
    + intros. apply rclo6_rclo6; auto.
  - eapply gf_mon; eauto using rclo6.
Qed.

Lemma upto6_init:
  paco6 (compose gf gres6) bot6 <6= paco6 gf bot6.
Proof.
  apply sound6_is_gf; eauto.
  apply respectful6_is_sound6.
  apply grespectful6_respectful6.
Qed.

Lemma upto6_final:
  paco6 gf <7= paco6 (compose gf gres6).
Proof.
  pcofix CIH. intros. punfold PR. pfold.
  eapply gf_mon; [|apply grespectful6_incl].
  eapply gf_mon; [eauto|]. intros. right. inversion PR0; auto.
Qed.

Lemma upto6_step
      r clo (RES: weak_respectful6 clo):
  clo (paco6 (compose gf gres6) r) <6= paco6 (compose gf gres6) r.
Proof.
  intros. apply grespectful6_incl_rev.
  assert (RES' := weak_respectful6_respectful6 RES).
  eapply grespectful6_greatest. eauto.
  eapply rclo6_base; eauto.
  inversion RES. auto.
Qed.

Lemma upto6_step_under
      r clo (RES: weak_respectful6 clo):
  clo (gres6 r) <6= gres6 r.
Proof.
  intros. apply weak_respectful6_respectful6 in RES; eauto.
  eapply grespectful6_compose; eauto. eauto using rclo6.
Qed.

End Respectful6.

Hint Constructors sound6.
Hint Constructors respectful6.
Hint Constructors gres6.
Hint Resolve gfclo6_mon : paco.
Hint Resolve gfgres6_mon : paco.
Hint Resolve grespectful6_incl.
Hint Resolve rclo6_mon: paco.
Hint Constructors weak_respectful6.

Ltac pupto6_init := eapply upto6_init; eauto with paco.
Ltac pupto6_final := first [eapply upto6_final; eauto with paco | eapply grespectful6_incl].
Ltac pupto6 H := first [eapply upto6_step|eapply upto6_step_under]; [|eapply H|]; eauto with paco.

