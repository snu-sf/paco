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
Proof.
  intros; destruct H; red; intros.
  eapply gf_mon; [apply IN|intros; eapply MON0; [apply PR|apply LE]].
Qed.
Hint Resolve gfclo1_mon : paco.

Lemma sound1_is_gf: forall clo (UPTO: sound1 clo),
    paco1 (compose gf clo) bot1 <1= paco1 gf bot1.
Proof.
  intros. _punfold PR; [|apply gfclo1_mon, UPTO]. edestruct UPTO.
  eapply (SOUND (paco1 (compose gf clo) bot1)).
  - intros. _punfold PR0; [|apply gfclo1_mon, UPTO].
    eapply (gfclo1_mon UPTO); [apply PR0| intros; destruct PR1; [apply H|destruct H]].
  - pfold. apply PR.
Qed.

Lemma respectful1_is_sound1: respectful1 <1= sound1.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \1/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; [apply MON0|].
  intros. set (rr e0 := exists n, rclo clo n r e0).
  assert (rr x0) by (exists 0; apply PR); clear PR.
  cut (forall n, rclo clo n r <1= gf (rclo clo (S n) r)).
  { intro X; revert x0 H; pcofix CIH; intros.
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

Lemma respectful1_compose
      clo0 clo1
      (RES0: respectful1 clo0)
      (RES1: respectful1 clo1):
  respectful1 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; [apply IN|].
    intros. eapply MON1; [apply PR|apply LE].
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; [apply PR0|apply LE].
    + intros. eapply RESPECTFUL1; [apply LE| apply GF| apply PR0].
Qed.

Lemma grespectful1_mon: monotone1 gres1.
Proof.
  red. intros.
  destruct IN; destruct RES; exists clo; [|eapply MON0; [eapply CLO| eapply LE]].
  constructor; [eapply MON0|].
  intros. eapply RESPECTFUL0; [apply LE0|apply GF|apply PR].
Qed.

Lemma grespectful1_respectful1: respectful1 gres1.
Proof.
  econstructor; [apply grespectful1_mon|intros].
  destruct PR; destruct RES; eapply gf_mon with (r:=clo r).
  eapply RESPECTFUL0; [apply LE|apply GF|apply CLO].
  intros. econstructor; [constructor; [apply MON0|apply RESPECTFUL0]|apply PR].
Qed.

Lemma gfgres1_mon: monotone1 (compose gf gres1).
Proof.
  destruct grespectful1_respectful1.
  unfold monotone1. intros. eapply gf_mon; [eapply IN|].
  intros. eapply MON0;[apply PR|apply LE].
Qed.
Hint Resolve gfgres1_mon : paco.

Lemma grespectful1_greatest: forall clo (RES: respectful1 clo), clo <2= gres1.
Proof. intros. econstructor;[apply RES|apply PR]. Qed.

Lemma grespectful1_incl: forall r, r <1= gres1 r.
Proof.
  intros; eexists (fun x => x).
  - econstructor.
    + red; intros; apply LE, IN.
    + intros; apply GF, PR0.
  - apply PR.
Qed.
Hint Resolve grespectful1_incl.

Lemma grespectful1_compose: forall clo (RES: respectful1 clo) r,
    clo (gres1 r) <1= gres1 r.
Proof.
  intros; eapply grespectful1_greatest with (clo := compose clo gres1); [|apply PR].
  apply respectful1_compose; [apply RES|apply grespectful1_respectful1].
Qed.

Lemma grespectful1_incl_rev: forall r,
    gres1 (paco1 (compose gf gres1) r) <1= paco1 (compose gf gres1) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful1_compose, grespectful1_respectful1.
  destruct grespectful1_respectful1; eapply RESPECTFUL0, PR; intros; [apply grespectful1_incl; right; apply CIH, grespectful1_incl, PR0|].
  _punfold PR0; [|apply gfgres1_mon].
  eapply gfgres1_mon; [apply PR0|].
  intros; destruct PR1.
  - left. eapply paco1_mon; [apply H| apply CIH0].
  - right. eapply CIH0, H.
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
  repeat intro. induction IN.
  - econstructor 1. apply LE, R.
  - econstructor 2; [intros; eapply H, PR| eapply CLOR'].
  - econstructor 3; [intros; eapply H, PR| eapply CLOR'].
Qed.
Hint Resolve rclo1_mon: paco.

Lemma rclo1_base
      clo
      (MON: monotone1 clo):
  clo <2= rclo1 clo.
Proof.
  intros. econstructor 2; [intros; apply PR0|].
  eapply MON; [apply PR|intros; constructor; apply PR0].
Qed.

Lemma rclo1_step
      (clo: rel -> rel) r:
  clo (rclo1 clo r) <1= rclo1 clo r.
Proof.
  intros. econstructor 2; [intros; apply PR0|apply PR].
Qed.

Lemma rclo1_rclo1
      clo r
      (MON: monotone1 clo):
  rclo1 clo (rclo1 clo r) <1= rclo1 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
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
  inversion RES. econstructor; [eapply rclo1_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply GF, R|]. intros.
    apply rclo1_incl. apply PR.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo1_mon; [apply R', PR|apply LE].
    + intros. apply rclo1_rclo1;[apply WEAK_MON0|apply PR].
  - eapply gf_mon; [apply CLOR'|].
    intros. eapply rclo1_mon; [apply R', PR| apply LE].
Qed.

Lemma upto1_init:
  paco1 (compose gf gres1) bot1 <1= paco1 gf bot1.
Proof.
  apply sound1_is_gf.
  apply respectful1_is_sound1.
  apply grespectful1_respectful1.
Qed.

Lemma upto1_final:
  paco1 gf <2= paco1 (compose gf gres1).
Proof.
  pcofix CIH. intros. _punfold PR; [|apply gf_mon]. pfold.
  eapply gf_mon; [|apply grespectful1_incl].
  eapply gf_mon; [apply PR|]. intros. right.
  inversion PR0; [apply CIH, H | apply CIH0, H].
Qed.

Lemma upto1_step
      r clo (RES: weak_respectful1 clo):
  clo (paco1 (compose gf gres1) r) <1= paco1 (compose gf gres1) r.
Proof.
  intros. apply grespectful1_incl_rev.
  assert (RES' := weak_respectful1_respectful1 RES).
  eapply grespectful1_greatest; [apply RES'|].
  eapply rclo1_base; [apply RES|].
  inversion RES. apply PR.
Qed.

Lemma upto1_step_under
      r clo (RES: weak_respectful1 clo):
  clo (gres1 r) <1= gres1 r.
Proof.
  intros. apply weak_respectful1_respectful1 in RES.
  eapply grespectful1_compose; [apply RES|].
  econstructor 2; [intros; constructor 1; apply PR0 | apply PR].
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

Ltac pupto1_init := eapply upto1_init; [eauto with paco|].
Ltac pupto1_final := first [eapply upto1_final; [eauto with paco|] | eapply grespectful1_incl].
Ltac pupto1 H := first [eapply upto1_step|eapply upto1_step_under]; [|eapply H|]; [eauto with paco|].

