Require Export Program.Basics. Open Scope program_scope.
Require Import paco6.
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
Proof.
  intros; destruct H; red; intros.
  eapply gf_mon; [apply IN|intros; eapply MON0; [apply PR|apply LE]].
Qed.
Hint Resolve gfclo6_mon : paco.

Lemma sound6_is_gf: forall clo (UPTO: sound6 clo),
    paco6 (compose gf clo) bot6 <6= paco6 gf bot6.
Proof.
  intros. _punfold PR; [|apply gfclo6_mon, UPTO]. edestruct UPTO.
  eapply (SOUND (paco6 (compose gf clo) bot6)).
  - intros. _punfold PR0; [|apply gfclo6_mon, UPTO].
    eapply (gfclo6_mon UPTO); [apply PR0| intros; destruct PR1; [apply H|destruct H]].
  - pfold. apply PR.
Qed.

Lemma respectful6_is_sound6: respectful6 <1= sound6.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \6/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; [apply MON0|].
  intros. set (rr e0 e1 e2 e3 e4 e5 := exists n, rclo clo n r e0 e1 e2 e3 e4 e5).
  assert (rr x0 x1 x2 x3 x4 x5) by (exists 0; apply PR); clear PR.
  cut (forall n, rclo clo n r <6= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 x4 x5 H; pcofix CIH; intros.
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

Lemma respectful6_compose
      clo0 clo1
      (RES0: respectful6 clo0)
      (RES1: respectful6 clo1):
  respectful6 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; [apply IN|].
    intros. eapply MON1; [apply PR|apply LE].
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; [apply PR0|apply LE].
    + intros. eapply RESPECTFUL1; [apply LE| apply GF| apply PR0].
Qed.

Lemma grespectful6_mon: monotone6 gres6.
Proof.
  red. intros.
  destruct IN; destruct RES; exists clo; [|eapply MON0; [eapply CLO| eapply LE]].
  constructor; [eapply MON0|].
  intros. eapply RESPECTFUL0; [apply LE0|apply GF|apply PR].
Qed.

Lemma grespectful6_respectful6: respectful6 gres6.
Proof.
  econstructor; [apply grespectful6_mon|intros].
  destruct PR; destruct RES; eapply gf_mon with (r:=clo r).
  eapply RESPECTFUL0; [apply LE|apply GF|apply CLO].
  intros. econstructor; [constructor; [apply MON0|apply RESPECTFUL0]|apply PR].
Qed.

Lemma gfgres6_mon: monotone6 (compose gf gres6).
Proof.
  destruct grespectful6_respectful6.
  unfold monotone6. intros. eapply gf_mon; [eapply IN|].
  intros. eapply MON0;[apply PR|apply LE].
Qed.
Hint Resolve gfgres6_mon : paco.

Lemma grespectful6_greatest: forall clo (RES: respectful6 clo), clo <7= gres6.
Proof. intros. econstructor;[apply RES|apply PR]. Qed.

Lemma grespectful6_incl: forall r, r <6= gres6 r.
Proof.
  intros; eexists (fun x => x).
  - econstructor.
    + red; intros; apply LE, IN.
    + intros; apply GF, PR0.
  - apply PR.
Qed.
Hint Resolve grespectful6_incl.

Lemma grespectful6_compose: forall clo (RES: respectful6 clo) r,
    clo (gres6 r) <6= gres6 r.
Proof.
  intros; eapply grespectful6_greatest with (clo := compose clo gres6); [|apply PR].
  apply respectful6_compose; [apply RES|apply grespectful6_respectful6].
Qed.

Lemma grespectful6_incl_rev: forall r,
    gres6 (paco6 (compose gf gres6) r) <6= paco6 (compose gf gres6) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful6_compose, grespectful6_respectful6.
  destruct grespectful6_respectful6; eapply RESPECTFUL0, PR; intros; [apply grespectful6_incl; right; apply CIH, grespectful6_incl, PR0|].
  _punfold PR0; [|apply gfgres6_mon].
  eapply gfgres6_mon; [apply PR0|].
  intros; destruct PR1.
  - left. eapply paco6_mon; [apply H| apply CIH0].
  - right. eapply CIH0, H.
Qed.

Inductive rclo6 (clo: rel->rel) (r: rel): rel :=
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

Lemma rclo6_mon_gen clo clo' r r' e0 e1 e2 e3 e4 e5
      (REL: @rclo6 clo r e0 e1 e2 e3 e4 e5)
      (LEclo: clo <7= clo')
      (LEr: r <6= r') :
  @rclo6 clo' r' e0 e1 e2 e3 e4 e5.
Proof.
  induction REL.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR| apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR| apply CLOR'].
Qed.

Lemma rclo6_mon clo:
  monotone6 (rclo6 clo).
Proof.
  repeat intro. eapply rclo6_mon_gen; intros; [apply IN | apply PR | apply LE, PR].
Qed.
Hint Resolve rclo6_mon: paco.

Lemma rclo6_base
      clo
      (MON: monotone6 clo):
  clo <7= rclo6 clo.
Proof.
  intros. econstructor 2; [intros; apply PR0|].
  eapply MON; [apply PR|intros; constructor; apply PR0].
Qed.

Lemma rclo6_step
      (clo: rel -> rel) r:
  clo (rclo6 clo r) <6= rclo6 clo r.
Proof.
  intros. econstructor 2; [intros; apply PR0|apply PR].
Qed.

Lemma rclo6_rclo6
      clo r
      (MON: monotone6 clo):
  rclo6 clo (rclo6 clo r) <6= rclo6 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
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
  inversion RES. econstructor; [eapply rclo6_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply GF, R|]. intros.
    apply rclo6_incl. apply PR.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo6_mon; [apply R', PR|apply LE].
    + intros. apply rclo6_rclo6;[apply WEAK_MON0|apply PR].
  - eapply gf_mon; [apply CLOR'|].
    intros. eapply rclo6_mon; [apply R', PR| apply LE].
Qed.

Lemma upto6_init:
  paco6 (compose gf gres6) bot6 <6= paco6 gf bot6.
Proof.
  apply sound6_is_gf.
  apply respectful6_is_sound6.
  apply grespectful6_respectful6.
Qed.

Lemma upto6_final:
  paco6 gf <7= paco6 (compose gf gres6).
Proof.
  pcofix CIH. intros. _punfold PR; [|apply gf_mon]. pfold.
  eapply gf_mon; [|apply grespectful6_incl].
  eapply gf_mon; [apply PR|]. intros. right.
  inversion PR0; [apply CIH, H | apply CIH0, H].
Qed.

Lemma upto6_step
      r clo (RES: weak_respectful6 clo):
  clo (paco6 (compose gf gres6) r) <6= paco6 (compose gf gres6) r.
Proof.
  intros. apply grespectful6_incl_rev.
  assert (RES' := weak_respectful6_respectful6 RES).
  eapply grespectful6_greatest; [apply RES'|].
  eapply rclo6_base; [apply RES|].
  inversion RES. apply PR.
Qed.

Lemma upto6_step_under
      r clo (RES: weak_respectful6 clo):
  clo (gres6 r) <6= gres6 r.
Proof.
  intros. apply weak_respectful6_respectful6 in RES.
  eapply grespectful6_compose; [apply RES|].
  econstructor 2; [intros; constructor 1; apply PR0 | apply PR].
Qed.

End Respectful6.

Lemma grespectful6_impl T0 T1 T2 T3 T4 T5 (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) r x0 x1 x2 x3 x4 x5
    (PR: gres6 gf r x0 x1 x2 x3 x4 x5)
    (EQ: forall r x0 x1 x2 x3 x4 x5, gf r x0 x1 x2 x3 x4 x5 <-> gf' r x0 x1 x2 x3 x4 x5):
  gres6 gf' r x0 x1 x2 x3 x4 x5.
Proof.
  intros. destruct PR. econstructor; [|apply CLO].
  destruct RES. econstructor; [apply MON0|].
  intros. eapply EQ. eapply RESPECTFUL0; [apply LE| |apply PR].
  intros. eapply EQ. apply GF, PR0.
Qed.

Lemma grespectful6_iff T0 T1 T2 T3 T4 T5 (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) r x0 x1 x2 x3 x4 x5
    (EQ: forall r x0 x1 x2 x3 x4 x5, gf r x0 x1 x2 x3 x4 x5 <-> gf' r x0 x1 x2 x3 x4 x5):
  gres6 gf r x0 x1 x2 x3 x4 x5 <-> gres6 gf' r x0 x1 x2 x3 x4 x5.
Proof.
  split; intros.
  - eapply grespectful6_impl; [apply H | apply EQ].
  - eapply grespectful6_impl; [apply H | split; apply EQ].
Qed.

Hint Constructors sound6.
Hint Constructors respectful6.
Hint Constructors gres6.
Hint Resolve gfclo6_mon : paco.
Hint Resolve gfgres6_mon : paco.
Hint Resolve grespectful6_incl.
Hint Resolve rclo6_mon: paco.
Hint Constructors weak_respectful6.

Ltac pupto6_init := eapply upto6_init; [eauto with paco|].
Ltac pupto6_final := first [eapply upto6_final; [eauto with paco|] | eapply grespectful6_incl].
Ltac pupto6 H := first [eapply upto6_step|eapply upto6_step_under]; [|eapply H|]; [eauto with paco|].

