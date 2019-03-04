Require Export Program.Basics. Open Scope program_scope.
Require Import paco14.
Set Implicit Arguments.

Section Respectful14.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.

Local Notation rel := (rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone14 gf.

Inductive sound14 (clo: rel -> rel): Prop :=
| sound14_intro
    (MON: monotone14 clo)
    (SOUND:
       forall r (PFIX: r <14= gf (clo r)),
         r <14= paco14 gf bot14)
.
Hint Constructors sound14.

Structure respectful14 (clo: rel -> rel) : Prop :=
  respectful14_intro {
      MON: monotone14 clo;
      RESPECTFUL:
        forall l r (LE: l <14= r) (GF: l <14= gf r),
          clo l <14= gf (clo r);
    }.
Hint Constructors respectful14.

Inductive gres14 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 : Prop :=
| gres14_intro
    clo
    (RES: respectful14 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
.
Hint Constructors gres14.

Lemma gfclo14_mon: forall clo, sound14 clo -> monotone14 (compose gf clo).
Proof.
  intros; destruct H; red; intros.
  eapply gf_mon; [apply IN|intros; eapply MON0; [apply PR|apply LE]].
Qed.
Hint Resolve gfclo14_mon : paco.

Lemma sound14_is_gf: forall clo (UPTO: sound14 clo),
    paco14 (compose gf clo) bot14 <14= paco14 gf bot14.
Proof.
  intros. _punfold PR; [|apply gfclo14_mon, UPTO]. edestruct UPTO.
  eapply (SOUND (paco14 (compose gf clo) bot14)).
  - intros. _punfold PR0; [|apply gfclo14_mon, UPTO].
    eapply (gfclo14_mon UPTO); [apply PR0| intros; destruct PR1; [apply H|destruct H]].
  - pfold. apply PR.
Qed.

Lemma respectful14_is_sound14: respectful14 <1= sound14.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \14/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; [apply MON0|].
  intros. set (rr e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 := exists n, rclo clo n r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13).
  assert (rr x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) by (exists 0; apply PR); clear PR.
  cut (forall n, rclo clo n r <14= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 H; pcofix CIH; intros.
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

Lemma respectful14_compose
      clo0 clo1
      (RES0: respectful14 clo0)
      (RES1: respectful14 clo1):
  respectful14 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; [apply IN|].
    intros. eapply MON1; [apply PR|apply LE].
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; [apply PR0|apply LE].
    + intros. eapply RESPECTFUL1; [apply LE| apply GF| apply PR0].
Qed.

Lemma grespectful14_mon: monotone14 gres14.
Proof.
  red. intros.
  destruct IN; destruct RES; exists clo; [|eapply MON0; [eapply CLO| eapply LE]].
  constructor; [eapply MON0|].
  intros. eapply RESPECTFUL0; [apply LE0|apply GF|apply PR].
Qed.

Lemma grespectful14_respectful14: respectful14 gres14.
Proof.
  econstructor; [apply grespectful14_mon|intros].
  destruct PR; destruct RES; eapply gf_mon with (r:=clo r).
  eapply RESPECTFUL0; [apply LE|apply GF|apply CLO].
  intros. econstructor; [constructor; [apply MON0|apply RESPECTFUL0]|apply PR].
Qed.

Lemma gfgres14_mon: monotone14 (compose gf gres14).
Proof.
  destruct grespectful14_respectful14.
  unfold monotone14. intros. eapply gf_mon; [eapply IN|].
  intros. eapply MON0;[apply PR|apply LE].
Qed.
Hint Resolve gfgres14_mon : paco.

Lemma grespectful14_greatest: forall clo (RES: respectful14 clo), clo <15= gres14.
Proof. intros. econstructor;[apply RES|apply PR]. Qed.

Lemma grespectful14_incl: forall r, r <14= gres14 r.
Proof.
  intros; eexists (fun x => x).
  - econstructor.
    + red; intros; apply LE, IN.
    + intros; apply GF, PR0.
  - apply PR.
Qed.
Hint Resolve grespectful14_incl.

Lemma grespectful14_compose: forall clo (RES: respectful14 clo) r,
    clo (gres14 r) <14= gres14 r.
Proof.
  intros; eapply grespectful14_greatest with (clo := compose clo gres14); [|apply PR].
  apply respectful14_compose; [apply RES|apply grespectful14_respectful14].
Qed.

Lemma grespectful14_incl_rev: forall r,
    gres14 (paco14 (compose gf gres14) r) <14= paco14 (compose gf gres14) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful14_compose, grespectful14_respectful14.
  destruct grespectful14_respectful14; eapply RESPECTFUL0, PR; intros; [apply grespectful14_incl; right; apply CIH, grespectful14_incl, PR0|].
  _punfold PR0; [|apply gfgres14_mon].
  eapply gfgres14_mon; [apply PR0|].
  intros; destruct PR1.
  - left. eapply paco14_mon; [apply H| apply CIH0].
  - right. eapply CIH0, H.
Qed.

Inductive rclo14 (clo: rel->rel) (r: rel): rel :=
| rclo14_incl
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13):
    @rclo14 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
| rclo14_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
    (R': r' <14= rclo14 clo r)
    (CLOR':clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13):
    @rclo14 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
| rclo14_gf
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
    (R': r' <14= rclo14 clo r)
    (CLOR':@gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13):
    @rclo14 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
.

Lemma rclo14_mon clo:
  monotone14 (rclo14 clo).
Proof.
  repeat intro. induction IN.
  - econstructor 1. apply LE, R.
  - econstructor 2; [intros; eapply H, PR| apply CLOR'].
  - econstructor 3; [intros; eapply H, PR| apply CLOR'].
Qed.
Hint Resolve rclo14_mon: paco.

Lemma rclo14_base
      clo
      (MON: monotone14 clo):
  clo <15= rclo14 clo.
Proof.
  intros. econstructor 2; [intros; apply PR0|].
  eapply MON; [apply PR|intros; constructor; apply PR0].
Qed.

Lemma rclo14_step
      (clo: rel -> rel) r:
  clo (rclo14 clo r) <14= rclo14 clo r.
Proof.
  intros. econstructor 2; [intros; apply PR0|apply PR].
Qed.

Lemma rclo14_rclo14
      clo r
      (MON: monotone14 clo):
  rclo14 clo (rclo14 clo r) <14= rclo14 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
Qed.

Structure weak_respectful14 (clo: rel -> rel) : Prop :=
  weak_respectful14_intro {
      WEAK_MON: monotone14 clo;
      WEAK_RESPECTFUL:
        forall l r (LE: l <14= r) (GF: l <14= gf r),
          clo l <14= gf (rclo14 clo r);
    }.
Hint Constructors weak_respectful14.

Lemma weak_respectful14_respectful14
      clo (RES: weak_respectful14 clo):
  respectful14 (rclo14 clo).
Proof.
  inversion RES. econstructor; [eapply rclo14_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply GF, R|]. intros.
    apply rclo14_incl. apply PR.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo14_mon; [apply R', PR|apply LE].
    + intros. apply rclo14_rclo14;[apply WEAK_MON0|apply PR].
  - eapply gf_mon; [apply CLOR'|].
    intros. eapply rclo14_mon; [apply R', PR| apply LE].
Qed.

Definition cgres14 := compose gf gres14.

Lemma upto14_init:
  paco14 cgres14 bot14 <14= paco14 gf bot14.
Proof.
  apply sound14_is_gf.
  apply respectful14_is_sound14.
  apply grespectful14_respectful14.
Qed.

Lemma upto14_final:
  paco14 gf <15= paco14 cgres14.
Proof.
  pcofix CIH. intros. _punfold PR; [|apply gf_mon]. pfold.
  eapply gf_mon; [|apply grespectful14_incl].
  eapply gf_mon; [apply PR|]. intros. right.
  inversion PR0; [apply CIH, H | apply CIH0, H].
Qed.

Lemma upto14_step
      r clo (RES: weak_respectful14 clo):
  clo (paco14 cgres14 r) <14= paco14 cgres14 r.
Proof.
  intros. apply grespectful14_incl_rev.
  assert (RES' := weak_respectful14_respectful14 RES).
  eapply grespectful14_greatest; [apply RES'|].
  eapply rclo14_base; [apply RES|].
  inversion RES. apply PR.
Qed.

Lemma upto14_step_under
      r clo (RES: weak_respectful14 clo):
  clo (gres14 r) <14= gres14 r.
Proof.
  intros. apply weak_respectful14_respectful14 in RES.
  eapply grespectful14_compose; [apply RES|].
  econstructor 2; [intros; constructor 1; apply PR0 | apply PR].
Qed.

End Respectful14.

Lemma rclo14_mon_gen T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) clo clo' r r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
      (REL: rclo14 gf clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
      (LEgf: gf <15= gf')
      (LEclo: clo <15= clo')
      (LEr: r <14= r') :
  rclo14 gf' clo' r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
Proof.
  induction REL.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR| apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR| apply LEgf, CLOR'].
Qed.

Lemma grespectful14_impl T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
    (PR: gres14 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
    (EQ: forall r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 <-> gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13):
  gres14 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  intros. destruct PR. econstructor; [|apply CLO].
  destruct RES. econstructor; [apply MON0|].
  intros. eapply EQ. eapply RESPECTFUL0; [apply LE| |apply PR].
  intros. eapply EQ. apply GF, PR0.
Qed.

Lemma grespectful14_iff T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
    (EQ: forall r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 <-> gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13):
  gres14 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 <-> gres14 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  split; intros.
  - eapply grespectful14_impl; [apply H | apply EQ].
  - eapply grespectful14_impl; [apply H | split; apply EQ].
Qed.

Hint Constructors sound14.
Hint Constructors respectful14.
Hint Constructors gres14.
Hint Resolve gfclo14_mon : paco.
Hint Resolve gfgres14_mon : paco.
Hint Resolve grespectful14_incl.
Hint Resolve rclo14_mon: paco.
Hint Constructors weak_respectful14.
Hint Unfold cgres14.

(* User Tactics *)

Ltac pupto14_init := eapply upto14_init; [eauto with paco|].
Ltac pupto14_final := first [eapply upto14_final; [eauto with paco|] | eapply grespectful14_incl].
Ltac pupto14 H := first [eapply upto14_step|eapply upto14_step_under]; [|eapply H|]; [eauto with paco|].

Ltac pfold14_reverse_ :=
  repeat red;
  match goal with
  | [|- ?gf (upaco14 _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ _ _ _ _] => eapply (paco14_unfold (gf := gf))
  | [|- ?gf (?gres (upaco14 _ _ _ _ _ _ _ _ _ _ _ _ _ _)) _ _ _ _ _ _ _ _ _ _ _ _ _ _] => eapply (paco14_unfold (gf := cgres14 gf))
  end.

Ltac pfold14_reverse := pfold14_reverse_; eauto with paco.

Ltac punfold14_reverse_ H :=
  repeat red in H;
  let PP := type of H in
  match PP with
  | ?gf (upaco14 _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eapply (paco14_fold gf) in H
  | ?gf (?gres (upaco14 _ _ _ _ _ _ _ _ _ _ _ _ _ _)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eapply (paco14_fold (cgres14 gf)) in H
  end.

Ltac punfold14_reverse H := punfold14_reverse_ H; eauto with paco.

