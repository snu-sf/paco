Require Export Program.Basics. Open Scope program_scope.
Require Import paco12.
Set Implicit Arguments.

Section Respectful12.

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

Local Notation rel := (rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11).

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone12 gf.

Inductive sound12 (clo: rel -> rel): Prop :=
| sound12_intro
    (MON: monotone12 clo)
    (SOUND:
       forall r (PFIX: r <12= gf (clo r)),
         r <12= paco12 gf bot12)
.
Hint Constructors sound12.

Structure respectful12 (clo: rel -> rel) : Prop :=
  respectful12_intro {
      MON: monotone12 clo;
      RESPECTFUL:
        forall l r (LE: l <12= r) (GF: l <12= gf r),
          clo l <12= gf (clo r);
    }.
Hint Constructors respectful12.

Inductive gres12 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : Prop :=
| gres12_intro
    clo
    (RES: respectful12 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)
.
Hint Constructors gres12.

Lemma gfclo12_mon: forall clo, sound12 clo -> monotone12 (compose gf clo).
Proof.
  intros; destruct H; red; intros.
  eapply gf_mon; [apply IN|intros; eapply MON0; [apply PR|apply LE]].
Qed.
Hint Resolve gfclo12_mon : paco.

Lemma sound12_is_gf: forall clo (UPTO: sound12 clo),
    paco12 (compose gf clo) bot12 <12= paco12 gf bot12.
Proof.
  intros. _punfold PR; [|apply gfclo12_mon, UPTO]. edestruct UPTO.
  eapply (SOUND (paco12 (compose gf clo) bot12)).
  - intros. _punfold PR0; [|apply gfclo12_mon, UPTO].
    eapply (gfclo12_mon UPTO); [apply PR0| intros; destruct PR1; [apply H|destruct H]].
  - pfold. apply PR.
Qed.

Lemma respectful12_is_sound12: respectful12 <1= sound12.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \12/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; [apply MON0|].
  intros. set (rr e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 := exists n, rclo clo n r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11).
  assert (rr x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) by (exists 0; apply PR); clear PR.
  cut (forall n, rclo clo n r <12= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 H; pcofix CIH; intros.
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

Lemma respectful12_compose
      clo0 clo1
      (RES0: respectful12 clo0)
      (RES1: respectful12 clo1):
  respectful12 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; [apply IN|].
    intros. eapply MON1; [apply PR|apply LE].
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; [apply PR0|apply LE].
    + intros. eapply RESPECTFUL1; [apply LE| apply GF| apply PR0].
Qed.

Lemma grespectful12_mon: monotone12 gres12.
Proof.
  red. intros.
  destruct IN; destruct RES; exists clo; [|eapply MON0; [eapply CLO| eapply LE]].
  constructor; [eapply MON0|].
  intros. eapply RESPECTFUL0; [apply LE0|apply GF|apply PR].
Qed.

Lemma grespectful12_respectful12: respectful12 gres12.
Proof.
  econstructor; [apply grespectful12_mon|intros].
  destruct PR; destruct RES; eapply gf_mon with (r:=clo r).
  eapply RESPECTFUL0; [apply LE|apply GF|apply CLO].
  intros. econstructor; [constructor; [apply MON0|apply RESPECTFUL0]|apply PR].
Qed.

Lemma gfgres12_mon: monotone12 (compose gf gres12).
Proof.
  destruct grespectful12_respectful12.
  unfold monotone12. intros. eapply gf_mon; [eapply IN|].
  intros. eapply MON0;[apply PR|apply LE].
Qed.
Hint Resolve gfgres12_mon : paco.

Lemma grespectful12_greatest: forall clo (RES: respectful12 clo), clo <13= gres12.
Proof. intros. econstructor;[apply RES|apply PR]. Qed.

Lemma grespectful12_incl: forall r, r <12= gres12 r.
Proof.
  intros; eexists (fun x => x).
  - econstructor.
    + red; intros; apply LE, IN.
    + intros; apply GF, PR0.
  - apply PR.
Qed.
Hint Resolve grespectful12_incl.

Lemma grespectful12_compose: forall clo (RES: respectful12 clo) r,
    clo (gres12 r) <12= gres12 r.
Proof.
  intros; eapply grespectful12_greatest with (clo := compose clo gres12); [|apply PR].
  apply respectful12_compose; [apply RES|apply grespectful12_respectful12].
Qed.

Lemma grespectful12_incl_rev: forall r,
    gres12 (paco12 (compose gf gres12) r) <12= paco12 (compose gf gres12) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful12_compose, grespectful12_respectful12.
  destruct grespectful12_respectful12; eapply RESPECTFUL0, PR; intros; [apply grespectful12_incl; right; apply CIH, grespectful12_incl, PR0|].
  _punfold PR0; [|apply gfgres12_mon].
  eapply gfgres12_mon; [apply PR0|].
  intros; destruct PR1.
  - left. eapply paco12_mon; [apply H| apply CIH0].
  - right. eapply CIH0, H.
Qed.

Inductive rclo12 (clo: rel->rel) (r: rel): rel :=
| rclo12_incl
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11):
    @rclo12 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
| rclo12_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
    (R': r' <12= rclo12 clo r)
    (CLOR':clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11):
    @rclo12 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
| rclo12_gf
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
    (R': r' <12= rclo12 clo r)
    (CLOR':@gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11):
    @rclo12 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
.

Lemma rclo12_mon clo:
  monotone12 (rclo12 clo).
Proof.
  repeat intro. induction IN.
  - econstructor 1. apply LE, R.
  - econstructor 2; [intros; eapply H, PR| apply CLOR'].
  - econstructor 3; [intros; eapply H, PR| apply CLOR'].
Qed.
Hint Resolve rclo12_mon: paco.

Lemma rclo12_base
      clo
      (MON: monotone12 clo):
  clo <13= rclo12 clo.
Proof.
  intros. econstructor 2; [intros; apply PR0|].
  eapply MON; [apply PR|intros; constructor; apply PR0].
Qed.

Lemma rclo12_step
      (clo: rel -> rel) r:
  clo (rclo12 clo r) <12= rclo12 clo r.
Proof.
  intros. econstructor 2; [intros; apply PR0|apply PR].
Qed.

Lemma rclo12_rclo12
      clo r
      (MON: monotone12 clo):
  rclo12 clo (rclo12 clo r) <12= rclo12 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
Qed.

Structure weak_respectful12 (clo: rel -> rel) : Prop :=
  weak_respectful12_intro {
      WEAK_MON: monotone12 clo;
      WEAK_RESPECTFUL:
        forall l r (LE: l <12= r) (GF: l <12= gf r),
          clo l <12= gf (rclo12 clo r);
    }.
Hint Constructors weak_respectful12.

Lemma weak_respectful12_respectful12
      clo (RES: weak_respectful12 clo):
  respectful12 (rclo12 clo).
Proof.
  inversion RES. econstructor; [eapply rclo12_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply GF, R|]. intros.
    apply rclo12_incl. apply PR.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo12_mon; [apply R', PR|apply LE].
    + intros. apply rclo12_rclo12;[apply WEAK_MON0|apply PR].
  - eapply gf_mon; [apply CLOR'|].
    intros. eapply rclo12_mon; [apply R', PR| apply LE].
Qed.

Lemma upto12_init:
  paco12 (compose gf gres12) bot12 <12= paco12 gf bot12.
Proof.
  apply sound12_is_gf.
  apply respectful12_is_sound12.
  apply grespectful12_respectful12.
Qed.

Lemma upto12_final:
  paco12 gf <13= paco12 (compose gf gres12).
Proof.
  pcofix CIH. intros. _punfold PR; [|apply gf_mon]. pfold.
  eapply gf_mon; [|apply grespectful12_incl].
  eapply gf_mon; [apply PR|]. intros. right.
  inversion PR0; [apply CIH, H | apply CIH0, H].
Qed.

Lemma upto12_step
      r clo (RES: weak_respectful12 clo):
  clo (paco12 (compose gf gres12) r) <12= paco12 (compose gf gres12) r.
Proof.
  intros. apply grespectful12_incl_rev.
  assert (RES' := weak_respectful12_respectful12 RES).
  eapply grespectful12_greatest; [apply RES'|].
  eapply rclo12_base; [apply RES|].
  inversion RES. apply PR.
Qed.

Lemma upto12_step_under
      r clo (RES: weak_respectful12 clo):
  clo (gres12 r) <12= gres12 r.
Proof.
  intros. apply weak_respectful12_respectful12 in RES.
  eapply grespectful12_compose; [apply RES|].
  econstructor 2; [intros; constructor 1; apply PR0 | apply PR].
Qed.

End Respectful12.

Lemma rclo12_mon_gen T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) clo clo' r r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
      (REL: rclo12 gf clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)
      (LEgf: gf <13= gf')
      (LEclo: clo <13= clo')
      (LEr: r <12= r') :
  rclo12 gf' clo' r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof.
  induction REL.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR| apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR| apply LEgf, CLOR'].
Qed.

Lemma grespectful12_impl T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    (PR: gres12 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
    (EQ: forall r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 <-> gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11):
  gres12 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  intros. destruct PR. econstructor; [|apply CLO].
  destruct RES. econstructor; [apply MON0|].
  intros. eapply EQ. eapply RESPECTFUL0; [apply LE| |apply PR].
  intros. eapply EQ. apply GF, PR0.
Qed.

Lemma grespectful12_iff T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    (EQ: forall r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 <-> gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11):
  gres12 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 <-> gres12 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  split; intros.
  - eapply grespectful12_impl; [apply H | apply EQ].
  - eapply grespectful12_impl; [apply H | split; apply EQ].
Qed.

Hint Constructors sound12.
Hint Constructors respectful12.
Hint Constructors gres12.
Hint Resolve gfclo12_mon : paco.
Hint Resolve gfgres12_mon : paco.
Hint Resolve grespectful12_incl.
Hint Resolve rclo12_mon: paco.
Hint Constructors weak_respectful12.

(* User Tactics *)

Ltac pupto12_init := eapply upto12_init; [eauto with paco|].
Ltac pupto12_final := first [eapply upto12_final; [eauto with paco|] | eapply grespectful12_incl].
Ltac pupto12 H := first [eapply upto12_step|eapply upto12_step_under]; [|eapply H|]; [eauto with paco|].

Ltac pfold12_reverse_ :=
    match goal with
    | [|- ?gf (upaco12 _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ _ _] => eapply (paco12_unfold gf)
    | [|- ?gf (?gres (upaco12 _ _ _ _ _ _ _ _ _ _ _ _)) _ _ _ _ _ _ _ _ _ _ _ _] => eapply (paco12_unfold (gf:=compose gf gres))
    end.

Ltac pfold12_reverse := pfold12_reverse_; eauto with paco.

Ltac punfold12_reverse_ H :=
  let PP := type of H in
  match PP with
  | ?gf (upaco12 _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ _ _ => eapply (paco12_fold gf) in H
  | ?gf (?gres (upaco12 _ _ _ _ _ _ _ _ _ _ _ _)) _ _ _ _ _ _ _ _ _ _ _ _ => eapply (paco12_fold (compose gf gres)) in H
  end.

Ltac punfold12_reverse H := punfold12_reverse_ H; eauto with paco.

