Require Export Program.Basics. Open Scope program_scope.
Require Import paco4.
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
Proof.
  intros; destruct H; red; intros.
  eapply gf_mon; [apply IN|intros; eapply MON0; [apply PR|apply LE]].
Qed.
Hint Resolve gfclo4_mon : paco.

Lemma sound4_is_gf: forall clo (UPTO: sound4 clo),
    paco4 (compose gf clo) bot4 <4= paco4 gf bot4.
Proof.
  intros. _punfold PR; [|apply gfclo4_mon, UPTO]. edestruct UPTO.
  eapply (SOUND (paco4 (compose gf clo) bot4)).
  - intros. _punfold PR0; [|apply gfclo4_mon, UPTO].
    eapply (gfclo4_mon UPTO); [apply PR0| intros; destruct PR1; [apply H|destruct H]].
  - pfold. apply PR.
Qed.

Lemma respectful4_is_sound4: respectful4 <1= sound4.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \4/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; [apply MON0|].
  intros. set (rr e0 e1 e2 e3 := exists n, rclo clo n r e0 e1 e2 e3).
  assert (rr x0 x1 x2 x3) by (exists 0; apply PR); clear PR.
  cut (forall n, rclo clo n r <4= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 x3 H; pcofix CIH; intros.
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

Lemma respectful4_compose
      clo0 clo1
      (RES0: respectful4 clo0)
      (RES1: respectful4 clo1):
  respectful4 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; [apply IN|].
    intros. eapply MON1; [apply PR|apply LE].
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; [apply PR0|apply LE].
    + intros. eapply RESPECTFUL1; [apply LE| apply GF| apply PR0].
Qed.

Lemma grespectful4_mon: monotone4 gres4.
Proof.
  red. intros.
  destruct IN; destruct RES; exists clo; [|eapply MON0; [eapply CLO| eapply LE]].
  constructor; [eapply MON0|].
  intros. eapply RESPECTFUL0; [apply LE0|apply GF|apply PR].
Qed.

Lemma grespectful4_respectful4: respectful4 gres4.
Proof.
  econstructor; [apply grespectful4_mon|intros].
  destruct PR; destruct RES; eapply gf_mon with (r:=clo r).
  eapply RESPECTFUL0; [apply LE|apply GF|apply CLO].
  intros. econstructor; [constructor; [apply MON0|apply RESPECTFUL0]|apply PR].
Qed.

Lemma gfgres4_mon: monotone4 (compose gf gres4).
Proof.
  destruct grespectful4_respectful4.
  unfold monotone4. intros. eapply gf_mon; [eapply IN|].
  intros. eapply MON0;[apply PR|apply LE].
Qed.
Hint Resolve gfgres4_mon : paco.

Lemma grespectful4_greatest: forall clo (RES: respectful4 clo), clo <5= gres4.
Proof. intros. econstructor;[apply RES|apply PR]. Qed.

Lemma grespectful4_incl: forall r, r <4= gres4 r.
Proof.
  intros; eexists (fun x => x).
  - econstructor.
    + red; intros; apply LE, IN.
    + intros; apply GF, PR0.
  - apply PR.
Qed.
Hint Resolve grespectful4_incl.

Lemma grespectful4_compose: forall clo (RES: respectful4 clo) r,
    clo (gres4 r) <4= gres4 r.
Proof.
  intros; eapply grespectful4_greatest with (clo := compose clo gres4); [|apply PR].
  apply respectful4_compose; [apply RES|apply grespectful4_respectful4].
Qed.

Lemma grespectful4_incl_rev: forall r,
    gres4 (paco4 (compose gf gres4) r) <4= paco4 (compose gf gres4) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful4_compose, grespectful4_respectful4.
  destruct grespectful4_respectful4; eapply RESPECTFUL0, PR; intros; [apply grespectful4_incl; right; apply CIH, grespectful4_incl, PR0|].
  _punfold PR0; [|apply gfgres4_mon].
  eapply gfgres4_mon; [apply PR0|].
  intros; destruct PR1.
  - left. eapply paco4_mon; [apply H| apply CIH0].
  - right. eapply CIH0, H.
Qed.

Inductive rclo4 (clo: rel->rel) (r: rel): rel :=
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
  repeat intro. induction IN.
  - econstructor 1. apply LE, R.
  - econstructor 2; [intros; eapply H, PR| apply CLOR'].
  - econstructor 3; [intros; eapply H, PR| apply CLOR'].
Qed.
Hint Resolve rclo4_mon: paco.

Lemma rclo4_base
      clo
      (MON: monotone4 clo):
  clo <5= rclo4 clo.
Proof.
  intros. econstructor 2; [intros; apply PR0|].
  eapply MON; [apply PR|intros; constructor; apply PR0].
Qed.

Lemma rclo4_step
      (clo: rel -> rel) r:
  clo (rclo4 clo r) <4= rclo4 clo r.
Proof.
  intros. econstructor 2; [intros; apply PR0|apply PR].
Qed.

Lemma rclo4_rclo4
      clo r
      (MON: monotone4 clo):
  rclo4 clo (rclo4 clo r) <4= rclo4 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
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
  inversion RES. econstructor; [eapply rclo4_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply GF, R|]. intros.
    apply rclo4_incl. apply PR.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo4_mon; [apply R', PR|apply LE].
    + intros. apply rclo4_rclo4;[apply WEAK_MON0|apply PR].
  - eapply gf_mon; [apply CLOR'|].
    intros. eapply rclo4_mon; [apply R', PR| apply LE].
Qed.

Lemma upto4_init:
  paco4 (compose gf gres4) bot4 <4= paco4 gf bot4.
Proof.
  apply sound4_is_gf.
  apply respectful4_is_sound4.
  apply grespectful4_respectful4.
Qed.

Lemma upto4_final:
  paco4 gf <5= paco4 (compose gf gres4).
Proof.
  pcofix CIH. intros. _punfold PR; [|apply gf_mon]. pfold.
  eapply gf_mon; [|apply grespectful4_incl].
  eapply gf_mon; [apply PR|]. intros. right.
  inversion PR0; [apply CIH, H | apply CIH0, H].
Qed.

Lemma upto4_step
      r clo (RES: weak_respectful4 clo):
  clo (paco4 (compose gf gres4) r) <4= paco4 (compose gf gres4) r.
Proof.
  intros. apply grespectful4_incl_rev.
  assert (RES' := weak_respectful4_respectful4 RES).
  eapply grespectful4_greatest; [apply RES'|].
  eapply rclo4_base; [apply RES|].
  inversion RES. apply PR.
Qed.

Lemma upto4_step_under
      r clo (RES: weak_respectful4 clo):
  clo (gres4 r) <4= gres4 r.
Proof.
  intros. apply weak_respectful4_respectful4 in RES.
  eapply grespectful4_compose; [apply RES|].
  econstructor 2; [intros; constructor 1; apply PR0 | apply PR].
Qed.

End Respectful4.

Lemma rclo4_mon_gen T0 T1 T2 T3 (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) clo clo' r r' e0 e1 e2 e3
      (REL: rclo4 gf clo r e0 e1 e2 e3)
      (LEgf: gf <5= gf')
      (LEclo: clo <5= clo')
      (LEr: r <4= r') :
  rclo4 gf' clo' r' e0 e1 e2 e3.
Proof.
  induction REL.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR| apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR| apply LEgf, CLOR'].
Qed.

Lemma grespectful4_impl T0 T1 T2 T3 (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) r x0 x1 x2 x3
    (PR: gres4 gf r x0 x1 x2 x3)
    (EQ: forall r x0 x1 x2 x3, gf r x0 x1 x2 x3 <-> gf' r x0 x1 x2 x3):
  gres4 gf' r x0 x1 x2 x3.
Proof.
  intros. destruct PR. econstructor; [|apply CLO].
  destruct RES. econstructor; [apply MON0|].
  intros. eapply EQ. eapply RESPECTFUL0; [apply LE| |apply PR].
  intros. eapply EQ. apply GF, PR0.
Qed.

Lemma grespectful4_iff T0 T1 T2 T3 (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) r x0 x1 x2 x3
    (EQ: forall r x0 x1 x2 x3, gf r x0 x1 x2 x3 <-> gf' r x0 x1 x2 x3):
  gres4 gf r x0 x1 x2 x3 <-> gres4 gf' r x0 x1 x2 x3.
Proof.
  split; intros.
  - eapply grespectful4_impl; [apply H | apply EQ].
  - eapply grespectful4_impl; [apply H | split; apply EQ].
Qed.

Hint Constructors sound4.
Hint Constructors respectful4.
Hint Constructors gres4.
Hint Resolve gfclo4_mon : paco.
Hint Resolve gfgres4_mon : paco.
Hint Resolve grespectful4_incl.
Hint Resolve rclo4_mon: paco.
Hint Constructors weak_respectful4.

(* User Tactics *)

Ltac pupto4_init := eapply upto4_init; [eauto with paco|].
Ltac pupto4_final := first [eapply upto4_final; [eauto with paco|] | eapply grespectful4_incl].
Ltac pupto4 H := first [eapply upto4_step|eapply upto4_step_under]; [|eapply H|]; [eauto with paco|].

Ltac pfold4_reverse_ :=
    match goal with
    | [|- ?gf (upaco4 _ _ _ _) _ _ _ _] => eapply (paco4_unfold gf)
    | [|- ?gf (?gres (upaco4 _ _ _ _)) _ _ _ _] => eapply (paco4_unfold (gf:=compose gf gres))
    end.

Ltac pfold4_reverse := pfold4_reverse_; eauto with paco.

Ltac punfold4_reverse_ H :=
  let PP := type of H in
  match PP with
  | ?gf (upaco4 _ _ _ _) _ _ _ _ => eapply (paco4_fold gf) in H
  | ?gf (?gres (upaco4 _ _ _ _)) _ _ _ _ => eapply (paco4_fold (compose gf gres)) in H
  end.

Ltac punfold4_reverse H := punfold4_reverse_ H; eauto with paco.

