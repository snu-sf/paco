Require Export Program.Basics. Open Scope program_scope.
Require Import paco3.
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
Proof.
  intros; destruct H; red; intros.
  eapply gf_mon; [apply IN|intros; eapply MON0; [apply PR|apply LE]].
Qed.
Hint Resolve gfclo3_mon : paco.

Lemma sound3_is_gf: forall clo (UPTO: sound3 clo),
    paco3 (compose gf clo) bot3 <3= paco3 gf bot3.
Proof.
  intros. _punfold PR; [|apply gfclo3_mon, UPTO]. edestruct UPTO.
  eapply (SOUND (paco3 (compose gf clo) bot3)).
  - intros. _punfold PR0; [|apply gfclo3_mon, UPTO].
    eapply (gfclo3_mon UPTO); [apply PR0| intros; destruct PR1; [apply H|destruct H]].
  - pfold. apply PR.
Qed.

Lemma respectful3_is_sound3: respectful3 <1= sound3.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \3/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; [apply MON0|].
  intros. set (rr e0 e1 e2 := exists n, rclo clo n r e0 e1 e2).
  assert (rr x0 x1 x2) by (exists 0; apply PR); clear PR.
  cut (forall n, rclo clo n r <3= gf (rclo clo (S n) r)).
  { intro X; revert x0 x1 x2 H; pcofix CIH; intros.
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

Lemma respectful3_compose
      clo0 clo1
      (RES0: respectful3 clo0)
      (RES1: respectful3 clo1):
  respectful3 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; [apply IN|].
    intros. eapply MON1; [apply PR|apply LE].
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; [apply PR0|apply LE].
    + intros. eapply RESPECTFUL1; [apply LE| apply GF| apply PR0].
Qed.

Lemma grespectful3_mon: monotone3 gres3.
Proof.
  red. intros.
  destruct IN; destruct RES; exists clo; [|eapply MON0; [eapply CLO| eapply LE]].
  constructor; [eapply MON0|].
  intros. eapply RESPECTFUL0; [apply LE0|apply GF|apply PR].
Qed.

Lemma grespectful3_respectful3: respectful3 gres3.
Proof.
  econstructor; [apply grespectful3_mon|intros].
  destruct PR; destruct RES; eapply gf_mon with (r:=clo r).
  eapply RESPECTFUL0; [apply LE|apply GF|apply CLO].
  intros. econstructor; [constructor; [apply MON0|apply RESPECTFUL0]|apply PR].
Qed.

Lemma gfgres3_mon: monotone3 (compose gf gres3).
Proof.
  destruct grespectful3_respectful3.
  unfold monotone3. intros. eapply gf_mon; [eapply IN|].
  intros. eapply MON0;[apply PR|apply LE].
Qed.
Hint Resolve gfgres3_mon : paco.

Lemma grespectful3_greatest: forall clo (RES: respectful3 clo), clo <4= gres3.
Proof. intros. econstructor;[apply RES|apply PR]. Qed.

Lemma grespectful3_incl: forall r, r <3= gres3 r.
Proof.
  intros; eexists (fun x => x).
  - econstructor.
    + red; intros; apply LE, IN.
    + intros; apply GF, PR0.
  - apply PR.
Qed.
Hint Resolve grespectful3_incl.

Lemma grespectful3_compose: forall clo (RES: respectful3 clo) r,
    clo (gres3 r) <3= gres3 r.
Proof.
  intros; eapply grespectful3_greatest with (clo := compose clo gres3); [|apply PR].
  apply respectful3_compose; [apply RES|apply grespectful3_respectful3].
Qed.

Lemma grespectful3_incl_rev: forall r,
    gres3 (paco3 (compose gf gres3) r) <3= paco3 (compose gf gres3) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful3_compose, grespectful3_respectful3.
  destruct grespectful3_respectful3; eapply RESPECTFUL0, PR; intros; [apply grespectful3_incl; right; apply CIH, grespectful3_incl, PR0|].
  _punfold PR0; [|apply gfgres3_mon].
  eapply gfgres3_mon; [apply PR0|].
  intros; destruct PR1.
  - left. eapply paco3_mon; [apply H| apply CIH0].
  - right. eapply CIH0, H.
Qed.

Inductive rclo3 (clo: rel->rel) (r: rel): rel :=
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
  repeat intro. induction IN.
  - econstructor 1. apply LE, R.
  - econstructor 2; [intros; eapply H, PR| apply CLOR'].
  - econstructor 3; [intros; eapply H, PR| apply CLOR'].
Qed.
Hint Resolve rclo3_mon: paco.

Lemma rclo3_base
      clo
      (MON: monotone3 clo):
  clo <4= rclo3 clo.
Proof.
  intros. econstructor 2; [intros; apply PR0|].
  eapply MON; [apply PR|intros; constructor; apply PR0].
Qed.

Lemma rclo3_step
      (clo: rel -> rel) r:
  clo (rclo3 clo r) <3= rclo3 clo r.
Proof.
  intros. econstructor 2; [intros; apply PR0|apply PR].
Qed.

Lemma rclo3_rclo3
      clo r
      (MON: monotone3 clo):
  rclo3 clo (rclo3 clo r) <3= rclo3 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
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
  inversion RES. econstructor; [eapply rclo3_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply GF, R|]. intros.
    apply rclo3_incl. apply PR.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo3_mon; [apply R', PR|apply LE].
    + intros. apply rclo3_rclo3;[apply WEAK_MON0|apply PR].
  - eapply gf_mon; [apply CLOR'|].
    intros. eapply rclo3_mon; [apply R', PR| apply LE].
Qed.

Lemma upto3_init:
  paco3 (compose gf gres3) bot3 <3= paco3 gf bot3.
Proof.
  apply sound3_is_gf.
  apply respectful3_is_sound3.
  apply grespectful3_respectful3.
Qed.

Lemma upto3_final:
  paco3 gf <4= paco3 (compose gf gres3).
Proof.
  pcofix CIH. intros. _punfold PR; [|apply gf_mon]. pfold.
  eapply gf_mon; [|apply grespectful3_incl].
  eapply gf_mon; [apply PR|]. intros. right.
  inversion PR0; [apply CIH, H | apply CIH0, H].
Qed.

Lemma upto3_step
      r clo (RES: weak_respectful3 clo):
  clo (paco3 (compose gf gres3) r) <3= paco3 (compose gf gres3) r.
Proof.
  intros. apply grespectful3_incl_rev.
  assert (RES' := weak_respectful3_respectful3 RES).
  eapply grespectful3_greatest; [apply RES'|].
  eapply rclo3_base; [apply RES|].
  inversion RES. apply PR.
Qed.

Lemma upto3_step_under
      r clo (RES: weak_respectful3 clo):
  clo (gres3 r) <3= gres3 r.
Proof.
  intros. apply weak_respectful3_respectful3 in RES.
  eapply grespectful3_compose; [apply RES|].
  econstructor 2; [intros; constructor 1; apply PR0 | apply PR].
Qed.

End Respectful3.

Lemma rclo3_mon_gen T0 T1 T2 (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) clo clo' r r' e0 e1 e2
      (REL: rclo3 gf clo r e0 e1 e2)
      (LEgf: gf <4= gf')
      (LEclo: clo <4= clo')
      (LEr: r <3= r') :
  rclo3 gf' clo' r' e0 e1 e2.
Proof.
  induction REL.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR| apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR| apply LEgf, CLOR'].
Qed.

Lemma grespectful3_impl T0 T1 T2 (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r x0 x1 x2
    (PR: gres3 gf r x0 x1 x2)
    (EQ: forall r x0 x1 x2, gf r x0 x1 x2 <-> gf' r x0 x1 x2):
  gres3 gf' r x0 x1 x2.
Proof.
  intros. destruct PR. econstructor; [|apply CLO].
  destruct RES. econstructor; [apply MON0|].
  intros. eapply EQ. eapply RESPECTFUL0; [apply LE| |apply PR].
  intros. eapply EQ. apply GF, PR0.
Qed.

Lemma grespectful3_iff T0 T1 T2 (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r x0 x1 x2
    (EQ: forall r x0 x1 x2, gf r x0 x1 x2 <-> gf' r x0 x1 x2):
  gres3 gf r x0 x1 x2 <-> gres3 gf' r x0 x1 x2.
Proof.
  split; intros.
  - eapply grespectful3_impl; [apply H | apply EQ].
  - eapply grespectful3_impl; [apply H | split; apply EQ].
Qed.

Hint Constructors sound3.
Hint Constructors respectful3.
Hint Constructors gres3.
Hint Resolve gfclo3_mon : paco.
Hint Resolve gfgres3_mon : paco.
Hint Resolve grespectful3_incl.
Hint Resolve rclo3_mon: paco.
Hint Constructors weak_respectful3.

(* User Tactics *)

Ltac pupto3_init := eapply upto3_init; [eauto with paco|].
Ltac pupto3_final := first [eapply upto3_final; [eauto with paco|] | eapply grespectful3_incl].
Ltac pupto3 H := first [eapply upto3_step|eapply upto3_step_under]; [|eapply H|]; [eauto with paco|].

Ltac pfold3_reverse_ :=
    match goal with
    | [|- ?gf (upaco3 _ _ _) _ _ _] => eapply (paco3_unfold gf)
    | [|- ?gf (?gres (upaco3 _ _ _)) _ _ _] => eapply (paco3_unfold (gf:=compose gf gres))
    end.

Ltac pfold3_reverse := pfold3_reverse_; eauto with paco.

Ltac punfold3_reverse_ H :=
  let PP := type of H in
  match PP with
  | ?gf (upaco3 _ _ _) _ _ _ => eapply (paco3_fold gf) in H
  | ?gf (?gres (upaco3 _ _ _)) _ _ _ => eapply (paco3_fold (compose gf gres)) in H
  end.

Ltac punfold3_reverse H := punfold3_reverse_ H; eauto with paco.

