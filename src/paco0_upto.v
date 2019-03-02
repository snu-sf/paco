Require Export Program.Basics. Open Scope program_scope.
Require Import paco0.
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
Proof.
  intros; destruct H; red; intros.
  eapply gf_mon; [apply IN|intros; eapply MON0; [apply PR|apply LE]].
Qed.
Hint Resolve gfclo0_mon : paco.

Lemma sound0_is_gf: forall clo (UPTO: sound0 clo),
    paco0 (compose gf clo) bot0 <0= paco0 gf bot0.
Proof.
  intros. _punfold PR; [|apply gfclo0_mon, UPTO]. edestruct UPTO.
  eapply (SOUND (paco0 (compose gf clo) bot0)).
  - intros. _punfold PR0; [|apply gfclo0_mon, UPTO].
    eapply (gfclo0_mon UPTO); [apply PR0| intros; destruct PR1; [apply H|destruct H]].
  - pfold. apply PR.
Qed.

Lemma respectful0_is_sound0: respectful0 <1= sound0.
Proof.
  intro clo.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \0/ clo (rclo clo n' r)
         end).
  intros. destruct PR. econstructor; [apply MON0|].
  intros. set (rr := exists n, rclo clo n r).
  assert (rr) by (exists 0; apply PR); clear PR.
  cut (forall n, rclo clo n r <0= gf (rclo clo (S n) r)).
  { intro X; revert H; pcofix CIH; intros.
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

Lemma respectful0_compose
      clo0 clo1
      (RES0: respectful0 clo0)
      (RES1: respectful0 clo1):
  respectful0 (compose clo0 clo1).
Proof.
  intros. destruct RES0, RES1.
  econstructor.
  - repeat intro. eapply MON0; [apply IN|].
    intros. eapply MON1; [apply PR|apply LE].
  - intros. eapply RESPECTFUL0; [| |apply PR].
    + intros. eapply MON1; [apply PR0|apply LE].
    + intros. eapply RESPECTFUL1; [apply LE| apply GF| apply PR0].
Qed.

Lemma grespectful0_mon: monotone0 gres0.
Proof.
  red. intros.
  destruct IN; destruct RES; exists clo; [|eapply MON0; [eapply CLO| eapply LE]].
  constructor; [eapply MON0|].
  intros. eapply RESPECTFUL0; [apply LE0|apply GF|apply PR].
Qed.

Lemma grespectful0_respectful0: respectful0 gres0.
Proof.
  econstructor; [apply grespectful0_mon|intros].
  destruct PR; destruct RES; eapply gf_mon with (r:=clo r).
  eapply RESPECTFUL0; [apply LE|apply GF|apply CLO].
  intros. econstructor; [constructor; [apply MON0|apply RESPECTFUL0]|apply PR].
Qed.

Lemma gfgres0_mon: monotone0 (compose gf gres0).
Proof.
  destruct grespectful0_respectful0.
  unfold monotone0. intros. eapply gf_mon; [eapply IN|].
  intros. eapply MON0;[apply PR|apply LE].
Qed.
Hint Resolve gfgres0_mon : paco.

Lemma grespectful0_greatest: forall clo (RES: respectful0 clo), clo <1= gres0.
Proof. intros. econstructor;[apply RES|apply PR]. Qed.

Lemma grespectful0_incl: forall r, r <0= gres0 r.
Proof.
  intros; eexists (fun x => x).
  - econstructor.
    + red; intros; apply LE, IN.
    + intros; apply GF, PR0.
  - apply PR.
Qed.
Hint Resolve grespectful0_incl.

Lemma grespectful0_compose: forall clo (RES: respectful0 clo) r,
    clo (gres0 r) <0= gres0 r.
Proof.
  intros; eapply grespectful0_greatest with (clo := compose clo gres0); [|apply PR].
  apply respectful0_compose; [apply RES|apply grespectful0_respectful0].
Qed.

Lemma grespectful0_incl_rev: forall r,
    gres0 (paco0 (compose gf gres0) r) <0= paco0 (compose gf gres0) r.
Proof.
  intro r; pcofix CIH; intros; pfold.
  eapply gf_mon, grespectful0_compose, grespectful0_respectful0.
  destruct grespectful0_respectful0; eapply RESPECTFUL0, PR; intros; [apply grespectful0_incl; right; apply CIH, grespectful0_incl, PR0|].
  _punfold PR0; [|apply gfgres0_mon].
  eapply gfgres0_mon; [apply PR0|].
  intros; destruct PR1.
  - left. eapply paco0_mon; [apply H| apply CIH0].
  - right. eapply CIH0, H.
Qed.

Inductive rclo0 (clo: rel->rel) (r: rel): rel :=
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
  repeat intro. induction IN.
  - econstructor 1. apply LE, R.
  - econstructor 2; [intros; eapply H, PR| apply CLOR'].
  - econstructor 3; [intros; eapply H, PR| apply CLOR'].
Qed.
Hint Resolve rclo0_mon: paco.

Lemma rclo0_base
      clo
      (MON: monotone0 clo):
  clo <1= rclo0 clo.
Proof.
  intros. econstructor 2; [intros; apply PR0|].
  eapply MON; [apply PR|intros; constructor; apply PR0].
Qed.

Lemma rclo0_step
      (clo: rel -> rel) r:
  clo (rclo0 clo r) <0= rclo0 clo r.
Proof.
  intros. econstructor 2; [intros; apply PR0|apply PR].
Qed.

Lemma rclo0_rclo0
      clo r
      (MON: monotone0 clo):
  rclo0 clo (rclo0 clo r) <0= rclo0 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
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
  inversion RES. econstructor; [eapply rclo0_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply GF, R|]. intros.
    apply rclo0_incl. apply PR.
  - eapply gf_mon.
    + eapply WEAK_RESPECTFUL0; [|apply H|apply CLOR'].
      intros. eapply rclo0_mon; [apply R', PR|apply LE].
    + intros. apply rclo0_rclo0;[apply WEAK_MON0|apply PR].
  - eapply gf_mon; [apply CLOR'|].
    intros. eapply rclo0_mon; [apply R', PR| apply LE].
Qed.

Lemma upto0_init:
  paco0 (compose gf gres0) bot0 <0= paco0 gf bot0.
Proof.
  apply sound0_is_gf.
  apply respectful0_is_sound0.
  apply grespectful0_respectful0.
Qed.

Lemma upto0_final:
  paco0 gf <1= paco0 (compose gf gres0).
Proof.
  pcofix CIH. intros. _punfold PR; [|apply gf_mon]. pfold.
  eapply gf_mon; [|apply grespectful0_incl].
  eapply gf_mon; [apply PR|]. intros. right.
  inversion PR0; [apply CIH, H | apply CIH0, H].
Qed.

Lemma upto0_step
      r clo (RES: respectful0 clo):
  clo (paco0 (compose gf gres0) r) <0= paco0 (compose gf gres0) r.
Proof.
  intros. apply grespectful0_incl_rev.
  eapply grespectful0_greatest; [apply RES|apply PR].
Qed.

Lemma upto0_step_under
      r clo (RES: respectful0 clo):
  clo (gres0 r) <0= gres0 r.
Proof.
  intros. eapply grespectful0_compose; [apply RES|apply PR].
Qed.

End Respectful0.

Lemma rclo0_mon_gen (gf gf': rel0 -> rel0) clo clo' r r'
      (REL: rclo0 gf clo r)
      (LEgf: gf <1= gf')
      (LEclo: clo <1= clo')
      (LEr: r <0= r') :
  rclo0 gf' clo' r'.
Proof.
  induction REL.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR| apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR| apply LEgf, CLOR'].
Qed.

Lemma grespectful0_impl (gf gf': rel0 -> rel0) r
    (PR: gres0 gf r)
    (EQ: forall r, gf r <-> gf' r):
  gres0 gf' r.
Proof.
  intros. destruct PR. econstructor; [|apply CLO].
  destruct RES. econstructor; [apply MON0|].
  intros. eapply EQ. eapply RESPECTFUL0; [apply LE| |apply PR].
  intros. eapply EQ. apply GF, PR0.
Qed.

Lemma grespectful0_iff (gf gf': rel0 -> rel0) r
    (EQ: forall r, gf r <-> gf' r):
  gres0 gf r <-> gres0 gf' r.
Proof.
  split; intros.
  - eapply grespectful0_impl; [apply H | apply EQ].
  - eapply grespectful0_impl; [apply H | split; apply EQ].
Qed.

Hint Constructors sound0.
Hint Constructors respectful0.
Hint Constructors gres0.
Hint Resolve gfclo0_mon : paco.
Hint Resolve gfgres0_mon : paco.
Hint Resolve grespectful0_incl.
Hint Resolve rclo0_mon: paco.
Hint Constructors weak_respectful0.

Ltac pupto0_init := eapply upto0_init; [eauto with paco|].
Ltac pupto0_final := first [eapply upto0_final; [eauto with paco|] | eapply grespectful0_incl].
Ltac pupto0 H := first [eapply upto0_step|eapply upto0_step_under]; [|(eapply H || eapply weak_respectful0_respectful0, H)|]; [eauto with paco|].

