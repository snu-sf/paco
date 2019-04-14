Require Export Program.Basics. Open Scope program_scope.
Require Import paco7 pacotac.
Set Implicit Arguments.

Section Companion7.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.

Local Notation rel := (rel7 T0 T1 T2 T3 T4 T5 T6).

Section Companion7_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone7 gf.

(** 
  Compatibility, Companion & Guarded Companion
*)

Structure compatible7 (clo: rel -> rel) : Prop :=
  compat7_intro {
      compat7_mon: monotone7 clo;
      compat7_compat : forall r,
          clo (gf r) <7= gf (clo r);
    }.

Inductive cpn7 (r: rel) x0 x1 x2 x3 x4 x5 x6 : Prop :=
| cpn7_intro
    clo
    (COM: compatible7 clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6)
.

Definition fcpn7 := compose gf cpn7.

Lemma cpn7_mon: monotone7 cpn7.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat7_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn7_compat: compatible7 cpn7.
Proof.
  econstructor; [apply cpn7_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat7_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn7_greatest: forall clo (COM: compatible7 clo), clo <8= cpn7.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn7_cpn: forall r,
    cpn7 (cpn7 r) <7= cpn7 r.
Proof.
  intros. exists (compose cpn7 cpn7); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn7_mon; [apply IN|].
    intros. eapply cpn7_mon; [apply PR0|apply LE].
  - intros. eapply (compat7_compat cpn7_compat).
    eapply cpn7_mon; [apply PR0|].
    intros. eapply (compat7_compat cpn7_compat), PR1. 
Qed.

Lemma monotone7_compose (clo1 clo2: rel -> rel)
      (MON1: monotone7 clo1)
      (MON2: monotone7 clo2):
  monotone7 (compose clo1 clo2).
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma fcpn7_mon: monotone7 fcpn7.
Proof.
  apply monotone7_compose. apply gf_mon. apply cpn7_mon.
Qed.

Lemma fcpn7_sound:
  paco7 fcpn7 bot7 <7= paco7 gf bot7.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \7/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn7 n (paco7 fcpn7 bot7) x0 x1 x2 x3 x4 x5 x6) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn7 n (paco7 fcpn7 bot7) <7= gf (rclo cpn7 (S n) (paco7 fcpn7 bot7))).
  { intro X. revert x0 x1 x2 x3 x4 x5 x6 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply fcpn7_mon].
    + intros. right. eapply cpn7_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat7_compat cpn7_compat).
        eapply (compat7_mon cpn7_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo7 (clo: rel->rel) (r: rel): rel :=
| rclo7_base
    x0 x1 x2 x3 x4 x5 x6
    (IN: r x0 x1 x2 x3 x4 x5 x6):
    @rclo7 clo r x0 x1 x2 x3 x4 x5 x6
| rclo7_clo'
    r' x0 x1 x2 x3 x4 x5 x6
    (LE: r' <7= rclo7 clo r)
    (IN: clo r' x0 x1 x2 x3 x4 x5 x6):
    @rclo7 clo r x0 x1 x2 x3 x4 x5 x6
.           

Structure wcompatible7 (clo: rel -> rel) : Prop :=
  wcompat7_intro {
      wcompat7_mon: monotone7 clo;
      wcompat7_wcompat : forall r,
          clo (gf r) <7= gf (rclo7 (clo \8/ cpn7) r);
    }.

Lemma rclo7_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5 x6
      (IN: @rclo7 clo r x0 x1 x2 x3 x4 x5 x6)
      (LEclo: clo <8= clo')
      (LEr: r <7= r') :
  @rclo7 clo' r' x0 x1 x2 x3 x4 x5 x6.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo7_mon clo:
  monotone7 (rclo7 clo).
Proof.
  repeat intro. eapply rclo7_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo7_clo clo r:
  clo (rclo7 clo r) <7= rclo7 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo7_rclo clo r:
  rclo7 clo (rclo7 clo r) <7= rclo7 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo7_compose clo r:
  rclo7 (rclo7 clo) r <7= rclo7 clo r.
Proof.
  intros. induction PR.
  - apply rclo7_base, IN.
  - apply rclo7_rclo.
    eapply rclo7_mon; [apply IN|apply H].
Qed.

Lemma rclo7_compat clo
      (COM: compatible7 clo):
  compatible7 (rclo7 clo).
Proof.
  econstructor.
  - apply rclo7_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo7_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo7_clo. apply PR.
Qed.

Lemma wcompat7_compat  clo
      (WCOM: wcompatible7 clo):
  compatible7 (rclo7 (clo \8/ cpn7)).
Proof.
  econstructor; [eapply rclo7_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply IN|]. intros.
    apply rclo7_base. apply PR.
  - destruct IN as [IN|IN].
    + eapply gf_mon.
      * eapply WCOM. eapply WCOM; [apply IN|apply H].
      * intros. apply rclo7_rclo, PR.
    + eapply gf_mon; [|intros; apply rclo7_clo; right; apply PR].
      apply (compat7_compat cpn7_compat).
      eapply cpn7_mon; [apply IN|apply H].
Qed.

Lemma wcompat7_sound clo
      (WCOM: wcompatible7 clo):
  clo <8= cpn7.
Proof.
  intros. exists (rclo7 (clo \8/ cpn7)).
  - apply wcompat7_compat, WCOM.
  - apply rclo7_clo.
    left. eapply WCOM. apply PR.
    intros. apply rclo7_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn7_base: forall r, r <7= cpn7 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
  - apply PR.
Qed.

Lemma cpn7_step r:
  fcpn7 r <7= cpn7 r.
Proof.
  intros. eapply cpn7_cpn. exists gf.
  - econstructor. apply gf_mon. intros; apply PR0.
  - apply PR.
Qed.

Lemma cpn7_from_upaco r:
  upaco7 fcpn7 r <7= cpn7 r.
Proof.
  eapply wcompat7_sound.
  econstructor; [apply upaco7_mon|].
  intros. destruct PR as [PR|PR].
  - _punfold PR; [|apply fcpn7_mon]. 
    eapply gf_mon; [apply PR|].
    intros. apply rclo7_clo; right.
    eapply cpn7_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo7_clo; left.
      left. eapply paco7_mon; [apply H|].
      intros. apply rclo7_clo; right. apply cpn7_step.
      eapply gf_mon; [apply PR1|].
      intros. apply cpn7_base, rclo7_base, PR2.
    + apply rclo7_clo; right. apply cpn7_step.
      eapply gf_mon; [apply H|].
      intros. apply cpn7_base, rclo7_base, PR1.
  - eapply gf_mon. apply PR.
    intros. apply rclo7_base, PR0. 
Qed.

Lemma cpn7_from_paco r:
  paco7 fcpn7 r <7= cpn7 r.
Proof. intros. apply cpn7_from_upaco. left. apply PR. Qed.

Lemma fcpn7_from_paco r:
  paco7 fcpn7 r <7= fcpn7 r.
Proof.
  intros. _punfold PR; [|apply fcpn7_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn7_cpn.
  eapply cpn7_mon; [apply PR0|].
  apply cpn7_from_upaco.
Qed.

Lemma fcpn7_to_paco r:
  fcpn7 r <7= paco7 fcpn7 r.
Proof.
  intros. pfold. eapply fcpn7_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn7_complete:
  paco7 gf bot7 <7= cpn7 bot7.
Proof.
  intros. apply cpn7_from_paco.
  eapply paco7_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn7_base].
  - intros. apply PR0.
Qed.

Lemma cpn7_init:
  cpn7 bot7 <7= paco7 gf bot7.
Proof.
  intros. apply fcpn7_sound, fcpn7_to_paco, (compat7_compat cpn7_compat).
  eapply cpn7_mon; [apply PR|contradiction].
Qed.

Lemma cpn7_clo
      r clo (LE: clo <8= cpn7):
  clo (cpn7 r) <7= cpn7 r.
Proof.
  intros. apply cpn7_cpn, LE, PR.
Qed.

Lemma cpn7_unfold:
  cpn7 bot7 <7= fcpn7 bot7.
Proof.
  intros. apply cpn7_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn7_complete, PR0.
Qed.

Lemma fcpn7_clo
      r clo (LE: clo <8= cpn7):
  clo (fcpn7 r) <7= fcpn7 r.
Proof.
  intros. apply LE, (compat7_compat cpn7_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn7_cpn, PR0.
Qed.

Lemma cpn7_final: forall r, upaco7 gf r <7= cpn7 r.
Proof.
  intros. eapply cpn7_from_upaco.
  intros. eapply upaco7_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn7_base, PR1.
Qed.

Lemma fcpn7_final: forall r, paco7 gf r <7= fcpn7 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn7_final].
Qed.

Lemma cpn7_algebra r :
  r <7= gf r -> r <7= cpn7 bot7.
Proof.
  intros. apply cpn7_final. left.
  revert x0 x1 x2 x3 x4 x5 x6 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion7_main.

Lemma cpn7_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 r
      (IN: @cpn7 gf bot7 x0 x1 x2 x3 x4 x5 x6)
      (MONgf: monotone7 gf)
      (MONgf': monotone7 gf')
      (LE: gf <8= gf'):
  @cpn7 gf' r x0 x1 x2 x3 x4 x5 x6.
Proof.
  apply cpn7_init in IN; [|apply MONgf].
  apply cpn7_final; [apply MONgf'|].
  left. eapply paco7_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn7_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 r
      (IN: @fcpn7 gf bot7 x0 x1 x2 x3 x4 x5 x6)
      (MONgf: monotone7 gf)
      (MONgf': monotone7 gf')
      (LE: gf <8= gf'):
  @fcpn7 gf' r x0 x1 x2 x3 x4 x5 x6.
Proof.
  apply LE. eapply MONgf. apply IN.
  intros. eapply cpn7_mon_bot; eassumption.
Qed.

End Companion7.

Hint Unfold fcpn7 : paco.

Hint Resolve cpn7_base : paco.
Hint Resolve cpn7_step : paco.
Hint Constructors rclo7 : paco.
Hint Resolve rclo7_clo : paco.
