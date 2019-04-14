Require Export Program.Basics. Open Scope program_scope.
Require Import paco6 pacotac.
Set Implicit Arguments.

Section Companion6.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.

Local Notation rel := (rel6 T0 T1 T2 T3 T4 T5).

Section Companion6_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone6 gf.

(** 
  Compatibility, Companion & Guarded Companion
*)

Structure compatible6 (clo: rel -> rel) : Prop :=
  compat6_intro {
      compat6_mon: monotone6 clo;
      compat6_compat : forall r,
          clo (gf r) <6= gf (clo r);
    }.

Inductive cpn6 (r: rel) x0 x1 x2 x3 x4 x5 : Prop :=
| cpn6_intro
    clo
    (COM: compatible6 clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5)
.

Definition fcpn6 := compose gf cpn6.

Lemma cpn6_mon: monotone6 cpn6.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat6_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn6_compat: compatible6 cpn6.
Proof.
  econstructor; [apply cpn6_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat6_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn6_greatest: forall clo (COM: compatible6 clo), clo <7= cpn6.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn6_cpn: forall r,
    cpn6 (cpn6 r) <6= cpn6 r.
Proof.
  intros. exists (compose cpn6 cpn6); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn6_mon; [apply IN|].
    intros. eapply cpn6_mon; [apply PR0|apply LE].
  - intros. eapply (compat6_compat cpn6_compat).
    eapply cpn6_mon; [apply PR0|].
    intros. eapply (compat6_compat cpn6_compat), PR1. 
Qed.

Lemma fcpn6_mon: monotone6 fcpn6.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn6_mon; [apply PR|apply LE].
Qed.

Lemma fcpn6_sound:
  paco6 fcpn6 bot6 <6= paco6 gf bot6.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \6/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn6 n (paco6 fcpn6 bot6) x0 x1 x2 x3 x4 x5) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn6 n (paco6 fcpn6 bot6) <6= gf (rclo cpn6 (S n) (paco6 fcpn6 bot6))).
  { intro X. revert x0 x1 x2 x3 x4 x5 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply fcpn6_mon].
    + intros. right. eapply cpn6_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat6_compat cpn6_compat).
        eapply (compat6_mon cpn6_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo6 (clo: rel->rel) (r: rel): rel :=
| rclo6_base
    x0 x1 x2 x3 x4 x5
    (IN: r x0 x1 x2 x3 x4 x5):
    @rclo6 clo r x0 x1 x2 x3 x4 x5
| rclo6_clo'
    r' x0 x1 x2 x3 x4 x5
    (LE: r' <6= rclo6 clo r)
    (IN: clo r' x0 x1 x2 x3 x4 x5):
    @rclo6 clo r x0 x1 x2 x3 x4 x5
.           

Structure wcompatible6 (clo: rel -> rel) : Prop :=
  wcompat6_intro {
      wcompat6_mon: monotone6 clo;
      wcompat6_wcompat : forall r,
          clo (gf r) <6= gf (rclo6 (clo \7/ cpn6) r);
    }.


Lemma rclo6_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5
      (IN: @rclo6 clo r x0 x1 x2 x3 x4 x5)
      (LEclo: clo <7= clo')
      (LEr: r <6= r') :
  @rclo6 clo' r' x0 x1 x2 x3 x4 x5.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo6_mon clo:
  monotone6 (rclo6 clo).
Proof.
  repeat intro. eapply rclo6_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo6_clo clo r:
  clo (rclo6 clo r) <6= rclo6 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo6_rclo clo r:
  rclo6 clo (rclo6 clo r) <6= rclo6 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo6_compose clo r:
  rclo6 (rclo6 clo) r <6= rclo6 clo r.
Proof.
  intros. induction PR.
  - apply rclo6_base, IN.
  - apply rclo6_rclo.
    eapply rclo6_mon; [apply IN|apply H].
Qed.

Lemma rclo6_compat clo
      (COM: compatible6 clo):
  compatible6 (rclo6 clo).
Proof.
  econstructor.
  - apply rclo6_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo6_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo6_clo. apply PR.
Qed.

Lemma wcompat6_compat  clo
      (WCOM: wcompatible6 clo):
  compatible6 (rclo6 (clo \7/ cpn6)).
Proof.
  econstructor; [eapply rclo6_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply IN|]. intros.
    apply rclo6_base. apply PR.
  - destruct IN as [IN|IN].
    + eapply gf_mon.
      * eapply WCOM. eapply WCOM; [apply IN|apply H].
      * intros. apply rclo6_rclo, PR.
    + eapply gf_mon; [|intros; apply rclo6_clo; right; apply PR].
      apply (compat6_compat cpn6_compat).
      eapply cpn6_mon; [apply IN|apply H].
Qed.

Lemma wcompat6_sound clo
      (WCOM: wcompatible6 clo):
  clo <7= cpn6.
Proof.
  intros. exists (rclo6 (clo \7/ cpn6)).
  - apply wcompat6_compat, WCOM.
  - apply rclo6_clo.
    left. eapply WCOM. apply PR.
    intros. apply rclo6_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn6_base: forall r, r <6= cpn6 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
  - apply PR.
Qed.

Lemma cpn6_step r:
  fcpn6 r <6= cpn6 r.
Proof.
  intros. eapply cpn6_cpn. exists gf.
  - econstructor. apply gf_mon. intros; apply PR0.
  - apply PR.
Qed.

Lemma cpn6_from_upaco r:
  upaco6 fcpn6 r <6= cpn6 r.
Proof.
  eapply wcompat6_sound.
  econstructor; [apply upaco6_mon|].
  intros. destruct PR as [PR|PR].
  - _punfold PR; [|apply fcpn6_mon]. 
    eapply gf_mon; [apply PR|].
    intros. apply rclo6_clo; right.
    eapply cpn6_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo6_clo; left.
      left. eapply paco6_mon; [apply H|].
      intros. apply rclo6_clo; right. apply cpn6_step.
      eapply gf_mon; [apply PR1|].
      intros. apply cpn6_base, rclo6_base, PR2.
    + apply rclo6_clo; right. apply cpn6_step.
      eapply gf_mon; [apply H|].
      intros. apply cpn6_base, rclo6_base, PR1.
  - eapply gf_mon. apply PR.
    intros. apply rclo6_base, PR0. 
Qed.

Lemma cpn6_from_paco r:
  paco6 fcpn6 r <6= cpn6 r.
Proof. intros. apply cpn6_from_upaco. left. apply PR. Qed.

Lemma fcpn6_from_paco r:
  paco6 fcpn6 r <6= fcpn6 r.
Proof.
  intros. _punfold PR; [|apply fcpn6_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn6_cpn.
  eapply cpn6_mon; [apply PR0|].
  apply cpn6_from_upaco.
Qed.

Lemma fcpn6_to_paco r:
  fcpn6 r <6= paco6 fcpn6 r.
Proof.
  intros. pfold. eapply fcpn6_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn6_complete:
  paco6 gf bot6 <6= cpn6 bot6.
Proof.
  intros. apply cpn6_from_paco.
  eapply paco6_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn6_base].
  - intros. apply PR0.
Qed.

Lemma cpn6_init:
  cpn6 bot6 <6= paco6 gf bot6.
Proof.
  intros. apply fcpn6_sound, fcpn6_to_paco, (compat6_compat cpn6_compat).
  eapply cpn6_mon; [apply PR|contradiction].
Qed.

Lemma cpn6_clo
      r clo (LE: clo <7= cpn6):
  clo (cpn6 r) <6= cpn6 r.
Proof.
  intros. apply cpn6_cpn, LE, PR.
Qed.

Lemma cpn6_unfold:
  cpn6 bot6 <6= fcpn6 bot6.
Proof.
  intros. apply cpn6_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn6_complete, PR0.
Qed.

Lemma fcpn6_clo
      r clo (LE: clo <7= cpn6):
  clo (fcpn6 r) <6= fcpn6 r.
Proof.
  intros. apply LE, (compat6_compat cpn6_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn6_cpn, PR0.
Qed.

Lemma cpn6_final: forall r, upaco6 gf r <6= cpn6 r.
Proof.
  intros. eapply cpn6_from_upaco.
  intros. eapply upaco6_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn6_base, PR1.
Qed.

Lemma fcpn6_final: forall r, paco6 gf r <6= fcpn6 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn6_final].
Qed.

Lemma cpn6_algebra r :
  r <6= gf r -> r <6= cpn6 bot6.
Proof.
  intros. apply cpn6_final. left.
  revert x0 x1 x2 x3 x4 x5 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion6_main.

Lemma cpn6_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 r
      (IN: @cpn6 gf bot6 x0 x1 x2 x3 x4 x5)
      (MONgf: monotone6 gf)
      (MONgf': monotone6 gf')
      (LE: gf <7= gf'):
  @cpn6 gf' r x0 x1 x2 x3 x4 x5.
Proof.
  apply cpn6_init in IN; [|apply MONgf].
  apply cpn6_final; [apply MONgf'|].
  left. eapply paco6_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn6_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 r
      (IN: @fcpn6 gf bot6 x0 x1 x2 x3 x4 x5)
      (MONgf: monotone6 gf)
      (MONgf': monotone6 gf')
      (LE: gf <7= gf'):
  @fcpn6 gf' r x0 x1 x2 x3 x4 x5.
Proof.
  apply LE. eapply MONgf. apply IN.
  intros. eapply cpn6_mon_bot; eassumption.
Qed.

End Companion6.

Hint Unfold fcpn6 : paco.

Hint Resolve cpn6_base : paco.
Hint Resolve cpn6_step : paco.
Hint Constructors rclo6 : paco.
Hint Resolve rclo6_clo : paco.
