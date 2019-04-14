Require Export Program.Basics. Open Scope program_scope.
Require Import paco2 pacotac.
Set Implicit Arguments.

Section Companion2.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.

Local Notation rel := (rel2 T0 T1).

Section Companion2_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone2 gf.

(** 
  Compatibility, Companion & Guarded Companion
*)

Structure compatible2 (clo: rel -> rel) : Prop :=
  compat2_intro {
      compat2_mon: monotone2 clo;
      compat2_compat : forall r,
          clo (gf r) <2= gf (clo r);
    }.

Inductive cpn2 (r: rel) x0 x1 : Prop :=
| cpn2_intro
    clo
    (COM: compatible2 clo)
    (CLO: clo r x0 x1)
.

Definition fcpn2 := compose gf cpn2.

Lemma cpn2_mon: monotone2 cpn2.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat2_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn2_compat: compatible2 cpn2.
Proof.
  econstructor; [apply cpn2_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat2_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn2_greatest: forall clo (COM: compatible2 clo), clo <3= cpn2.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn2_cpn: forall r,
    cpn2 (cpn2 r) <2= cpn2 r.
Proof.
  intros. exists (compose cpn2 cpn2); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn2_mon; [apply IN|].
    intros. eapply cpn2_mon; [apply PR0|apply LE].
  - intros. eapply (compat2_compat cpn2_compat).
    eapply cpn2_mon; [apply PR0|].
    intros. eapply (compat2_compat cpn2_compat), PR1. 
Qed.

Lemma monotone2_compose (clo1 clo2: rel -> rel)
      (MON1: monotone2 clo1)
      (MON2: monotone2 clo2):
  monotone2 (compose clo1 clo2).
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma fcpn2_mon: monotone2 fcpn2.
Proof.
  apply monotone2_compose. apply gf_mon. apply cpn2_mon.
Qed.

Lemma fcpn2_sound:
  paco2 fcpn2 bot2 <2= paco2 gf bot2.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \2/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn2 n (paco2 fcpn2 bot2) x0 x1) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn2 n (paco2 fcpn2 bot2) <2= gf (rclo cpn2 (S n) (paco2 fcpn2 bot2))).
  { intro X. revert x0 x1 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply fcpn2_mon].
    + intros. right. eapply cpn2_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat2_compat cpn2_compat).
        eapply (compat2_mon cpn2_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo2 (clo: rel->rel) (r: rel): rel :=
| rclo2_base
    x0 x1
    (IN: r x0 x1):
    @rclo2 clo r x0 x1
| rclo2_clo'
    r' x0 x1
    (LE: r' <2= rclo2 clo r)
    (IN: clo r' x0 x1):
    @rclo2 clo r x0 x1
.           

Structure wcompatible2 (clo: rel -> rel) : Prop :=
  wcompat2_intro {
      wcompat2_mon: monotone2 clo;
      wcompat2_wcompat : forall r,
          clo (gf r) <2= gf (rclo2 (clo \3/ cpn2) r);
    }.

Lemma rclo2_mon_gen clo clo' r r' x0 x1
      (IN: @rclo2 clo r x0 x1)
      (LEclo: clo <3= clo')
      (LEr: r <2= r') :
  @rclo2 clo' r' x0 x1.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo2_mon clo:
  monotone2 (rclo2 clo).
Proof.
  repeat intro. eapply rclo2_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo2_clo clo r:
  clo (rclo2 clo r) <2= rclo2 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo2_rclo clo r:
  rclo2 clo (rclo2 clo r) <2= rclo2 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo2_compose clo r:
  rclo2 (rclo2 clo) r <2= rclo2 clo r.
Proof.
  intros. induction PR.
  - apply rclo2_base, IN.
  - apply rclo2_rclo.
    eapply rclo2_mon; [apply IN|apply H].
Qed.

Lemma rclo2_compat clo
      (COM: compatible2 clo):
  compatible2 (rclo2 clo).
Proof.
  econstructor.
  - apply rclo2_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo2_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo2_clo. apply PR.
Qed.

Lemma wcompat2_compat  clo
      (WCOM: wcompatible2 clo):
  compatible2 (rclo2 (clo \3/ cpn2)).
Proof.
  econstructor; [eapply rclo2_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply IN|]. intros.
    apply rclo2_base. apply PR.
  - destruct IN as [IN|IN].
    + eapply gf_mon.
      * eapply WCOM. eapply WCOM; [apply IN|apply H].
      * intros. apply rclo2_rclo, PR.
    + eapply gf_mon; [|intros; apply rclo2_clo; right; apply PR].
      apply (compat2_compat cpn2_compat).
      eapply cpn2_mon; [apply IN|apply H].
Qed.

Lemma wcompat2_sound clo
      (WCOM: wcompatible2 clo):
  clo <3= cpn2.
Proof.
  intros. exists (rclo2 (clo \3/ cpn2)).
  - apply wcompat2_compat, WCOM.
  - apply rclo2_clo.
    left. eapply WCOM. apply PR.
    intros. apply rclo2_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn2_base: forall r, r <2= cpn2 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
  - apply PR.
Qed.

Lemma cpn2_step r:
  fcpn2 r <2= cpn2 r.
Proof.
  intros. eapply cpn2_cpn. exists gf.
  - econstructor. apply gf_mon. intros; apply PR0.
  - apply PR.
Qed.

Lemma cpn2_from_upaco r:
  upaco2 fcpn2 r <2= cpn2 r.
Proof.
  eapply wcompat2_sound.
  econstructor; [apply upaco2_mon|].
  intros. destruct PR as [PR|PR].
  - _punfold PR; [|apply fcpn2_mon]. 
    eapply gf_mon; [apply PR|].
    intros. apply rclo2_clo; right.
    eapply cpn2_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo2_clo; left.
      left. eapply paco2_mon; [apply H|].
      intros. apply rclo2_clo; right. apply cpn2_step.
      eapply gf_mon; [apply PR1|].
      intros. apply cpn2_base, rclo2_base, PR2.
    + apply rclo2_clo; right. apply cpn2_step.
      eapply gf_mon; [apply H|].
      intros. apply cpn2_base, rclo2_base, PR1.
  - eapply gf_mon. apply PR.
    intros. apply rclo2_base, PR0. 
Qed.

Lemma cpn2_from_paco r:
  paco2 fcpn2 r <2= cpn2 r.
Proof. intros. apply cpn2_from_upaco. left. apply PR. Qed.

Lemma fcpn2_from_paco r:
  paco2 fcpn2 r <2= fcpn2 r.
Proof.
  intros. _punfold PR; [|apply fcpn2_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn2_cpn.
  eapply cpn2_mon; [apply PR0|].
  apply cpn2_from_upaco.
Qed.

Lemma fcpn2_to_paco r:
  fcpn2 r <2= paco2 fcpn2 r.
Proof.
  intros. pfold. eapply fcpn2_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn2_complete:
  paco2 gf bot2 <2= cpn2 bot2.
Proof.
  intros. apply cpn2_from_paco.
  eapply paco2_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn2_base].
  - intros. apply PR0.
Qed.

Lemma cpn2_init:
  cpn2 bot2 <2= paco2 gf bot2.
Proof.
  intros. apply fcpn2_sound, fcpn2_to_paco, (compat2_compat cpn2_compat).
  eapply cpn2_mon; [apply PR|contradiction].
Qed.

Lemma cpn2_clo
      r clo (LE: clo <3= cpn2):
  clo (cpn2 r) <2= cpn2 r.
Proof.
  intros. apply cpn2_cpn, LE, PR.
Qed.

Lemma cpn2_unfold:
  cpn2 bot2 <2= fcpn2 bot2.
Proof.
  intros. apply cpn2_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn2_complete, PR0.
Qed.

Lemma fcpn2_clo
      r clo (LE: clo <3= cpn2):
  clo (fcpn2 r) <2= fcpn2 r.
Proof.
  intros. apply LE, (compat2_compat cpn2_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn2_cpn, PR0.
Qed.

Lemma cpn2_final: forall r, upaco2 gf r <2= cpn2 r.
Proof.
  intros. eapply cpn2_from_upaco.
  intros. eapply upaco2_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn2_base, PR1.
Qed.

Lemma fcpn2_final: forall r, paco2 gf r <2= fcpn2 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn2_final].
Qed.

Lemma cpn2_algebra r :
  r <2= gf r -> r <2= cpn2 bot2.
Proof.
  intros. apply cpn2_final. left.
  revert x0 x1 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion2_main.

Lemma cpn2_mon_bot (gf gf': rel -> rel) x0 x1 r
      (IN: @cpn2 gf bot2 x0 x1)
      (MONgf: monotone2 gf)
      (MONgf': monotone2 gf')
      (LE: gf <3= gf'):
  @cpn2 gf' r x0 x1.
Proof.
  apply cpn2_init in IN; [|apply MONgf].
  apply cpn2_final; [apply MONgf'|].
  left. eapply paco2_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn2_mon_bot (gf gf': rel -> rel) x0 x1 r
      (IN: @fcpn2 gf bot2 x0 x1)
      (MONgf: monotone2 gf)
      (MONgf': monotone2 gf')
      (LE: gf <3= gf'):
  @fcpn2 gf' r x0 x1.
Proof.
  apply LE. eapply MONgf. apply IN.
  intros. eapply cpn2_mon_bot; eassumption.
Qed.

End Companion2.

Hint Unfold fcpn2 : paco.

Hint Resolve cpn2_base : paco.
Hint Resolve cpn2_step : paco.
Hint Constructors rclo2 : paco.
Hint Resolve rclo2_clo : paco.
