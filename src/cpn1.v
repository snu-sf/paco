Require Export Program.Basics. Open Scope program_scope.
Require Import paco1 pacotac.
Set Implicit Arguments.

Section Companion1.

Variable T0 : Type.

Local Notation rel := (rel1 T0).

Section Companion1_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone1 gf.

(** 
  Compatibility, Companion & Guarded Companion
*)

Structure compatible1 (clo: rel -> rel) : Prop :=
  compat1_intro {
      compat1_mon: monotone1 clo;
      compat1_compat : forall r,
          clo (gf r) <1= gf (clo r);
    }.

Inductive cpn1 (r: rel) x0 : Prop :=
| cpn1_intro
    clo
    (COM: compatible1 clo)
    (CLO: clo r x0)
.

Definition fcpn1 := compose gf cpn1.

Lemma cpn1_mon: monotone1 cpn1.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat1_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn1_compat: compatible1 cpn1.
Proof.
  econstructor; [apply cpn1_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat1_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn1_greatest: forall clo (COM: compatible1 clo), clo <2= cpn1.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn1_cpn: forall r,
    cpn1 (cpn1 r) <1= cpn1 r.
Proof.
  intros. exists (compose cpn1 cpn1); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn1_mon; [apply IN|].
    intros. eapply cpn1_mon; [apply PR0|apply LE].
  - intros. eapply (compat1_compat cpn1_compat).
    eapply cpn1_mon; [apply PR0|].
    intros. eapply (compat1_compat cpn1_compat), PR1. 
Qed.

Lemma fcpn1_mon: monotone1 fcpn1.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn1_mon; [apply PR|apply LE].
Qed.

Lemma fcpn1_sound:
  paco1 fcpn1 bot1 <1= paco1 gf bot1.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \1/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn1 n (paco1 fcpn1 bot1) x0) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn1 n (paco1 fcpn1 bot1) <1= gf (rclo cpn1 (S n) (paco1 fcpn1 bot1))).
  { intro X. revert x0 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply fcpn1_mon].
    + intros. right. eapply cpn1_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat1_compat cpn1_compat).
        eapply (compat1_mon cpn1_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo1 (clo: rel->rel) (r: rel): rel :=
| rclo1_base
    x0
    (IN: r x0):
    @rclo1 clo r x0
| rclo1_clo'
    r' x0
    (LE: r' <1= rclo1 clo r)
    (IN: clo r' x0):
    @rclo1 clo r x0
.           

Structure wcompatible1 (clo: rel -> rel) : Prop :=
  wcompat1_intro {
      wcompat1_mon: monotone1 clo;
      wcompat1_wcompat : forall r,
          clo (gf r) <1= gf (rclo1 (clo \2/ cpn1) r);
    }.


Lemma rclo1_mon_gen clo clo' r r' x0
      (IN: @rclo1 clo r x0)
      (LEclo: clo <2= clo')
      (LEr: r <1= r') :
  @rclo1 clo' r' x0.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo1_mon clo:
  monotone1 (rclo1 clo).
Proof.
  repeat intro. eapply rclo1_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo1_clo clo r:
  clo (rclo1 clo r) <1= rclo1 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo1_rclo clo r:
  rclo1 clo (rclo1 clo r) <1= rclo1 clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo1_compose clo r:
  rclo1 (rclo1 clo) r <1= rclo1 clo r.
Proof.
  intros. induction PR.
  - apply rclo1_base, IN.
  - apply rclo1_rclo.
    eapply rclo1_mon; [apply IN|apply H].
Qed.

Lemma rclo1_compat clo
      (COM: compatible1 clo):
  compatible1 (rclo1 clo).
Proof.
  econstructor.
  - apply rclo1_mon.
  - intros. induction PR.
    + eapply gf_mon. apply IN.
      intros. eapply rclo1_base. apply PR.
    + eapply gf_mon.
      * eapply COM. eapply COM. apply IN. apply H.
      * intros. eapply rclo1_clo. apply PR.
Qed.

Lemma wcompat1_compat  clo
      (WCOM: wcompatible1 clo):
  compatible1 (rclo1 (clo \2/ cpn1)).
Proof.
  econstructor; [eapply rclo1_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply IN|]. intros.
    apply rclo1_base. apply PR.
  - destruct IN as [IN|IN].
    + eapply gf_mon.
      * eapply WCOM. eapply WCOM; [apply IN|apply H].
      * intros. apply rclo1_rclo, PR.
    + eapply gf_mon; [|intros; apply rclo1_clo; right; apply PR].
      apply (compat1_compat cpn1_compat).
      eapply cpn1_mon; [apply IN|apply H].
Qed.

Lemma wcompat1_sound clo
      (WCOM: wcompatible1 clo):
  clo <2= cpn1.
Proof.
  intros. exists (rclo1 (clo \2/ cpn1)).
  - apply wcompat1_compat, WCOM.
  - apply rclo1_clo.
    left. eapply WCOM. apply PR.
    intros. apply rclo1_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn1_base: forall r, r <1= cpn1 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
  - apply PR.
Qed.

Lemma cpn1_step r:
  fcpn1 r <1= cpn1 r.
Proof.
  intros. eapply cpn1_cpn. exists gf.
  - econstructor. apply gf_mon. intros; apply PR0.
  - apply PR.
Qed.

Lemma cpn1_from_upaco r:
  upaco1 fcpn1 r <1= cpn1 r.
Proof.
  eapply wcompat1_sound.
  econstructor; [apply upaco1_mon|].
  intros. destruct PR as [PR|PR].
  - _punfold PR; [|apply fcpn1_mon]. 
    eapply gf_mon; [apply PR|].
    intros. apply rclo1_clo; right.
    eapply cpn1_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo1_clo; left.
      left. eapply paco1_mon; [apply H|].
      intros. apply rclo1_clo; right. apply cpn1_step.
      eapply gf_mon; [apply PR1|].
      intros. apply cpn1_base, rclo1_base, PR2.
    + apply rclo1_clo; right. apply cpn1_step.
      eapply gf_mon; [apply H|].
      intros. apply cpn1_base, rclo1_base, PR1.
  - eapply gf_mon. apply PR.
    intros. apply rclo1_base, PR0. 
Qed.

Lemma cpn1_from_paco r:
  paco1 fcpn1 r <1= cpn1 r.
Proof. intros. apply cpn1_from_upaco. left. apply PR. Qed.

Lemma fcpn1_from_paco r:
  paco1 fcpn1 r <1= fcpn1 r.
Proof.
  intros. _punfold PR; [|apply fcpn1_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn1_cpn.
  eapply cpn1_mon; [apply PR0|].
  apply cpn1_from_upaco.
Qed.

Lemma fcpn1_to_paco r:
  fcpn1 r <1= paco1 fcpn1 r.
Proof.
  intros. pfold. eapply fcpn1_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn1_complete:
  paco1 gf bot1 <1= cpn1 bot1.
Proof.
  intros. apply cpn1_from_paco.
  eapply paco1_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn1_base].
  - intros. apply PR0.
Qed.

Lemma cpn1_init:
  cpn1 bot1 <1= paco1 gf bot1.
Proof.
  intros. apply fcpn1_sound, fcpn1_to_paco, (compat1_compat cpn1_compat).
  eapply cpn1_mon; [apply PR|contradiction].
Qed.

Lemma cpn1_clo
      r clo (LE: clo <2= cpn1):
  clo (cpn1 r) <1= cpn1 r.
Proof.
  intros. apply cpn1_cpn, LE, PR.
Qed.

Lemma cpn1_unfold:
  cpn1 bot1 <1= fcpn1 bot1.
Proof.
  intros. apply cpn1_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn1_complete, PR0.
Qed.

Lemma fcpn1_clo
      r clo (LE: clo <2= cpn1):
  clo (fcpn1 r) <1= fcpn1 r.
Proof.
  intros. apply LE, (compat1_compat cpn1_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn1_cpn, PR0.
Qed.

Lemma cpn1_final: forall r, upaco1 gf r <1= cpn1 r.
Proof.
  intros. eapply cpn1_from_upaco.
  intros. eapply upaco1_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn1_base, PR1.
Qed.

Lemma fcpn1_final: forall r, paco1 gf r <1= fcpn1 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn1_final].
Qed.

Lemma cpn1_algebra r :
  r <1= gf r -> r <1= cpn1 bot1.
Proof.
  intros. apply cpn1_final. left.
  revert x0 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion1_main.

Lemma cpn1_mon_bot (gf gf': rel -> rel) x0 r
      (IN: @cpn1 gf bot1 x0)
      (MONgf: monotone1 gf)
      (MONgf': monotone1 gf')
      (LE: gf <2= gf'):
  @cpn1 gf' r x0.
Proof.
  apply cpn1_init in IN; [|apply MONgf].
  apply cpn1_final; [apply MONgf'|].
  left. eapply paco1_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn1_mon_bot (gf gf': rel -> rel) x0 r
      (IN: @fcpn1 gf bot1 x0)
      (MONgf: monotone1 gf)
      (MONgf': monotone1 gf')
      (LE: gf <2= gf'):
  @fcpn1 gf' r x0.
Proof.
  apply LE. eapply MONgf. apply IN.
  intros. eapply cpn1_mon_bot; eassumption.
Qed.

End Companion1.

Hint Unfold fcpn1 : paco.

Hint Resolve cpn1_base : paco.
Hint Resolve cpn1_step : paco.
Hint Constructors rclo1 : paco.
Hint Resolve rclo1_clo : paco.
