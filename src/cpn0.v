Require Export Program.Basics. Open Scope program_scope.
Require Import paco0 pacotac.
Set Implicit Arguments.

Section Companion0.


Local Notation rel := (rel0).

Section Companion0_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone0 gf.

(** 
  Compatibility, Companion & Guarded Companion
*)

Structure compatible0 (clo: rel -> rel) : Prop :=
  compat0_intro {
      compat0_mon: monotone0 clo;
      compat0_compat : forall r,
          clo (gf r) <0= gf (clo r);
    }.

Inductive cpn0 (r: rel) : Prop :=
| cpn0_intro
    clo
    (COM: compatible0 clo)
    (CLO: clo r)
.

Definition gcpn0 := compose gf cpn0.

Lemma cpn0_mon: monotone0 cpn0.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat0_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn0_compat: compatible0 cpn0.
Proof.
  econstructor; [apply cpn0_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - eapply (compat0_compat COM); apply CLO.
  - intros. econstructor; [apply COM|apply PR].
Qed.

Lemma cpn0_greatest: forall clo (COM: compatible0 clo), clo <1= cpn0.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn0_cpn: forall r,
    cpn0 (cpn0 r) <0= cpn0 r.
Proof.
  intros. exists (compose cpn0 cpn0); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn0_mon; [apply IN|].
    intros. eapply cpn0_mon; [apply PR0|apply LE].
  - intros. eapply (compat0_compat cpn0_compat).
    eapply cpn0_mon; [apply PR0|].
    intros. eapply (compat0_compat cpn0_compat), PR1. 
Qed.

Lemma gcpn0_mon: monotone0 gcpn0.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn0_mon; [apply PR|apply LE].
Qed.

Lemma gcpn0_sound:
  paco0 gcpn0 bot0 <0= paco0 gf bot0.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \0/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn0 n (paco0 gcpn0 bot0)) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn0 n (paco0 gcpn0 bot0) <0= gf (rclo cpn0 (S n) (paco0 gcpn0 bot0))).
  { intro X. revert RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply gcpn0_mon].
    + intros. right. eapply cpn0_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat0_compat cpn0_compat).
        eapply (compat0_mon cpn0_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo0 (clo: rel->rel) (r: rel): rel :=
| rclo0_base
   
    (R: r):
    @rclo0 clo r
| rclo0_clo'
    r'
    (R': r' <0= rclo0 clo r)
    (CLOR': clo r'):
    @rclo0 clo r
| rclo0_step'
    r'
    (R': r' <0= rclo0 clo r)
    (CLOR': @gf r'):
    @rclo0 clo r
| rclo0_cpn'
    r'
    (R': r' <0= rclo0 clo r)
    (CLOR': @cpn0 r'):
    @rclo0 clo r
.

Structure wcompatible0 (clo: rel -> rel) : Prop :=
  wcompat0_intro {
      wcompat0_mon: monotone0 clo;
      wcompat0_wcompat: forall r,
          clo (gf r) <0= gf (rclo0 clo r);
    }.

Lemma rclo0_mon_gen clo clo' r r'
      (IN: @rclo0 clo r)
      (LEclo: clo <1= clo')
      (LEr: r <0= r') :
  @rclo0 clo' r'.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn0_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo0_mon clo:
  monotone0 (rclo0 clo).
Proof.
  repeat intro. eapply rclo0_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo0_clo clo r:
  clo (rclo0 clo r) <0= rclo0 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo0_step clo r:
  gf (rclo0 clo r) <0= rclo0 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo0_cpn clo r:
  cpn0 (rclo0 clo r) <0= rclo0 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo0_mult clo r:
  rclo0 clo (rclo0 clo r) <0= rclo0 clo r.
Proof.
  intros. induction PR.
  - eapply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo0_compose clo r:
  rclo0 (rclo0 clo) r <0= rclo0 clo r.
Proof.
  intros. induction PR.
  - apply rclo0_base, R.
  - apply rclo0_mult.
    eapply rclo0_mon; [apply CLOR'|apply H].
  - apply rclo0_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo0_cpn.
    eapply cpn0_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat0_compat
      clo (WCOM: wcompatible0 clo):
  compatible0 (rclo0 clo).
Proof.
  econstructor; [eapply rclo0_mon|]. intros.
  induction PR; intros.
  - eapply gf_mon; [apply R|]. intros.
    apply rclo0_base. apply PR.
  - eapply gf_mon.
    + eapply (wcompat0_wcompat WCOM).
      eapply (wcompat0_mon WCOM); [apply CLOR'|apply H].
    + intros. apply rclo0_mult, PR.
  - eapply gf_mon; [apply CLOR'|].
    intros. apply H in PR. apply rclo0_step, PR.
  - eapply gf_mon; [|intros; apply rclo0_cpn, PR].
    apply (compat0_compat cpn0_compat).
    eapply cpn0_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat0_sound clo (WCOM: wcompatible0 clo):
  clo <1= cpn0.
Proof.
  intros. exists (rclo0 clo).
  - apply wcompat0_compat, WCOM.
  - apply rclo0_clo.
    eapply (wcompat0_mon WCOM); [apply PR|].
    intros. apply rclo0_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn0_base: forall r, r <0= cpn0 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
  - apply PR.
Qed.

Lemma cpn0_from_upaco r:
  upaco0 gcpn0 r <0= cpn0 r.
Proof.
  intros. destruct PR; [| apply cpn0_base, H].
  exists (rclo0 (paco0 gcpn0)).
  - apply wcompat0_compat.
    econstructor; [apply paco0_mon|].
    intros. _punfold PR; [|apply gcpn0_mon].
    eapply gf_mon; [apply PR|].
    intros. apply rclo0_cpn.
    eapply cpn0_mon; [apply PR0|].
    intros. destruct PR1.
    + apply rclo0_clo.
      eapply paco0_mon; [apply H0|].
      intros. apply rclo0_step.
      eapply gf_mon; [apply PR1|].
      intros. apply rclo0_base, PR2.
    + apply rclo0_step.
      eapply gf_mon; [apply H0|].
      intros. apply rclo0_base, PR1.
  - apply rclo0_clo.
    eapply paco0_mon; [apply H|].
    intros. apply rclo0_base, PR.
Qed.

Lemma cpn0_from_paco r:
  paco0 gcpn0 r <0= cpn0 r.
Proof. intros. apply cpn0_from_upaco. left. apply PR. Qed.

Lemma gcpn0_from_paco r:
  paco0 gcpn0 r <0= gcpn0 r.
Proof.
  intros. _punfold PR; [|apply gcpn0_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn0_cpn.
  eapply cpn0_mon; [apply PR0|].
  apply cpn0_from_upaco.
Qed.

Lemma gcpn0_to_paco r:
  gcpn0 r <0= paco0 gcpn0 r.
Proof.
  intros. pfold. eapply gcpn0_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn0_complete:
  paco0 gf bot0 <0= cpn0 bot0.
Proof.
  intros. apply cpn0_from_paco.
  eapply paco0_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn0_base].
  - intros. apply PR0.
Qed.

Lemma cpn0_init:
  cpn0 bot0 <0= paco0 gf bot0.
Proof.
  intros. apply gcpn0_sound, gcpn0_to_paco, (compat0_compat cpn0_compat).
  eapply cpn0_mon; [apply PR|contradiction].
Qed.

Lemma cpn0_clo
      r clo (LE: clo <1= cpn0):
  clo (cpn0 r) <0= cpn0 r.
Proof.
  intros. apply cpn0_cpn, LE, PR.
Qed.

Lemma cpn0_unfold:
  cpn0 bot0 <0= gcpn0 bot0.
Proof.
  intros. apply cpn0_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn0_complete, PR0.
Qed.

Lemma cpn0_step r:
  gcpn0 r <0= cpn0 r.
Proof.
  intros. eapply cpn0_clo, PR.
  intros. eapply wcompat0_sound, PR0.
  econstructor; [apply gf_mon|].
  intros. eapply gf_mon; [apply PR1|].
  intros. apply rclo0_step.
  eapply gf_mon; [apply PR2|].
  intros. apply rclo0_base, PR3.
Qed.

Lemma gcpn0_clo
      r clo (LE: clo <1= cpn0):
  clo (gcpn0 r) <0= gcpn0 r.
Proof.
  intros. apply LE, (compat0_compat cpn0_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn0_cpn, PR0.
Qed.

Lemma cpn0_final: forall r, upaco0 gf r <0= cpn0 r.
Proof.
  intros. eapply cpn0_from_upaco.
  intros. eapply upaco0_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn0_base, PR1.
Qed.

Lemma gcpn0_final: forall r, paco0 gf r <0= gcpn0 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn0_final].
Qed.

Lemma cpn0_algebra r :
  r <0= gf r -> r <0= cpn0 bot0.
Proof.
  intros. apply cpn0_final. left.
  revert PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion0_main.

Lemma cpn0_mon_bot (gf gf': rel -> rel) r
      (IN: @cpn0 gf bot0)
      (MONgf: monotone0 gf)
      (MONgf': monotone0 gf')
      (LE: gf <1= gf'):
  @cpn0 gf' r.
Proof.
  apply cpn0_init in IN; [|apply MONgf].
  apply cpn0_final; [apply MONgf'|].
  left. eapply paco0_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma gcpn0_mon_bot (gf gf': rel -> rel) r
      (IN: @gcpn0 gf bot0)
      (MONgf: monotone0 gf)
      (MONgf': monotone0 gf')
      (LE: gf <1= gf'):
  @gcpn0 gf' r.
Proof.
  apply LE. eapply MONgf. apply IN.
  intros. eapply cpn0_mon_bot; eassumption.
Qed.

End Companion0.

Hint Unfold gcpn0 : paco.

Hint Resolve cpn0_base : paco.
Hint Resolve cpn0_step : paco.

Hint Constructors rclo0 : rclo.
Hint Resolve rclo0_clo rclo0_step rclo0_cpn : rclo.

