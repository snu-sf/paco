Require Export Program.Basics. Open Scope program_scope.
Require Import paco0 pacotac.
Set Implicit Arguments.

Section Companion0.


Local Notation rel := (rel0).

Section Companion0_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone0 gf.

(** 
  Bounded Compatibility, Companion & Guarded Companion
*)

Inductive pointwise_union (bnd: rel -> rel) (r: rel) : Prop :=
| pw_union_
            (IN: r)
            (PTW: forall (s: rel), s -> bnd s)
.

Structure compatible_bound0 (bnd: rel -> rel) : Prop :=
  cbound0_intro {
      cbound0_distr : forall r,
          bnd r <0= pointwise_union bnd r;
      cbound0_compat: forall r,
          bnd (gf r) <0= gf (bnd r);
      cbound0_bound: forall r,
          bnd (bnd r) <0= (bnd r \0/ gf (bnd r));
    }.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound0 bnd.

Structure compatible0 (clo: rel -> rel) : Prop :=
  compat0_intro {
      compat0_mon: monotone0 clo;
      compat0_compat : forall r,
          clo (gf r) <0= gf (clo r);
      compat0_bound : forall r,
          bnd (clo r) <0= (bnd r \0/ gf (clo r))
    }.

Inductive cpn0 (r: rel) : Prop :=
| cpn0_intro
    clo
    (COM: compatible0 clo)
    (CLO: clo r)
.

Definition fcpn0 := compose gf cpn0.

Lemma cbound0_union r1 r2 : bnd (r1 \0/ r2) <0= (bnd r1 \0/ bnd r2).
Proof.
  intros. eapply cbound0_distr in PR; [|apply bnd_compat].
  destruct PR. destruct IN.
  - left. apply PTW, H.
  - right. apply PTW, H.
Qed.

Lemma cbound0_mon: monotone0 bnd.
Proof.
  repeat intro.
  apply (cbound0_distr bnd_compat) in IN.
  destruct IN.
  apply PTW, LE, IN.
Qed.

Lemma cpn0_mon: monotone0 cpn0.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat0_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn0_compat: compatible0 cpn0.
Proof.
  econstructor; [apply cpn0_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (compat0_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - eapply (cbound0_distr bnd_compat) in PR.
    destruct PR. destruct IN.
    specialize (PTW (clo r) CLO).
    apply (compat0_bound COM) in PTW.
    destruct PTW.
    + left. apply H.
    + right. eapply gf_mon; [apply H|].
      intros. econstructor;[apply COM|apply PR].
Qed.

Lemma cpn0_greatest: forall clo (COM: compatible0 clo), clo <1= cpn0.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn0_base: forall r, r <0= cpn0 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
    + left. apply PR0.
  - apply PR.
Qed.

Lemma cpn0_bound : forall r, bnd r <0= cpn0 r.
Proof.
  intros. exists bnd.
  - econstructor; repeat intro.
    + eapply cbound0_mon. apply IN. apply LE.
    + apply (cbound0_compat bnd_compat), PR0.
    + apply (cbound0_bound bnd_compat), PR0.
  - apply PR.
Qed.

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
  - intros. eapply (compat0_bound cpn0_compat) in PR0.
    destruct PR0; [|right; apply H].
    eapply (compat0_bound cpn0_compat) in H.
    destruct H; [left; apply H|].
    right. eapply gf_mon; [apply H|].
    intros. apply cpn0_base. apply PR0.
Qed.

Lemma fcpn0_mon: monotone0 fcpn0.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn0_mon; [apply PR|apply LE].
Qed.

Lemma fcpn0_sound:
  paco0 fcpn0 bot0 <0= paco0 gf bot0.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \0/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn0 n (paco0 fcpn0 bot0)) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn0 n (paco0 fcpn0 bot0) <0= gf (rclo cpn0 (S n) (paco0 fcpn0 bot0))).
  { intro X. revert RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply fcpn0_mon].
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
      wcompat0_bound : forall r,
          bnd (clo r) <0= (bnd r \0/ gf (rclo0 clo r))
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
  - apply R.
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
  econstructor; [eapply rclo0_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo0_base. apply PR.
    + eapply gf_mon.
      * eapply (wcompat0_wcompat WCOM).
        eapply (wcompat0_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo0_mult, PR.
    + eapply gf_mon; [apply CLOR'|].
      intros. apply H in PR. apply rclo0_step, PR.
    + eapply gf_mon; [|intros; apply rclo0_cpn, PR].
      apply (compat0_compat cpn0_compat).
      eapply cpn0_mon; [apply CLOR'|apply H].
  - eapply (cbound0_distr bnd_compat) in PR.
    destruct PR. revert PTW.
    induction IN; intros.
    + left. apply PTW, R.
    + specialize (PTW _ CLOR').
      eapply (wcompat0_bound WCOM) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound0_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo0_mult.
        eapply rclo0_mon, R'. apply PR.
    + specialize (PTW _ CLOR').
      eapply (cbound0_compat bnd_compat) in PTW.
      right. eapply gf_mon. apply PTW. intros.
      eapply (cbound0_distr bnd_compat) in PR.
      destruct PR.
      eapply H in IN; [|apply PTW0].
      destruct IN.
      * apply rclo0_cpn, cpn0_bound.
        eapply cbound0_mon. apply H0. apply rclo0_base.
      * apply rclo0_step. apply H0.
    + specialize (PTW _ CLOR').
      apply (compat0_bound cpn0_compat) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound0_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo0_cpn.
        eapply cpn0_mon; [apply PR|].
        intros. apply R', PR0.
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

Lemma cpn0_from_upaco r:
  upaco0 fcpn0 r <0= cpn0 r.
Proof.
  intros. destruct PR; [| apply cpn0_base, H].
  exists (rclo0 (paco0 fcpn0)).
  - apply wcompat0_compat.
    econstructor; [apply paco0_mon| |].
    + intros. _punfold PR; [|apply fcpn0_mon].
      eapply gf_mon; [apply PR|].
      intros. apply rclo0_cpn.
      eapply cpn0_mon; [apply PR0|].
      intros. destruct PR1.
      * apply rclo0_clo.
        eapply paco0_mon; [apply H0|].
        intros. apply rclo0_step.
        eapply gf_mon; [apply PR1|].
        intros. apply rclo0_base, PR2.
      * apply rclo0_step.
        eapply gf_mon; [apply H0|].
        intros. apply rclo0_base, PR1.
    + intros. right.
      eapply gf_mon, rclo0_cpn.
      eapply gf_mon, cpn0_bound.
      apply (cbound0_compat bnd_compat).
      eapply cbound0_mon. apply PR.
      intros. _punfold PR0; [|apply fcpn0_mon].
      eapply gf_mon. apply PR0.
      intros. apply rclo0_cpn.
      eapply cpn0_mon. apply PR1.
      intros. destruct PR2.
      * apply rclo0_clo.
        eapply paco0_mon. apply H0.
        intros. apply rclo0_base. apply PR2.
      * apply rclo0_base. apply H0.
  - apply rclo0_clo.
    eapply paco0_mon; [apply H|].
    intros. apply rclo0_base, PR.
Qed.

Lemma cpn0_from_paco r:
  paco0 fcpn0 r <0= cpn0 r.
Proof. intros. apply cpn0_from_upaco. left. apply PR. Qed.

Lemma fcpn0_from_paco r:
  paco0 fcpn0 r <0= fcpn0 r.
Proof.
  intros. _punfold PR; [|apply fcpn0_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn0_cpn.
  eapply cpn0_mon; [apply PR0|].
  apply cpn0_from_upaco.
Qed.

Lemma fcpn0_to_paco r:
  fcpn0 r <0= paco0 fcpn0 r.
Proof.
  intros. pfold. eapply fcpn0_mon; [apply PR|].
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
  intros. apply fcpn0_sound, fcpn0_to_paco, (compat0_compat cpn0_compat).
  eapply cpn0_mon; [apply PR|contradiction].
Qed.

Lemma cpn0_clo
      r clo (LE: clo <1= cpn0):
  clo (cpn0 r) <0= cpn0 r.
Proof.
  intros. apply cpn0_cpn, LE, PR.
Qed.

Lemma cpn0_unfold:
  cpn0 bot0 <0= fcpn0 bot0.
Proof.
  intros. apply cpn0_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn0_complete, PR0.
Qed.

Lemma cpn0_unfold_bound r
      (BASE: forall r, r <0= bnd r):
  cpn0 r <0= (bnd r \0/ fcpn0 r).
Proof.
  intros. apply BASE in PR.
  eapply compat0_bound in PR.
  - apply PR.
  - apply cpn0_compat.
Qed.

Lemma cpn0_step r:
  fcpn0 r <0= cpn0 r.
Proof.
  intros. eapply cpn0_clo, PR.
  intros. eapply wcompat0_sound, PR0.
  econstructor; [apply gf_mon| |].
  - intros. eapply gf_mon; [apply PR1|].
    intros. apply rclo0_step.
    eapply gf_mon; [apply PR2|].
    intros. apply rclo0_base, PR3.
  - intros. apply (cbound0_compat bnd_compat) in PR1.
    right. eapply gf_mon. apply PR1.
    intros. apply rclo0_cpn, cpn0_bound.
    eapply cbound0_mon. apply PR2.
    intros. apply rclo0_base, PR3.
Qed.

Lemma fcpn0_clo
      r clo (LE: clo <1= cpn0):
  clo (fcpn0 r) <0= fcpn0 r.
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

Lemma fcpn0_final: forall r, paco0 gf r <0= fcpn0 r.
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

Lemma cbound0_bot gf:
  compatible_bound0 gf bot1.
Proof.
  econstructor; intros; contradiction.
Qed.

Lemma cpn0_mon_bot (gf gf': rel -> rel) bnd bnd' r
      (IN: @cpn0 gf bnd bot0)
      (MON: monotone0 gf)
      (MON': monotone0 gf')
      (BASE: compatible_bound0 gf bnd)
      (BASE': compatible_bound0 gf' bnd')
      (LE: gf <1= gf'):
  @cpn0 gf' bnd' r.
Proof.
  apply cpn0_init in IN; [|apply MON|apply BASE].
  apply cpn0_final; [apply MON'|apply BASE'|].
  left. eapply paco0_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn0_mon_bot (gf gf': rel -> rel) bnd bnd' r
      (IN: @fcpn0 gf bnd bot0)
      (MON: monotone0 gf)
      (MON': monotone0 gf')
      (BASE: compatible_bound0 gf bnd)
      (BASE': compatible_bound0 gf' bnd')
      (LE: gf <1= gf'):
  @fcpn0 gf' bnd' r.
Proof.
  apply LE. eapply MON. apply IN.
  intros. eapply cpn0_mon_bot; eassumption.
Qed.

End Companion0.

Hint Unfold fcpn0 : paco.
Hint Resolve cpn0_base : paco.
Hint Resolve cpn0_step : paco.
Hint Resolve cbound0_bot : paco.

Hint Constructors rclo0 : rclo.
Hint Resolve rclo0_clo rclo0_step rclo0_cpn : rclo.

