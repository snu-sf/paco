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
  Bounded Compatibility, Companion & Guarded Companion
*)

Inductive pointwise_union (bnd: rel -> rel) (r: rel) e0 : Prop :=
| pw_union_ d0
            (IN: r d0)
            (PTW: forall (s: rel), s d0 -> bnd s e0)
.

Structure compatible_bound1 (bnd: rel -> rel) : Prop :=
  cbound1_intro {
      cbound1_distr : forall r,
          bnd r <1= pointwise_union bnd r;
      cbound1_compat: forall r,
          bnd (gf r) <1= gf (bnd r);
      cbound1_bound: forall r,
          bnd (bnd r) <1= (bnd r \1/ gf (bnd r));
    }.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound1 bnd.

Structure compatible1 (clo: rel -> rel) : Prop :=
  compat1_intro {
      compat1_mon: monotone1 clo;
      compat1_compat : forall r,
          clo (gf r) <1= gf (clo r);
      compat1_bound : forall r,
          bnd (clo r) <1= (bnd r \1/ gf (clo r))
    }.

Inductive cpn1 (r: rel) e0 : Prop :=
| cpn1_intro
    clo
    (COM: compatible1 clo)
    (CLO: clo r e0)
.

Definition fcpn1 := compose gf cpn1.

Lemma cbound1_union r1 r2 : bnd (r1 \1/ r2) <1= (bnd r1 \1/ bnd r2).
Proof.
  intros. eapply cbound1_distr in PR; [|apply bnd_compat].
  destruct PR. destruct IN.
  - left. apply PTW, H.
  - right. apply PTW, H.
Qed.

Lemma cbound1_mon: monotone1 bnd.
Proof.
  repeat intro.
  apply (cbound1_distr bnd_compat) in IN.
  destruct IN.
  apply PTW, LE, IN.
Qed.

Lemma cpn1_mon: monotone1 cpn1.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat1_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn1_compat: compatible1 cpn1.
Proof.
  econstructor; [apply cpn1_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (compat1_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - eapply (cbound1_distr bnd_compat) in PR.
    destruct PR. destruct IN.
    specialize (PTW (clo r) CLO).
    apply (compat1_bound COM) in PTW.
    destruct PTW.
    + left. apply H.
    + right. eapply gf_mon; [apply H|].
      intros. econstructor;[apply COM|apply PR].
Qed.

Lemma cpn1_greatest: forall clo (COM: compatible1 clo), clo <2= cpn1.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn1_base: forall r, r <1= cpn1 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
    + left. apply PR0.
  - apply PR.
Qed.

Lemma cpn1_bound : forall r, bnd r <1= cpn1 r.
Proof.
  intros. exists bnd.
  - econstructor; repeat intro.
    + eapply cbound1_mon. apply IN. apply LE.
    + apply (cbound1_compat bnd_compat), PR0.
    + apply (cbound1_bound bnd_compat), PR0.
  - apply PR.
Qed.

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
  - intros. eapply (compat1_bound cpn1_compat) in PR0.
    destruct PR0; [|right; apply H].
    eapply (compat1_bound cpn1_compat) in H.
    destruct H; [left; apply H|].
    right. eapply gf_mon; [apply H|].
    intros. apply cpn1_base. apply PR0.
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
    e0
    (R: r e0):
    @rclo1 clo r e0
| rclo1_clo'
    r' e0
    (R': r' <1= rclo1 clo r)
    (CLOR': clo r' e0):
    @rclo1 clo r e0
| rclo1_step'
    r' e0
    (R': r' <1= rclo1 clo r)
    (CLOR': @gf r' e0):
    @rclo1 clo r e0
| rclo1_cpn'
    r' e0
    (R': r' <1= rclo1 clo r)
    (CLOR': @cpn1 r' e0):
    @rclo1 clo r e0
.

Structure wcompatible1 (clo: rel -> rel) : Prop :=
  wcompat1_intro {
      wcompat1_mon: monotone1 clo;
      wcompat1_wcompat: forall r,
          clo (gf r) <1= gf (rclo1 clo r);
      wcompat1_bound : forall r,
          bnd (clo r) <1= (bnd r \1/ gf (rclo1 clo r))
    }.

Lemma rclo1_mon_gen clo clo' r r' e0
      (IN: @rclo1 clo r e0)
      (LEclo: clo <2= clo')
      (LEr: r <1= r') :
  @rclo1 clo' r' e0.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn1_mon; [apply CLOR'|].
    intros. apply PR.
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

Lemma rclo1_step clo r:
  gf (rclo1 clo r) <1= rclo1 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo1_cpn clo r:
  cpn1 (rclo1 clo r) <1= rclo1 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo1_mult clo r:
  rclo1 clo (rclo1 clo r) <1= rclo1 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo1_compose clo r:
  rclo1 (rclo1 clo) r <1= rclo1 clo r.
Proof.
  intros. induction PR.
  - apply rclo1_base, R.
  - apply rclo1_mult.
    eapply rclo1_mon; [apply CLOR'|apply H].
  - apply rclo1_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo1_cpn.
    eapply cpn1_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat1_compat
      clo (WCOM: wcompatible1 clo):
  compatible1 (rclo1 clo).
Proof.
  econstructor; [eapply rclo1_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo1_base. apply PR.
    + eapply gf_mon.
      * eapply (wcompat1_wcompat WCOM).
        eapply (wcompat1_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo1_mult, PR.
    + eapply gf_mon; [apply CLOR'|].
      intros. apply H in PR. apply rclo1_step, PR.
    + eapply gf_mon; [|intros; apply rclo1_cpn, PR].
      apply (compat1_compat cpn1_compat).
      eapply cpn1_mon; [apply CLOR'|apply H].
  - eapply (cbound1_distr bnd_compat) in PR.
    destruct PR. revert x0 PTW.
    induction IN; intros.
    + left. apply PTW, R.
    + specialize (PTW _ CLOR').
      eapply (wcompat1_bound WCOM) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound1_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo1_mult.
        eapply rclo1_mon, R'. apply PR.
    + specialize (PTW _ CLOR').
      eapply (cbound1_compat bnd_compat) in PTW.
      right. eapply gf_mon. apply PTW. intros.
      eapply (cbound1_distr bnd_compat) in PR.
      destruct PR.
      eapply H in IN; [|apply PTW0].
      destruct IN.
      * apply rclo1_cpn, cpn1_bound.
        eapply cbound1_mon. apply H0. apply rclo1_base.
      * apply rclo1_step. apply H0.
    + specialize (PTW _ CLOR').
      apply (compat1_bound cpn1_compat) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound1_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo1_cpn.
        eapply cpn1_mon; [apply PR|].
        intros. apply R', PR0.
Qed.

Lemma wcompat1_sound clo (WCOM: wcompatible1 clo):
  clo <2= cpn1.
Proof.
  intros. exists (rclo1 clo).
  - apply wcompat1_compat, WCOM.
  - apply rclo1_clo.
    eapply (wcompat1_mon WCOM); [apply PR|].
    intros. apply rclo1_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn1_from_upaco r:
  upaco1 fcpn1 r <1= cpn1 r.
Proof.
  intros. destruct PR; [| apply cpn1_base, H].
  exists (rclo1 (paco1 fcpn1)).
  - apply wcompat1_compat.
    econstructor; [apply paco1_mon| |].
    + intros. _punfold PR; [|apply fcpn1_mon].
      eapply gf_mon; [apply PR|].
      intros. apply rclo1_cpn.
      eapply cpn1_mon; [apply PR0|].
      intros. destruct PR1.
      * apply rclo1_clo.
        eapply paco1_mon; [apply H0|].
        intros. apply rclo1_step.
        eapply gf_mon; [apply PR1|].
        intros. apply rclo1_base, PR2.
      * apply rclo1_step.
        eapply gf_mon; [apply H0|].
        intros. apply rclo1_base, PR1.
    + intros. right.
      eapply gf_mon, rclo1_cpn.
      eapply gf_mon, cpn1_bound.
      apply (cbound1_compat bnd_compat).
      eapply cbound1_mon. apply PR.
      intros. _punfold PR0; [|apply fcpn1_mon].
      eapply gf_mon. apply PR0.
      intros. apply rclo1_cpn.
      eapply cpn1_mon. apply PR1.
      intros. destruct PR2.
      * apply rclo1_clo.
        eapply paco1_mon. apply H0.
        intros. apply rclo1_base. apply PR2.
      * apply rclo1_base. apply H0.
  - apply rclo1_clo.
    eapply paco1_mon; [apply H|].
    intros. apply rclo1_base, PR.
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

Lemma cpn1_unfold_bound r
      (BASE: forall r, r <1= bnd r):
  cpn1 r <1= (bnd r \1/ fcpn1 r).
Proof.
  intros. apply BASE in PR.
  eapply compat1_bound in PR.
  - apply PR.
  - apply cpn1_compat.
Qed.

Lemma cpn1_step r:
  fcpn1 r <1= cpn1 r.
Proof.
  intros. eapply cpn1_clo, PR.
  intros. eapply wcompat1_sound, PR0.
  econstructor; [apply gf_mon| |].
  - intros. eapply gf_mon; [apply PR1|].
    intros. apply rclo1_step.
    eapply gf_mon; [apply PR2|].
    intros. apply rclo1_base, PR3.
  - intros. apply (cbound1_compat bnd_compat) in PR1.
    right. eapply gf_mon. apply PR1.
    intros. apply rclo1_cpn, cpn1_bound.
    eapply cbound1_mon. apply PR2.
    intros. apply rclo1_base, PR3.
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

Lemma cbound1_bot gf:
  compatible_bound1 gf bot2.
Proof.
  econstructor; intros; contradiction.
Qed.

Lemma cpn1_mon_bot (gf gf': rel -> rel) bnd bnd' e0 r
      (IN: @cpn1 gf bnd bot1 e0)
      (MON: monotone1 gf)
      (MON': monotone1 gf')
      (BASE: compatible_bound1 gf bnd)
      (BASE': compatible_bound1 gf' bnd')
      (LE: gf <2= gf'):
  @cpn1 gf' bnd' r e0.
Proof.
  apply cpn1_init in IN; [|apply MON|apply BASE].
  apply cpn1_final; [apply MON'|apply BASE'|].
  left. eapply paco1_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn1_mon_bot (gf gf': rel -> rel) bnd bnd' e0 r
      (IN: @fcpn1 gf bnd bot1 e0)
      (MON: monotone1 gf)
      (MON': monotone1 gf')
      (BASE: compatible_bound1 gf bnd)
      (BASE': compatible_bound1 gf' bnd')
      (LE: gf <2= gf'):
  @fcpn1 gf' bnd' r e0.
Proof.
  apply LE. eapply MON. apply IN.
  intros. eapply cpn1_mon_bot; eassumption.
Qed.

End Companion1.

Hint Unfold fcpn1 : paco.
Hint Resolve cpn1_base : paco.
Hint Resolve cpn1_step : paco.
Hint Resolve cbound1_bot : paco.

Hint Constructors rclo1 : rclo.
Hint Resolve rclo1_clo rclo1_step rclo1_cpn : rclo.

