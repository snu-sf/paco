Require Export Program.Basics. Open Scope program_scope.
Require Import paco4 pacotac.
Set Implicit Arguments.

Section Companion4.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.

Local Notation rel := (rel4 T0 T1 T2 T3).

Section Companion4_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone4 gf.

(** 
  Bounded Compatibility, Companion & Guarded Companion
*)

Inductive pointwise_union (bnd: rel -> rel) (r: rel) e0 e1 e2 e3 : Prop :=
| pw_union_ d0 d1 d2 d3
            (IN: r d0 d1 d2 d3)
            (PTW: forall (s: rel), s d0 d1 d2 d3 -> bnd s e0 e1 e2 e3)
.

Structure compatible_bound4 (bnd: rel -> rel) : Prop :=
  cbound4_intro {
      cbound4_distr : forall r,
          bnd r <4= pointwise_union bnd r;
      cbound4_compat: forall r,
          bnd (gf r) <4= gf (bnd r);
      cbound4_bound: forall r,
          bnd (bnd r) <4= (bnd r \4/ gf (bnd r));
    }.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound4 bnd.

Structure compatible4 (clo: rel -> rel) : Prop :=
  compat4_intro {
      compat4_mon: monotone4 clo;
      compat4_compat : forall r,
          clo (gf r) <4= gf (clo r);
      compat4_bound : forall r,
          bnd (clo r) <4= (bnd r \4/ gf (clo r))
    }.

Inductive cpn4 (r: rel) e0 e1 e2 e3 : Prop :=
| cpn4_intro
    clo
    (COM: compatible4 clo)
    (CLO: clo r e0 e1 e2 e3)
.

Definition fcpn4 := compose gf cpn4.

Lemma cbound4_union r1 r2 : bnd (r1 \4/ r2) <4= (bnd r1 \4/ bnd r2).
Proof.
  intros. eapply cbound4_distr in PR; [|apply bnd_compat].
  destruct PR. destruct IN.
  - left. apply PTW, H.
  - right. apply PTW, H.
Qed.

Lemma cbound4_mon: monotone4 bnd.
Proof.
  repeat intro.
  apply (cbound4_distr bnd_compat) in IN.
  destruct IN.
  apply PTW, LE, IN.
Qed.

Lemma cpn4_mon: monotone4 cpn4.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat4_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn4_compat: compatible4 cpn4.
Proof.
  econstructor; [apply cpn4_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (compat4_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - eapply (cbound4_distr bnd_compat) in PR.
    destruct PR. destruct IN.
    specialize (PTW (clo r) CLO).
    apply (compat4_bound COM) in PTW.
    destruct PTW.
    + left. apply H.
    + right. eapply gf_mon; [apply H|].
      intros. econstructor;[apply COM|apply PR].
Qed.

Lemma cpn4_greatest: forall clo (COM: compatible4 clo), clo <5= cpn4.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn4_base: forall r, r <4= cpn4 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
    + left. apply PR0.
  - apply PR.
Qed.

Lemma cpn4_bound : forall r, bnd r <4= cpn4 r.
Proof.
  intros. exists bnd.
  - econstructor; repeat intro.
    + eapply cbound4_mon. apply IN. apply LE.
    + apply (cbound4_compat bnd_compat), PR0.
    + apply (cbound4_bound bnd_compat), PR0.
  - apply PR.
Qed.

Lemma cpn4_cpn: forall r,
    cpn4 (cpn4 r) <4= cpn4 r.
Proof.
  intros. exists (compose cpn4 cpn4); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn4_mon; [apply IN|].
    intros. eapply cpn4_mon; [apply PR0|apply LE].
  - intros. eapply (compat4_compat cpn4_compat).
    eapply cpn4_mon; [apply PR0|].
    intros. eapply (compat4_compat cpn4_compat), PR1.
  - intros. eapply (compat4_bound cpn4_compat) in PR0.
    destruct PR0; [|right; apply H].
    eapply (compat4_bound cpn4_compat) in H.
    destruct H; [left; apply H|].
    right. eapply gf_mon; [apply H|].
    intros. apply cpn4_base. apply PR0.
Qed.

Lemma fcpn4_mon: monotone4 fcpn4.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn4_mon; [apply PR|apply LE].
Qed.

Lemma fcpn4_sound:
  paco4 fcpn4 bot4 <4= paco4 gf bot4.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \4/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn4 n (paco4 fcpn4 bot4) x0 x1 x2 x3) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn4 n (paco4 fcpn4 bot4) <4= gf (rclo cpn4 (S n) (paco4 fcpn4 bot4))).
  { intro X. revert x0 x1 x2 x3 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply fcpn4_mon].
    + intros. right. eapply cpn4_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat4_compat cpn4_compat).
        eapply (compat4_mon cpn4_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo4 (clo: rel->rel) (r: rel): rel :=
| rclo4_base
    e0 e1 e2 e3
    (R: r e0 e1 e2 e3):
    @rclo4 clo r e0 e1 e2 e3
| rclo4_clo'
    r' e0 e1 e2 e3
    (R': r' <4= rclo4 clo r)
    (CLOR': clo r' e0 e1 e2 e3):
    @rclo4 clo r e0 e1 e2 e3
| rclo4_step'
    r' e0 e1 e2 e3
    (R': r' <4= rclo4 clo r)
    (CLOR': @gf r' e0 e1 e2 e3):
    @rclo4 clo r e0 e1 e2 e3
| rclo4_cpn'
    r' e0 e1 e2 e3
    (R': r' <4= rclo4 clo r)
    (CLOR': @cpn4 r' e0 e1 e2 e3):
    @rclo4 clo r e0 e1 e2 e3
.

Structure wcompatible4 (clo: rel -> rel) : Prop :=
  wcompat4_intro {
      wcompat4_mon: monotone4 clo;
      wcompat4_wcompat: forall r,
          clo (gf r) <4= gf (rclo4 clo r);
      wcompat4_bound : forall r,
          bnd (clo r) <4= (bnd r \4/ gf (rclo4 clo r))
    }.

Lemma rclo4_mon_gen clo clo' r r' e0 e1 e2 e3
      (IN: @rclo4 clo r e0 e1 e2 e3)
      (LEclo: clo <5= clo')
      (LEr: r <4= r') :
  @rclo4 clo' r' e0 e1 e2 e3.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn4_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo4_mon clo:
  monotone4 (rclo4 clo).
Proof.
  repeat intro. eapply rclo4_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo4_clo clo r:
  clo (rclo4 clo r) <4= rclo4 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo4_step clo r:
  gf (rclo4 clo r) <4= rclo4 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo4_cpn clo r:
  cpn4 (rclo4 clo r) <4= rclo4 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo4_mult clo r:
  rclo4 clo (rclo4 clo r) <4= rclo4 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo4_compose clo r:
  rclo4 (rclo4 clo) r <4= rclo4 clo r.
Proof.
  intros. induction PR.
  - apply rclo4_base, R.
  - apply rclo4_mult.
    eapply rclo4_mon; [apply CLOR'|apply H].
  - apply rclo4_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo4_cpn.
    eapply cpn4_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat4_compat
      clo (WCOM: wcompatible4 clo):
  compatible4 (rclo4 clo).
Proof.
  econstructor; [eapply rclo4_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo4_base. apply PR.
    + eapply gf_mon.
      * eapply (wcompat4_wcompat WCOM).
        eapply (wcompat4_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo4_mult, PR.
    + eapply gf_mon; [apply CLOR'|].
      intros. apply H in PR. apply rclo4_step, PR.
    + eapply gf_mon; [|intros; apply rclo4_cpn, PR].
      apply (compat4_compat cpn4_compat).
      eapply cpn4_mon; [apply CLOR'|apply H].
  - eapply (cbound4_distr bnd_compat) in PR.
    destruct PR. revert x0 x1 x2 x3 PTW.
    induction IN; intros.
    + left. apply PTW, R.
    + specialize (PTW _ CLOR').
      eapply (wcompat4_bound WCOM) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound4_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo4_mult.
        eapply rclo4_mon, R'. apply PR.
    + specialize (PTW _ CLOR').
      eapply (cbound4_compat bnd_compat) in PTW.
      right. eapply gf_mon. apply PTW. intros.
      eapply (cbound4_distr bnd_compat) in PR.
      destruct PR.
      eapply H in IN; [|apply PTW0].
      destruct IN.
      * apply rclo4_cpn, cpn4_bound.
        eapply cbound4_mon. apply H0. apply rclo4_base.
      * apply rclo4_step. apply H0.
    + specialize (PTW _ CLOR').
      apply (compat4_bound cpn4_compat) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound4_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo4_cpn.
        eapply cpn4_mon; [apply PR|].
        intros. apply R', PR0.
Qed.

Lemma wcompat4_sound clo (WCOM: wcompatible4 clo):
  clo <5= cpn4.
Proof.
  intros. exists (rclo4 clo).
  - apply wcompat4_compat, WCOM.
  - apply rclo4_clo.
    eapply (wcompat4_mon WCOM); [apply PR|].
    intros. apply rclo4_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn4_from_upaco r:
  upaco4 fcpn4 r <4= cpn4 r.
Proof.
  intros. destruct PR; [| apply cpn4_base, H].
  exists (rclo4 (paco4 fcpn4)).
  - apply wcompat4_compat.
    econstructor; [apply paco4_mon| |].
    + intros. _punfold PR; [|apply fcpn4_mon].
      eapply gf_mon; [apply PR|].
      intros. apply rclo4_cpn.
      eapply cpn4_mon; [apply PR0|].
      intros. destruct PR1.
      * apply rclo4_clo.
        eapply paco4_mon; [apply H0|].
        intros. apply rclo4_step.
        eapply gf_mon; [apply PR1|].
        intros. apply rclo4_base, PR2.
      * apply rclo4_step.
        eapply gf_mon; [apply H0|].
        intros. apply rclo4_base, PR1.
    + intros. right.
      eapply gf_mon, rclo4_cpn.
      eapply gf_mon, cpn4_bound.
      apply (cbound4_compat bnd_compat).
      eapply cbound4_mon. apply PR.
      intros. _punfold PR0; [|apply fcpn4_mon].
      eapply gf_mon. apply PR0.
      intros. apply rclo4_cpn.
      eapply cpn4_mon. apply PR1.
      intros. destruct PR2.
      * apply rclo4_clo.
        eapply paco4_mon. apply H0.
        intros. apply rclo4_base. apply PR2.
      * apply rclo4_base. apply H0.
  - apply rclo4_clo.
    eapply paco4_mon; [apply H|].
    intros. apply rclo4_base, PR.
Qed.

Lemma cpn4_from_paco r:
  paco4 fcpn4 r <4= cpn4 r.
Proof. intros. apply cpn4_from_upaco. left. apply PR. Qed.

Lemma fcpn4_from_paco r:
  paco4 fcpn4 r <4= fcpn4 r.
Proof.
  intros. _punfold PR; [|apply fcpn4_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn4_cpn.
  eapply cpn4_mon; [apply PR0|].
  apply cpn4_from_upaco.
Qed.

Lemma fcpn4_to_paco r:
  fcpn4 r <4= paco4 fcpn4 r.
Proof.
  intros. pfold. eapply fcpn4_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn4_complete:
  paco4 gf bot4 <4= cpn4 bot4.
Proof.
  intros. apply cpn4_from_paco.
  eapply paco4_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn4_base].
  - intros. apply PR0.
Qed.

Lemma cpn4_init:
  cpn4 bot4 <4= paco4 gf bot4.
Proof.
  intros. apply fcpn4_sound, fcpn4_to_paco, (compat4_compat cpn4_compat).
  eapply cpn4_mon; [apply PR|contradiction].
Qed.

Lemma cpn4_clo
      r clo (LE: clo <5= cpn4):
  clo (cpn4 r) <4= cpn4 r.
Proof.
  intros. apply cpn4_cpn, LE, PR.
Qed.

Lemma cpn4_unfold:
  cpn4 bot4 <4= fcpn4 bot4.
Proof.
  intros. apply cpn4_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn4_complete, PR0.
Qed.

Lemma cpn4_unfold_bound r
      (BASE: forall r, r <4= bnd r):
  cpn4 r <4= (bnd r \4/ fcpn4 r).
Proof.
  intros. apply BASE in PR.
  eapply compat4_bound in PR.
  - apply PR.
  - apply cpn4_compat.
Qed.

Lemma cpn4_step r:
  fcpn4 r <4= cpn4 r.
Proof.
  intros. eapply cpn4_clo, PR.
  intros. eapply wcompat4_sound, PR0.
  econstructor; [apply gf_mon| |].
  - intros. eapply gf_mon; [apply PR1|].
    intros. apply rclo4_step.
    eapply gf_mon; [apply PR2|].
    intros. apply rclo4_base, PR3.
  - intros. apply (cbound4_compat bnd_compat) in PR1.
    right. eapply gf_mon. apply PR1.
    intros. apply rclo4_cpn, cpn4_bound.
    eapply cbound4_mon. apply PR2.
    intros. apply rclo4_base, PR3.
Qed.

Lemma fcpn4_clo
      r clo (LE: clo <5= cpn4):
  clo (fcpn4 r) <4= fcpn4 r.
Proof.
  intros. apply LE, (compat4_compat cpn4_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn4_cpn, PR0.
Qed.

Lemma cpn4_final: forall r, upaco4 gf r <4= cpn4 r.
Proof.
  intros. eapply cpn4_from_upaco.
  intros. eapply upaco4_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn4_base, PR1.
Qed.

Lemma fcpn4_final: forall r, paco4 gf r <4= fcpn4 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn4_final].
Qed.

Lemma cpn4_algebra r :
  r <4= gf r -> r <4= cpn4 bot4.
Proof.
  intros. apply cpn4_final. left.
  revert x0 x1 x2 x3 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion4_main.

Lemma cbound4_bot gf:
  compatible_bound4 gf bot5.
Proof.
  econstructor; intros; contradiction.
Qed.

Lemma cpn4_mon_bot (gf gf': rel -> rel) bnd bnd' e0 e1 e2 e3 r
      (IN: @cpn4 gf bnd bot4 e0 e1 e2 e3)
      (MON: monotone4 gf)
      (MON': monotone4 gf')
      (BASE: compatible_bound4 gf bnd)
      (BASE': compatible_bound4 gf' bnd')
      (LE: gf <5= gf'):
  @cpn4 gf' bnd' r e0 e1 e2 e3.
Proof.
  apply cpn4_init in IN; [|apply MON|apply BASE].
  apply cpn4_final; [apply MON'|apply BASE'|].
  left. eapply paco4_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn4_mon_bot (gf gf': rel -> rel) bnd bnd' e0 e1 e2 e3 r
      (IN: @fcpn4 gf bnd bot4 e0 e1 e2 e3)
      (MON: monotone4 gf)
      (MON': monotone4 gf')
      (BASE: compatible_bound4 gf bnd)
      (BASE': compatible_bound4 gf' bnd')
      (LE: gf <5= gf'):
  @fcpn4 gf' bnd' r e0 e1 e2 e3.
Proof.
  apply LE. eapply MON. apply IN.
  intros. eapply cpn4_mon_bot; eassumption.
Qed.

End Companion4.

Hint Unfold fcpn4 : paco.
Hint Resolve cpn4_base : paco.
Hint Resolve cpn4_step : paco.
Hint Resolve cbound4_bot : paco.

Hint Constructors rclo4 : rclo.
Hint Resolve rclo4_clo rclo4_step rclo4_cpn : rclo.

