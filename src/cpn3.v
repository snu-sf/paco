Require Export Program.Basics. Open Scope program_scope.
Require Import paco3 pacotac.
Set Implicit Arguments.

Section Companion3.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.

Local Notation rel := (rel3 T0 T1 T2).

Section Companion3_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone3 gf.

(** 
  Bounded Compatibility, Companion & Guarded Companion
*)

Inductive pointwise_union (bnd: rel -> rel) (r: rel) e0 e1 e2 : Prop :=
| pw_union_ d0 d1 d2
            (IN: r d0 d1 d2)
            (PTW: forall (s: rel), s d0 d1 d2 -> bnd s e0 e1 e2)
.

Structure compatible_bound3 (bnd: rel -> rel) : Prop :=
  cbound3_intro {
      cbound3_distr : forall r,
          bnd r <3= pointwise_union bnd r;
      cbound3_compat: forall r,
          bnd (gf r) <3= gf (bnd r);
      cbound3_bound: forall r,
          bnd (bnd r) <3= (bnd r \3/ gf (bnd r));
    }.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound3 bnd.

Structure compatible3 (clo: rel -> rel) : Prop :=
  compat3_intro {
      compat3_mon: monotone3 clo;
      compat3_compat : forall r,
          clo (gf r) <3= gf (clo r);
      compat3_bound : forall r,
          bnd (clo r) <3= (bnd r \3/ gf (clo r))
    }.

Inductive cpn3 (r: rel) e0 e1 e2 : Prop :=
| cpn3_intro
    clo
    (COM: compatible3 clo)
    (CLO: clo r e0 e1 e2)
.

Definition fcpn3 := compose gf cpn3.

Lemma cbound3_union r1 r2 : bnd (r1 \3/ r2) <3= (bnd r1 \3/ bnd r2).
Proof.
  intros. eapply cbound3_distr in PR; [|apply bnd_compat].
  destruct PR. destruct IN.
  - left. apply PTW, H.
  - right. apply PTW, H.
Qed.

Lemma cbound3_mon: monotone3 bnd.
Proof.
  repeat intro.
  apply (cbound3_distr bnd_compat) in IN.
  destruct IN.
  apply PTW, LE, IN.
Qed.

Lemma cpn3_mon: monotone3 cpn3.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat3_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn3_compat: compatible3 cpn3.
Proof.
  econstructor; [apply cpn3_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (compat3_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - eapply (cbound3_distr bnd_compat) in PR.
    destruct PR. destruct IN.
    specialize (PTW (clo r) CLO).
    apply (compat3_bound COM) in PTW.
    destruct PTW.
    + left. apply H.
    + right. eapply gf_mon; [apply H|].
      intros. econstructor;[apply COM|apply PR].
Qed.

Lemma cpn3_greatest: forall clo (COM: compatible3 clo), clo <4= cpn3.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn3_base: forall r, r <3= cpn3 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
    + left. apply PR0.
  - apply PR.
Qed.

Lemma cpn3_bound : forall r, bnd r <3= cpn3 r.
Proof.
  intros. exists bnd.
  - econstructor; repeat intro.
    + eapply cbound3_mon. apply IN. apply LE.
    + apply (cbound3_compat bnd_compat), PR0.
    + apply (cbound3_bound bnd_compat), PR0.
  - apply PR.
Qed.

Lemma cpn3_cpn: forall r,
    cpn3 (cpn3 r) <3= cpn3 r.
Proof.
  intros. exists (compose cpn3 cpn3); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn3_mon; [apply IN|].
    intros. eapply cpn3_mon; [apply PR0|apply LE].
  - intros. eapply (compat3_compat cpn3_compat).
    eapply cpn3_mon; [apply PR0|].
    intros. eapply (compat3_compat cpn3_compat), PR1.
  - intros. eapply (compat3_bound cpn3_compat) in PR0.
    destruct PR0; [|right; apply H].
    eapply (compat3_bound cpn3_compat) in H.
    destruct H; [left; apply H|].
    right. eapply gf_mon; [apply H|].
    intros. apply cpn3_base. apply PR0.
Qed.

Lemma fcpn3_mon: monotone3 fcpn3.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn3_mon; [apply PR|apply LE].
Qed.

Lemma fcpn3_sound:
  paco3 fcpn3 bot3 <3= paco3 gf bot3.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \3/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn3 n (paco3 fcpn3 bot3) x0 x1 x2) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn3 n (paco3 fcpn3 bot3) <3= gf (rclo cpn3 (S n) (paco3 fcpn3 bot3))).
  { intro X. revert x0 x1 x2 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply fcpn3_mon].
    + intros. right. eapply cpn3_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat3_compat cpn3_compat).
        eapply (compat3_mon cpn3_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo3 (clo: rel->rel) (r: rel): rel :=
| rclo3_base
    e0 e1 e2
    (R: r e0 e1 e2):
    @rclo3 clo r e0 e1 e2
| rclo3_clo'
    r' e0 e1 e2
    (R': r' <3= rclo3 clo r)
    (CLOR': clo r' e0 e1 e2):
    @rclo3 clo r e0 e1 e2
| rclo3_step'
    r' e0 e1 e2
    (R': r' <3= rclo3 clo r)
    (CLOR': @gf r' e0 e1 e2):
    @rclo3 clo r e0 e1 e2
| rclo3_cpn'
    r' e0 e1 e2
    (R': r' <3= rclo3 clo r)
    (CLOR': @cpn3 r' e0 e1 e2):
    @rclo3 clo r e0 e1 e2
.

Structure wcompatible3 (clo: rel -> rel) : Prop :=
  wcompat3_intro {
      wcompat3_mon: monotone3 clo;
      wcompat3_wcompat: forall r,
          clo (gf r) <3= gf (rclo3 clo r);
      wcompat3_bound : forall r,
          bnd (clo r) <3= (bnd r \3/ gf (rclo3 clo r))
    }.

Lemma rclo3_mon_gen clo clo' r r' e0 e1 e2
      (IN: @rclo3 clo r e0 e1 e2)
      (LEclo: clo <4= clo')
      (LEr: r <3= r') :
  @rclo3 clo' r' e0 e1 e2.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn3_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo3_mon clo:
  monotone3 (rclo3 clo).
Proof.
  repeat intro. eapply rclo3_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo3_clo clo r:
  clo (rclo3 clo r) <3= rclo3 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo3_step clo r:
  gf (rclo3 clo r) <3= rclo3 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo3_cpn clo r:
  cpn3 (rclo3 clo r) <3= rclo3 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo3_mult clo r:
  rclo3 clo (rclo3 clo r) <3= rclo3 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo3_compose clo r:
  rclo3 (rclo3 clo) r <3= rclo3 clo r.
Proof.
  intros. induction PR.
  - apply rclo3_base, R.
  - apply rclo3_mult.
    eapply rclo3_mon; [apply CLOR'|apply H].
  - apply rclo3_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo3_cpn.
    eapply cpn3_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat3_compat
      clo (WCOM: wcompatible3 clo):
  compatible3 (rclo3 clo).
Proof.
  econstructor; [eapply rclo3_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo3_base. apply PR.
    + eapply gf_mon.
      * eapply (wcompat3_wcompat WCOM).
        eapply (wcompat3_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo3_mult, PR.
    + eapply gf_mon; [apply CLOR'|].
      intros. apply H in PR. apply rclo3_step, PR.
    + eapply gf_mon; [|intros; apply rclo3_cpn, PR].
      apply (compat3_compat cpn3_compat).
      eapply cpn3_mon; [apply CLOR'|apply H].
  - eapply (cbound3_distr bnd_compat) in PR.
    destruct PR. revert x0 x1 x2 PTW.
    induction IN; intros.
    + left. apply PTW, R.
    + specialize (PTW _ CLOR').
      eapply (wcompat3_bound WCOM) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound3_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo3_mult.
        eapply rclo3_mon, R'. apply PR.
    + specialize (PTW _ CLOR').
      eapply (cbound3_compat bnd_compat) in PTW.
      right. eapply gf_mon. apply PTW. intros.
      eapply (cbound3_distr bnd_compat) in PR.
      destruct PR.
      eapply H in IN; [|apply PTW0].
      destruct IN.
      * apply rclo3_cpn, cpn3_bound.
        eapply cbound3_mon. apply H0. apply rclo3_base.
      * apply rclo3_step. apply H0.
    + specialize (PTW _ CLOR').
      apply (compat3_bound cpn3_compat) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound3_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo3_cpn.
        eapply cpn3_mon; [apply PR|].
        intros. apply R', PR0.
Qed.

Lemma wcompat3_sound clo (WCOM: wcompatible3 clo):
  clo <4= cpn3.
Proof.
  intros. exists (rclo3 clo).
  - apply wcompat3_compat, WCOM.
  - apply rclo3_clo.
    eapply (wcompat3_mon WCOM); [apply PR|].
    intros. apply rclo3_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn3_from_upaco r:
  upaco3 fcpn3 r <3= cpn3 r.
Proof.
  intros. destruct PR; [| apply cpn3_base, H].
  exists (rclo3 (paco3 fcpn3)).
  - apply wcompat3_compat.
    econstructor; [apply paco3_mon| |].
    + intros. _punfold PR; [|apply fcpn3_mon].
      eapply gf_mon; [apply PR|].
      intros. apply rclo3_cpn.
      eapply cpn3_mon; [apply PR0|].
      intros. destruct PR1.
      * apply rclo3_clo.
        eapply paco3_mon; [apply H0|].
        intros. apply rclo3_step.
        eapply gf_mon; [apply PR1|].
        intros. apply rclo3_base, PR2.
      * apply rclo3_step.
        eapply gf_mon; [apply H0|].
        intros. apply rclo3_base, PR1.
    + intros. right.
      eapply gf_mon, rclo3_cpn.
      eapply gf_mon, cpn3_bound.
      apply (cbound3_compat bnd_compat).
      eapply cbound3_mon. apply PR.
      intros. _punfold PR0; [|apply fcpn3_mon].
      eapply gf_mon. apply PR0.
      intros. apply rclo3_cpn.
      eapply cpn3_mon. apply PR1.
      intros. destruct PR2.
      * apply rclo3_clo.
        eapply paco3_mon. apply H0.
        intros. apply rclo3_base. apply PR2.
      * apply rclo3_base. apply H0.
  - apply rclo3_clo.
    eapply paco3_mon; [apply H|].
    intros. apply rclo3_base, PR.
Qed.

Lemma cpn3_from_paco r:
  paco3 fcpn3 r <3= cpn3 r.
Proof. intros. apply cpn3_from_upaco. left. apply PR. Qed.

Lemma fcpn3_from_paco r:
  paco3 fcpn3 r <3= fcpn3 r.
Proof.
  intros. _punfold PR; [|apply fcpn3_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn3_cpn.
  eapply cpn3_mon; [apply PR0|].
  apply cpn3_from_upaco.
Qed.

Lemma fcpn3_to_paco r:
  fcpn3 r <3= paco3 fcpn3 r.
Proof.
  intros. pfold. eapply fcpn3_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn3_complete:
  paco3 gf bot3 <3= cpn3 bot3.
Proof.
  intros. apply cpn3_from_paco.
  eapply paco3_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn3_base].
  - intros. apply PR0.
Qed.

Lemma cpn3_init:
  cpn3 bot3 <3= paco3 gf bot3.
Proof.
  intros. apply fcpn3_sound, fcpn3_to_paco, (compat3_compat cpn3_compat).
  eapply cpn3_mon; [apply PR|contradiction].
Qed.

Lemma cpn3_clo
      r clo (LE: clo <4= cpn3):
  clo (cpn3 r) <3= cpn3 r.
Proof.
  intros. apply cpn3_cpn, LE, PR.
Qed.

Lemma cpn3_unfold:
  cpn3 bot3 <3= fcpn3 bot3.
Proof.
  intros. apply cpn3_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn3_complete, PR0.
Qed.

Lemma cpn3_unfold_bound r
      (BASE: forall r, r <3= bnd r):
  cpn3 r <3= (bnd r \3/ fcpn3 r).
Proof.
  intros. apply BASE in PR.
  eapply compat3_bound in PR.
  - apply PR.
  - apply cpn3_compat.
Qed.

Lemma cpn3_step r:
  fcpn3 r <3= cpn3 r.
Proof.
  intros. eapply cpn3_clo, PR.
  intros. eapply wcompat3_sound, PR0.
  econstructor; [apply gf_mon| |].
  - intros. eapply gf_mon; [apply PR1|].
    intros. apply rclo3_step.
    eapply gf_mon; [apply PR2|].
    intros. apply rclo3_base, PR3.
  - intros. apply (cbound3_compat bnd_compat) in PR1.
    right. eapply gf_mon. apply PR1.
    intros. apply rclo3_cpn, cpn3_bound.
    eapply cbound3_mon. apply PR2.
    intros. apply rclo3_base, PR3.
Qed.

Lemma fcpn3_clo
      r clo (LE: clo <4= cpn3):
  clo (fcpn3 r) <3= fcpn3 r.
Proof.
  intros. apply LE, (compat3_compat cpn3_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn3_cpn, PR0.
Qed.

Lemma cpn3_final: forall r, upaco3 gf r <3= cpn3 r.
Proof.
  intros. eapply cpn3_from_upaco.
  intros. eapply upaco3_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn3_base, PR1.
Qed.

Lemma fcpn3_final: forall r, paco3 gf r <3= fcpn3 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn3_final].
Qed.

Lemma cpn3_algebra r :
  r <3= gf r -> r <3= cpn3 bot3.
Proof.
  intros. apply cpn3_final. left.
  revert x0 x1 x2 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion3_main.

Lemma cbound3_bot gf:
  compatible_bound3 gf bot4.
Proof.
  econstructor; intros; contradiction.
Qed.

Lemma cpn3_mon_bot (gf gf': rel -> rel) bnd bnd' e0 e1 e2 r
      (IN: @cpn3 gf bnd bot3 e0 e1 e2)
      (MON: monotone3 gf)
      (MON': monotone3 gf')
      (BASE: compatible_bound3 gf bnd)
      (BASE': compatible_bound3 gf' bnd')
      (LE: gf <4= gf'):
  @cpn3 gf' bnd' r e0 e1 e2.
Proof.
  apply cpn3_init in IN; [|apply MON|apply BASE].
  apply cpn3_final; [apply MON'|apply BASE'|].
  left. eapply paco3_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn3_mon_bot (gf gf': rel -> rel) bnd bnd' e0 e1 e2 r
      (IN: @fcpn3 gf bnd bot3 e0 e1 e2)
      (MON: monotone3 gf)
      (MON': monotone3 gf')
      (BASE: compatible_bound3 gf bnd)
      (BASE': compatible_bound3 gf' bnd')
      (LE: gf <4= gf'):
  @fcpn3 gf' bnd' r e0 e1 e2.
Proof.
  apply LE. eapply MON. apply IN.
  intros. eapply cpn3_mon_bot; eassumption.
Qed.

End Companion3.

Hint Unfold fcpn3 : paco.
Hint Resolve cpn3_base : paco.
Hint Resolve cpn3_step : paco.
Hint Resolve cbound3_bot : paco.

Hint Constructors rclo3 : rclo.
Hint Resolve rclo3_clo rclo3_step rclo3_cpn : rclo.

