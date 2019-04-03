Require Export Program.Basics. Open Scope program_scope.
Require Import paco11 pacotac.
Set Implicit Arguments.

Section Companion11.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.

Local Notation rel := (rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10).

Section Companion11_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone11 gf.

(** 
  Bounded Compatibility, Companion & Guarded Companion
*)

Inductive pointwise_union (bnd: rel -> rel) (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 : Prop :=
| pw_union_ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
            (IN: r d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10)
            (PTW: forall (s: rel), s d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 -> bnd s e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)
.

Structure compatible_bound11 (bnd: rel -> rel) : Prop :=
  cbound11_intro {
      cbound11_distr : forall r,
          bnd r <11= pointwise_union bnd r;
      cbound11_compat: forall r,
          bnd (gf r) <11= gf (bnd r);
      cbound11_bound: forall r,
          bnd (bnd r) <11= (bnd r \11/ gf (bnd r));
    }.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound11 bnd.

Structure compatible11 (clo: rel -> rel) : Prop :=
  compat11_intro {
      compat11_mon: monotone11 clo;
      compat11_compat : forall r,
          clo (gf r) <11= gf (clo r);
      compat11_bound : forall r,
          bnd (clo r) <11= (bnd r \11/ gf (clo r))
    }.

Inductive cpn11 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 : Prop :=
| cpn11_intro
    clo
    (COM: compatible11 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)
.

Definition fcpn11 := compose gf cpn11.

Lemma cbound11_union r1 r2 : bnd (r1 \11/ r2) <11= (bnd r1 \11/ bnd r2).
Proof.
  intros. eapply cbound11_distr in PR; [|apply bnd_compat].
  destruct PR. destruct IN.
  - left. apply PTW, H.
  - right. apply PTW, H.
Qed.

Lemma cbound11_mon: monotone11 bnd.
Proof.
  repeat intro.
  apply (cbound11_distr bnd_compat) in IN.
  destruct IN.
  apply PTW, LE, IN.
Qed.

Lemma cpn11_mon: monotone11 cpn11.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat11_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn11_compat: compatible11 cpn11.
Proof.
  econstructor; [apply cpn11_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (compat11_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - eapply (cbound11_distr bnd_compat) in PR.
    destruct PR. destruct IN.
    specialize (PTW (clo r) CLO).
    apply (compat11_bound COM) in PTW.
    destruct PTW.
    + left. apply H.
    + right. eapply gf_mon; [apply H|].
      intros. econstructor;[apply COM|apply PR].
Qed.

Lemma cpn11_greatest: forall clo (COM: compatible11 clo), clo <12= cpn11.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn11_base: forall r, r <11= cpn11 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
    + left. apply PR0.
  - apply PR.
Qed.

Lemma cpn11_bound : forall r, bnd r <11= cpn11 r.
Proof.
  intros. exists bnd.
  - econstructor; repeat intro.
    + eapply cbound11_mon. apply IN. apply LE.
    + apply (cbound11_compat bnd_compat), PR0.
    + apply (cbound11_bound bnd_compat), PR0.
  - apply PR.
Qed.

Lemma cpn11_cpn: forall r,
    cpn11 (cpn11 r) <11= cpn11 r.
Proof.
  intros. exists (compose cpn11 cpn11); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn11_mon; [apply IN|].
    intros. eapply cpn11_mon; [apply PR0|apply LE].
  - intros. eapply (compat11_compat cpn11_compat).
    eapply cpn11_mon; [apply PR0|].
    intros. eapply (compat11_compat cpn11_compat), PR1.
  - intros. eapply (compat11_bound cpn11_compat) in PR0.
    destruct PR0; [|right; apply H].
    eapply (compat11_bound cpn11_compat) in H.
    destruct H; [left; apply H|].
    right. eapply gf_mon; [apply H|].
    intros. apply cpn11_base. apply PR0.
Qed.

Lemma fcpn11_mon: monotone11 fcpn11.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn11_mon; [apply PR|apply LE].
Qed.

Lemma fcpn11_sound:
  paco11 fcpn11 bot11 <11= paco11 gf bot11.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \11/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn11 n (paco11 fcpn11 bot11) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn11 n (paco11 fcpn11 bot11) <11= gf (rclo cpn11 (S n) (paco11 fcpn11 bot11))).
  { intro X. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply fcpn11_mon].
    + intros. right. eapply cpn11_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat11_compat cpn11_compat).
        eapply (compat11_mon cpn11_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo11 (clo: rel->rel) (r: rel): rel :=
| rclo11_base
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10):
    @rclo11 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
| rclo11_clo'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    (R': r' <11= rclo11 clo r)
    (CLOR': clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10):
    @rclo11 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
| rclo11_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    (R': r' <11= rclo11 clo r)
    (CLOR': @gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10):
    @rclo11 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
| rclo11_cpn'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    (R': r' <11= rclo11 clo r)
    (CLOR': @cpn11 r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10):
    @rclo11 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
.

Structure wcompatible11 (clo: rel -> rel) : Prop :=
  wcompat11_intro {
      wcompat11_mon: monotone11 clo;
      wcompat11_wcompat: forall r,
          clo (gf r) <11= gf (rclo11 clo r);
      wcompat11_bound : forall r,
          bnd (clo r) <11= (bnd r \11/ gf (rclo11 clo r))
    }.

Lemma rclo11_mon_gen clo clo' r r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
      (IN: @rclo11 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)
      (LEclo: clo <12= clo')
      (LEr: r <11= r') :
  @rclo11 clo' r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn11_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo11_mon clo:
  monotone11 (rclo11 clo).
Proof.
  repeat intro. eapply rclo11_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo11_clo clo r:
  clo (rclo11 clo r) <11= rclo11 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo11_step clo r:
  gf (rclo11 clo r) <11= rclo11 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo11_cpn clo r:
  cpn11 (rclo11 clo r) <11= rclo11 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo11_mult clo r:
  rclo11 clo (rclo11 clo r) <11= rclo11 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo11_compose clo r:
  rclo11 (rclo11 clo) r <11= rclo11 clo r.
Proof.
  intros. induction PR.
  - apply rclo11_base, R.
  - apply rclo11_mult.
    eapply rclo11_mon; [apply CLOR'|apply H].
  - apply rclo11_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo11_cpn.
    eapply cpn11_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat11_compat
      clo (WCOM: wcompatible11 clo):
  compatible11 (rclo11 clo).
Proof.
  econstructor; [eapply rclo11_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo11_base. apply PR.
    + eapply gf_mon.
      * eapply (wcompat11_wcompat WCOM).
        eapply (wcompat11_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo11_mult, PR.
    + eapply gf_mon; [apply CLOR'|].
      intros. apply H in PR. apply rclo11_step, PR.
    + eapply gf_mon; [|intros; apply rclo11_cpn, PR].
      apply (compat11_compat cpn11_compat).
      eapply cpn11_mon; [apply CLOR'|apply H].
  - eapply (cbound11_distr bnd_compat) in PR.
    destruct PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 PTW.
    induction IN; intros.
    + left. apply PTW, R.
    + specialize (PTW _ CLOR').
      eapply (wcompat11_bound WCOM) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound11_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo11_mult.
        eapply rclo11_mon, R'. apply PR.
    + specialize (PTW _ CLOR').
      eapply (cbound11_compat bnd_compat) in PTW.
      right. eapply gf_mon. apply PTW. intros.
      eapply (cbound11_distr bnd_compat) in PR.
      destruct PR.
      eapply H in IN; [|apply PTW0].
      destruct IN.
      * apply rclo11_cpn, cpn11_bound.
        eapply cbound11_mon. apply H0. apply rclo11_base.
      * apply rclo11_step. apply H0.
    + specialize (PTW _ CLOR').
      apply (compat11_bound cpn11_compat) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound11_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo11_cpn.
        eapply cpn11_mon; [apply PR|].
        intros. apply R', PR0.
Qed.

Lemma wcompat11_sound clo (WCOM: wcompatible11 clo):
  clo <12= cpn11.
Proof.
  intros. exists (rclo11 clo).
  - apply wcompat11_compat, WCOM.
  - apply rclo11_clo.
    eapply (wcompat11_mon WCOM); [apply PR|].
    intros. apply rclo11_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn11_from_upaco r:
  upaco11 fcpn11 r <11= cpn11 r.
Proof.
  intros. destruct PR; [| apply cpn11_base, H].
  exists (rclo11 (paco11 fcpn11)).
  - apply wcompat11_compat.
    econstructor; [apply paco11_mon| |].
    + intros. _punfold PR; [|apply fcpn11_mon].
      eapply gf_mon; [apply PR|].
      intros. apply rclo11_cpn.
      eapply cpn11_mon; [apply PR0|].
      intros. destruct PR1.
      * apply rclo11_clo.
        eapply paco11_mon; [apply H0|].
        intros. apply rclo11_step.
        eapply gf_mon; [apply PR1|].
        intros. apply rclo11_base, PR2.
      * apply rclo11_step.
        eapply gf_mon; [apply H0|].
        intros. apply rclo11_base, PR1.
    + intros. right.
      eapply gf_mon, rclo11_cpn.
      eapply gf_mon, cpn11_bound.
      apply (cbound11_compat bnd_compat).
      eapply cbound11_mon. apply PR.
      intros. _punfold PR0; [|apply fcpn11_mon].
      eapply gf_mon. apply PR0.
      intros. apply rclo11_cpn.
      eapply cpn11_mon. apply PR1.
      intros. destruct PR2.
      * apply rclo11_clo.
        eapply paco11_mon. apply H0.
        intros. apply rclo11_base. apply PR2.
      * apply rclo11_base. apply H0.
  - apply rclo11_clo.
    eapply paco11_mon; [apply H|].
    intros. apply rclo11_base, PR.
Qed.

Lemma cpn11_from_paco r:
  paco11 fcpn11 r <11= cpn11 r.
Proof. intros. apply cpn11_from_upaco. left. apply PR. Qed.

Lemma fcpn11_from_paco r:
  paco11 fcpn11 r <11= fcpn11 r.
Proof.
  intros. _punfold PR; [|apply fcpn11_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn11_cpn.
  eapply cpn11_mon; [apply PR0|].
  apply cpn11_from_upaco.
Qed.

Lemma fcpn11_to_paco r:
  fcpn11 r <11= paco11 fcpn11 r.
Proof.
  intros. pfold. eapply fcpn11_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn11_complete:
  paco11 gf bot11 <11= cpn11 bot11.
Proof.
  intros. apply cpn11_from_paco.
  eapply paco11_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn11_base].
  - intros. apply PR0.
Qed.

Lemma cpn11_init:
  cpn11 bot11 <11= paco11 gf bot11.
Proof.
  intros. apply fcpn11_sound, fcpn11_to_paco, (compat11_compat cpn11_compat).
  eapply cpn11_mon; [apply PR|contradiction].
Qed.

Lemma cpn11_clo
      r clo (LE: clo <12= cpn11):
  clo (cpn11 r) <11= cpn11 r.
Proof.
  intros. apply cpn11_cpn, LE, PR.
Qed.

Lemma cpn11_unfold:
  cpn11 bot11 <11= fcpn11 bot11.
Proof.
  intros. apply cpn11_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn11_complete, PR0.
Qed.

Lemma cpn11_unfold_bound r
      (BASE: forall r, r <11= bnd r):
  cpn11 r <11= (bnd r \11/ fcpn11 r).
Proof.
  intros. apply BASE in PR.
  eapply compat11_bound in PR.
  - apply PR.
  - apply cpn11_compat.
Qed.

Lemma cpn11_step r:
  fcpn11 r <11= cpn11 r.
Proof.
  intros. eapply cpn11_clo, PR.
  intros. eapply wcompat11_sound, PR0.
  econstructor; [apply gf_mon| |].
  - intros. eapply gf_mon; [apply PR1|].
    intros. apply rclo11_step.
    eapply gf_mon; [apply PR2|].
    intros. apply rclo11_base, PR3.
  - intros. apply (cbound11_compat bnd_compat) in PR1.
    right. eapply gf_mon. apply PR1.
    intros. apply rclo11_cpn, cpn11_bound.
    eapply cbound11_mon. apply PR2.
    intros. apply rclo11_base, PR3.
Qed.

Lemma fcpn11_clo
      r clo (LE: clo <12= cpn11):
  clo (fcpn11 r) <11= fcpn11 r.
Proof.
  intros. apply LE, (compat11_compat cpn11_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn11_cpn, PR0.
Qed.

Lemma cpn11_final: forall r, upaco11 gf r <11= cpn11 r.
Proof.
  intros. eapply cpn11_from_upaco.
  intros. eapply upaco11_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn11_base, PR1.
Qed.

Lemma fcpn11_final: forall r, paco11 gf r <11= fcpn11 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn11_final].
Qed.

Lemma cpn11_algebra r :
  r <11= gf r -> r <11= cpn11 bot11.
Proof.
  intros. apply cpn11_final. left.
  revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion11_main.

Lemma cbound11_bot gf:
  compatible_bound11 gf bot12.
Proof.
  econstructor; intros; contradiction.
Qed.

Lemma cpn11_mon_bot (gf gf': rel -> rel) bnd bnd' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 r
      (IN: @cpn11 gf bnd bot11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)
      (MON: monotone11 gf)
      (MON': monotone11 gf')
      (BASE: compatible_bound11 gf bnd)
      (BASE': compatible_bound11 gf' bnd')
      (LE: gf <12= gf'):
  @cpn11 gf' bnd' r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
Proof.
  apply cpn11_init in IN; [|apply MON|apply BASE].
  apply cpn11_final; [apply MON'|apply BASE'|].
  left. eapply paco11_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn11_mon_bot (gf gf': rel -> rel) bnd bnd' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 r
      (IN: @fcpn11 gf bnd bot11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)
      (MON: monotone11 gf)
      (MON': monotone11 gf')
      (BASE: compatible_bound11 gf bnd)
      (BASE': compatible_bound11 gf' bnd')
      (LE: gf <12= gf'):
  @fcpn11 gf' bnd' r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
Proof.
  apply LE. eapply MON. apply IN.
  intros. eapply cpn11_mon_bot; eassumption.
Qed.

End Companion11.

Hint Unfold fcpn11 : paco.
Hint Resolve cpn11_base : paco.
Hint Resolve cpn11_step : paco.
Hint Resolve cbound11_bot : paco.

Hint Constructors rclo11 : rclo.
Hint Resolve rclo11_clo rclo11_step rclo11_cpn : rclo.

