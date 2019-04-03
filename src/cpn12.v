Require Export Program.Basics. Open Scope program_scope.
Require Import paco12 pacotac.
Set Implicit Arguments.

Section Companion12.

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
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.

Local Notation rel := (rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11).

Section Companion12_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone12 gf.

(** 
  Bounded Compatibility, Companion & Guarded Companion
*)

Inductive pointwise_union (bnd: rel -> rel) (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : Prop :=
| pw_union_ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
            (IN: r d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11)
            (PTW: forall (s: rel), s d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 -> bnd s e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)
.

Structure compatible_bound12 (bnd: rel -> rel) : Prop :=
  cbound12_intro {
      cbound12_distr : forall r,
          bnd r <12= pointwise_union bnd r;
      cbound12_compat: forall r,
          bnd (gf r) <12= gf (bnd r);
      cbound12_bound: forall r,
          bnd (bnd r) <12= (bnd r \12/ gf (bnd r));
    }.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound12 bnd.

Structure compatible12 (clo: rel -> rel) : Prop :=
  compat12_intro {
      compat12_mon: monotone12 clo;
      compat12_compat : forall r,
          clo (gf r) <12= gf (clo r);
      compat12_bound : forall r,
          bnd (clo r) <12= (bnd r \12/ gf (clo r))
    }.

Inductive cpn12 (r: rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : Prop :=
| cpn12_intro
    clo
    (COM: compatible12 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)
.

Definition fcpn12 := compose gf cpn12.

Lemma cbound12_union r1 r2 : bnd (r1 \12/ r2) <12= (bnd r1 \12/ bnd r2).
Proof.
  intros. eapply cbound12_distr in PR; [|apply bnd_compat].
  destruct PR. destruct IN.
  - left. apply PTW, H.
  - right. apply PTW, H.
Qed.

Lemma cbound12_mon: monotone12 bnd.
Proof.
  repeat intro.
  apply (cbound12_distr bnd_compat) in IN.
  destruct IN.
  apply PTW, LE, IN.
Qed.

Lemma cpn12_mon: monotone12 cpn12.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat12_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn12_compat: compatible12 cpn12.
Proof.
  econstructor; [apply cpn12_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (compat12_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - eapply (cbound12_distr bnd_compat) in PR.
    destruct PR. destruct IN.
    specialize (PTW (clo r) CLO).
    apply (compat12_bound COM) in PTW.
    destruct PTW.
    + left. apply H.
    + right. eapply gf_mon; [apply H|].
      intros. econstructor;[apply COM|apply PR].
Qed.

Lemma cpn12_greatest: forall clo (COM: compatible12 clo), clo <13= cpn12.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn12_base: forall r, r <12= cpn12 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
    + left. apply PR0.
  - apply PR.
Qed.

Lemma cpn12_bound : forall r, bnd r <12= cpn12 r.
Proof.
  intros. exists bnd.
  - econstructor; repeat intro.
    + eapply cbound12_mon. apply IN. apply LE.
    + apply (cbound12_compat bnd_compat), PR0.
    + apply (cbound12_bound bnd_compat), PR0.
  - apply PR.
Qed.

Lemma cpn12_cpn: forall r,
    cpn12 (cpn12 r) <12= cpn12 r.
Proof.
  intros. exists (compose cpn12 cpn12); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn12_mon; [apply IN|].
    intros. eapply cpn12_mon; [apply PR0|apply LE].
  - intros. eapply (compat12_compat cpn12_compat).
    eapply cpn12_mon; [apply PR0|].
    intros. eapply (compat12_compat cpn12_compat), PR1.
  - intros. eapply (compat12_bound cpn12_compat) in PR0.
    destruct PR0; [|right; apply H].
    eapply (compat12_bound cpn12_compat) in H.
    destruct H; [left; apply H|].
    right. eapply gf_mon; [apply H|].
    intros. apply cpn12_base. apply PR0.
Qed.

Lemma fcpn12_mon: monotone12 fcpn12.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn12_mon; [apply PR|apply LE].
Qed.

Lemma fcpn12_sound:
  paco12 fcpn12 bot12 <12= paco12 gf bot12.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \12/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn12 n (paco12 fcpn12 bot12) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn12 n (paco12 fcpn12 bot12) <12= gf (rclo cpn12 (S n) (paco12 fcpn12 bot12))).
  { intro X. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply fcpn12_mon].
    + intros. right. eapply cpn12_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat12_compat cpn12_compat).
        eapply (compat12_mon cpn12_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo12 (clo: rel->rel) (r: rel): rel :=
| rclo12_base
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
    (R: r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11):
    @rclo12 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
| rclo12_clo'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
    (R': r' <12= rclo12 clo r)
    (CLOR': clo r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11):
    @rclo12 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
| rclo12_step'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
    (R': r' <12= rclo12 clo r)
    (CLOR': @gf r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11):
    @rclo12 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
| rclo12_cpn'
    r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
    (R': r' <12= rclo12 clo r)
    (CLOR': @cpn12 r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11):
    @rclo12 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
.

Structure wcompatible12 (clo: rel -> rel) : Prop :=
  wcompat12_intro {
      wcompat12_mon: monotone12 clo;
      wcompat12_wcompat: forall r,
          clo (gf r) <12= gf (rclo12 clo r);
      wcompat12_bound : forall r,
          bnd (clo r) <12= (bnd r \12/ gf (rclo12 clo r))
    }.

Lemma rclo12_mon_gen clo clo' r r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
      (IN: @rclo12 clo r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)
      (LEclo: clo <13= clo')
      (LEr: r <12= r') :
  @rclo12 clo' r' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn12_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo12_mon clo:
  monotone12 (rclo12 clo).
Proof.
  repeat intro. eapply rclo12_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo12_clo clo r:
  clo (rclo12 clo r) <12= rclo12 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo12_step clo r:
  gf (rclo12 clo r) <12= rclo12 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo12_cpn clo r:
  cpn12 (rclo12 clo r) <12= rclo12 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo12_mult clo r:
  rclo12 clo (rclo12 clo r) <12= rclo12 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo12_compose clo r:
  rclo12 (rclo12 clo) r <12= rclo12 clo r.
Proof.
  intros. induction PR.
  - apply rclo12_base, R.
  - apply rclo12_mult.
    eapply rclo12_mon; [apply CLOR'|apply H].
  - apply rclo12_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo12_cpn.
    eapply cpn12_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat12_compat
      clo (WCOM: wcompatible12 clo):
  compatible12 (rclo12 clo).
Proof.
  econstructor; [eapply rclo12_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo12_base. apply PR.
    + eapply gf_mon.
      * eapply (wcompat12_wcompat WCOM).
        eapply (wcompat12_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo12_mult, PR.
    + eapply gf_mon; [apply CLOR'|].
      intros. apply H in PR. apply rclo12_step, PR.
    + eapply gf_mon; [|intros; apply rclo12_cpn, PR].
      apply (compat12_compat cpn12_compat).
      eapply cpn12_mon; [apply CLOR'|apply H].
  - eapply (cbound12_distr bnd_compat) in PR.
    destruct PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 PTW.
    induction IN; intros.
    + left. apply PTW, R.
    + specialize (PTW _ CLOR').
      eapply (wcompat12_bound WCOM) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound12_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo12_mult.
        eapply rclo12_mon, R'. apply PR.
    + specialize (PTW _ CLOR').
      eapply (cbound12_compat bnd_compat) in PTW.
      right. eapply gf_mon. apply PTW. intros.
      eapply (cbound12_distr bnd_compat) in PR.
      destruct PR.
      eapply H in IN; [|apply PTW0].
      destruct IN.
      * apply rclo12_cpn, cpn12_bound.
        eapply cbound12_mon. apply H0. apply rclo12_base.
      * apply rclo12_step. apply H0.
    + specialize (PTW _ CLOR').
      apply (compat12_bound cpn12_compat) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound12_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo12_cpn.
        eapply cpn12_mon; [apply PR|].
        intros. apply R', PR0.
Qed.

Lemma wcompat12_sound clo (WCOM: wcompatible12 clo):
  clo <13= cpn12.
Proof.
  intros. exists (rclo12 clo).
  - apply wcompat12_compat, WCOM.
  - apply rclo12_clo.
    eapply (wcompat12_mon WCOM); [apply PR|].
    intros. apply rclo12_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn12_from_upaco r:
  upaco12 fcpn12 r <12= cpn12 r.
Proof.
  intros. destruct PR; [| apply cpn12_base, H].
  exists (rclo12 (paco12 fcpn12)).
  - apply wcompat12_compat.
    econstructor; [apply paco12_mon| |].
    + intros. _punfold PR; [|apply fcpn12_mon].
      eapply gf_mon; [apply PR|].
      intros. apply rclo12_cpn.
      eapply cpn12_mon; [apply PR0|].
      intros. destruct PR1.
      * apply rclo12_clo.
        eapply paco12_mon; [apply H0|].
        intros. apply rclo12_step.
        eapply gf_mon; [apply PR1|].
        intros. apply rclo12_base, PR2.
      * apply rclo12_step.
        eapply gf_mon; [apply H0|].
        intros. apply rclo12_base, PR1.
    + intros. right.
      eapply gf_mon, rclo12_cpn.
      eapply gf_mon, cpn12_bound.
      apply (cbound12_compat bnd_compat).
      eapply cbound12_mon. apply PR.
      intros. _punfold PR0; [|apply fcpn12_mon].
      eapply gf_mon. apply PR0.
      intros. apply rclo12_cpn.
      eapply cpn12_mon. apply PR1.
      intros. destruct PR2.
      * apply rclo12_clo.
        eapply paco12_mon. apply H0.
        intros. apply rclo12_base. apply PR2.
      * apply rclo12_base. apply H0.
  - apply rclo12_clo.
    eapply paco12_mon; [apply H|].
    intros. apply rclo12_base, PR.
Qed.

Lemma cpn12_from_paco r:
  paco12 fcpn12 r <12= cpn12 r.
Proof. intros. apply cpn12_from_upaco. left. apply PR. Qed.

Lemma fcpn12_from_paco r:
  paco12 fcpn12 r <12= fcpn12 r.
Proof.
  intros. _punfold PR; [|apply fcpn12_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn12_cpn.
  eapply cpn12_mon; [apply PR0|].
  apply cpn12_from_upaco.
Qed.

Lemma fcpn12_to_paco r:
  fcpn12 r <12= paco12 fcpn12 r.
Proof.
  intros. pfold. eapply fcpn12_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn12_complete:
  paco12 gf bot12 <12= cpn12 bot12.
Proof.
  intros. apply cpn12_from_paco.
  eapply paco12_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn12_base].
  - intros. apply PR0.
Qed.

Lemma cpn12_init:
  cpn12 bot12 <12= paco12 gf bot12.
Proof.
  intros. apply fcpn12_sound, fcpn12_to_paco, (compat12_compat cpn12_compat).
  eapply cpn12_mon; [apply PR|contradiction].
Qed.

Lemma cpn12_clo
      r clo (LE: clo <13= cpn12):
  clo (cpn12 r) <12= cpn12 r.
Proof.
  intros. apply cpn12_cpn, LE, PR.
Qed.

Lemma cpn12_unfold:
  cpn12 bot12 <12= fcpn12 bot12.
Proof.
  intros. apply cpn12_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn12_complete, PR0.
Qed.

Lemma cpn12_unfold_bound r
      (BASE: forall r, r <12= bnd r):
  cpn12 r <12= (bnd r \12/ fcpn12 r).
Proof.
  intros. apply BASE in PR.
  eapply compat12_bound in PR.
  - apply PR.
  - apply cpn12_compat.
Qed.

Lemma cpn12_step r:
  fcpn12 r <12= cpn12 r.
Proof.
  intros. eapply cpn12_clo, PR.
  intros. eapply wcompat12_sound, PR0.
  econstructor; [apply gf_mon| |].
  - intros. eapply gf_mon; [apply PR1|].
    intros. apply rclo12_step.
    eapply gf_mon; [apply PR2|].
    intros. apply rclo12_base, PR3.
  - intros. apply (cbound12_compat bnd_compat) in PR1.
    right. eapply gf_mon. apply PR1.
    intros. apply rclo12_cpn, cpn12_bound.
    eapply cbound12_mon. apply PR2.
    intros. apply rclo12_base, PR3.
Qed.

Lemma fcpn12_clo
      r clo (LE: clo <13= cpn12):
  clo (fcpn12 r) <12= fcpn12 r.
Proof.
  intros. apply LE, (compat12_compat cpn12_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn12_cpn, PR0.
Qed.

Lemma cpn12_final: forall r, upaco12 gf r <12= cpn12 r.
Proof.
  intros. eapply cpn12_from_upaco.
  intros. eapply upaco12_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn12_base, PR1.
Qed.

Lemma fcpn12_final: forall r, paco12 gf r <12= fcpn12 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn12_final].
Qed.

Lemma cpn12_algebra r :
  r <12= gf r -> r <12= cpn12 bot12.
Proof.
  intros. apply cpn12_final. left.
  revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion12_main.

Lemma cbound12_bot gf:
  compatible_bound12 gf bot13.
Proof.
  econstructor; intros; contradiction.
Qed.

Lemma cpn12_mon_bot (gf gf': rel -> rel) bnd bnd' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 r
      (IN: @cpn12 gf bnd bot12 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)
      (MON: monotone12 gf)
      (MON': monotone12 gf')
      (BASE: compatible_bound12 gf bnd)
      (BASE': compatible_bound12 gf' bnd')
      (LE: gf <13= gf'):
  @cpn12 gf' bnd' r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof.
  apply cpn12_init in IN; [|apply MON|apply BASE].
  apply cpn12_final; [apply MON'|apply BASE'|].
  left. eapply paco12_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn12_mon_bot (gf gf': rel -> rel) bnd bnd' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 r
      (IN: @fcpn12 gf bnd bot12 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)
      (MON: monotone12 gf)
      (MON': monotone12 gf')
      (BASE: compatible_bound12 gf bnd)
      (BASE': compatible_bound12 gf' bnd')
      (LE: gf <13= gf'):
  @fcpn12 gf' bnd' r e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof.
  apply LE. eapply MON. apply IN.
  intros. eapply cpn12_mon_bot; eassumption.
Qed.

End Companion12.

Hint Unfold fcpn12 : paco.
Hint Resolve cpn12_base : paco.
Hint Resolve cpn12_step : paco.
Hint Resolve cbound12_bot : paco.

Hint Constructors rclo12 : rclo.
Hint Resolve rclo12_clo rclo12_step rclo12_cpn : rclo.

