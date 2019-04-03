Require Export Program.Basics. Open Scope program_scope.
Require Import paco7 pacotac.
Set Implicit Arguments.

Section Companion7.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.

Local Notation rel := (rel7 T0 T1 T2 T3 T4 T5 T6).

Section Companion7_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone7 gf.

(** 
  Bounded Compatibility, Companion & Guarded Companion
*)

Inductive pointwise_union (bnd: rel -> rel) (r: rel) e0 e1 e2 e3 e4 e5 e6 : Prop :=
| pw_union_ d0 d1 d2 d3 d4 d5 d6
            (IN: r d0 d1 d2 d3 d4 d5 d6)
            (PTW: forall (s: rel), s d0 d1 d2 d3 d4 d5 d6 -> bnd s e0 e1 e2 e3 e4 e5 e6)
.

Structure compatible_bound7 (bnd: rel -> rel) : Prop :=
  cbound7_intro {
      cbound7_distr : forall r,
          bnd r <7= pointwise_union bnd r;
      cbound7_compat: forall r,
          bnd (gf r) <7= gf (bnd r);
      cbound7_bound: forall r,
          bnd (bnd r) <7= (bnd r \7/ gf (bnd r));
    }.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound7 bnd.

Structure compatible7 (clo: rel -> rel) : Prop :=
  compat7_intro {
      compat7_mon: monotone7 clo;
      compat7_compat : forall r,
          clo (gf r) <7= gf (clo r);
      compat7_bound : forall r,
          bnd (clo r) <7= (bnd r \7/ gf (clo r))
    }.

Inductive cpn7 (r: rel) e0 e1 e2 e3 e4 e5 e6 : Prop :=
| cpn7_intro
    clo
    (COM: compatible7 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5 e6)
.

Definition fcpn7 := compose gf cpn7.

Lemma cbound7_union r1 r2 : bnd (r1 \7/ r2) <7= (bnd r1 \7/ bnd r2).
Proof.
  intros. eapply cbound7_distr in PR; [|apply bnd_compat].
  destruct PR. destruct IN.
  - left. apply PTW, H.
  - right. apply PTW, H.
Qed.

Lemma cbound7_mon: monotone7 bnd.
Proof.
  repeat intro.
  apply (cbound7_distr bnd_compat) in IN.
  destruct IN.
  apply PTW, LE, IN.
Qed.

Lemma cpn7_mon: monotone7 cpn7.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat7_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn7_compat: compatible7 cpn7.
Proof.
  econstructor; [apply cpn7_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (compat7_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - eapply (cbound7_distr bnd_compat) in PR.
    destruct PR. destruct IN.
    specialize (PTW (clo r) CLO).
    apply (compat7_bound COM) in PTW.
    destruct PTW.
    + left. apply H.
    + right. eapply gf_mon; [apply H|].
      intros. econstructor;[apply COM|apply PR].
Qed.

Lemma cpn7_greatest: forall clo (COM: compatible7 clo), clo <8= cpn7.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn7_base: forall r, r <7= cpn7 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
    + left. apply PR0.
  - apply PR.
Qed.

Lemma cpn7_bound : forall r, bnd r <7= cpn7 r.
Proof.
  intros. exists bnd.
  - econstructor; repeat intro.
    + eapply cbound7_mon. apply IN. apply LE.
    + apply (cbound7_compat bnd_compat), PR0.
    + apply (cbound7_bound bnd_compat), PR0.
  - apply PR.
Qed.

Lemma cpn7_cpn: forall r,
    cpn7 (cpn7 r) <7= cpn7 r.
Proof.
  intros. exists (compose cpn7 cpn7); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn7_mon; [apply IN|].
    intros. eapply cpn7_mon; [apply PR0|apply LE].
  - intros. eapply (compat7_compat cpn7_compat).
    eapply cpn7_mon; [apply PR0|].
    intros. eapply (compat7_compat cpn7_compat), PR1.
  - intros. eapply (compat7_bound cpn7_compat) in PR0.
    destruct PR0; [|right; apply H].
    eapply (compat7_bound cpn7_compat) in H.
    destruct H; [left; apply H|].
    right. eapply gf_mon; [apply H|].
    intros. apply cpn7_base. apply PR0.
Qed.

Lemma fcpn7_mon: monotone7 fcpn7.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn7_mon; [apply PR|apply LE].
Qed.

Lemma fcpn7_sound:
  paco7 fcpn7 bot7 <7= paco7 gf bot7.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \7/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn7 n (paco7 fcpn7 bot7) x0 x1 x2 x3 x4 x5 x6) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn7 n (paco7 fcpn7 bot7) <7= gf (rclo cpn7 (S n) (paco7 fcpn7 bot7))).
  { intro X. revert x0 x1 x2 x3 x4 x5 x6 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply fcpn7_mon].
    + intros. right. eapply cpn7_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat7_compat cpn7_compat).
        eapply (compat7_mon cpn7_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo7 (clo: rel->rel) (r: rel): rel :=
| rclo7_base
    e0 e1 e2 e3 e4 e5 e6
    (R: r e0 e1 e2 e3 e4 e5 e6):
    @rclo7 clo r e0 e1 e2 e3 e4 e5 e6
| rclo7_clo'
    r' e0 e1 e2 e3 e4 e5 e6
    (R': r' <7= rclo7 clo r)
    (CLOR': clo r' e0 e1 e2 e3 e4 e5 e6):
    @rclo7 clo r e0 e1 e2 e3 e4 e5 e6
| rclo7_step'
    r' e0 e1 e2 e3 e4 e5 e6
    (R': r' <7= rclo7 clo r)
    (CLOR': @gf r' e0 e1 e2 e3 e4 e5 e6):
    @rclo7 clo r e0 e1 e2 e3 e4 e5 e6
| rclo7_cpn'
    r' e0 e1 e2 e3 e4 e5 e6
    (R': r' <7= rclo7 clo r)
    (CLOR': @cpn7 r' e0 e1 e2 e3 e4 e5 e6):
    @rclo7 clo r e0 e1 e2 e3 e4 e5 e6
.

Structure wcompatible7 (clo: rel -> rel) : Prop :=
  wcompat7_intro {
      wcompat7_mon: monotone7 clo;
      wcompat7_wcompat: forall r,
          clo (gf r) <7= gf (rclo7 clo r);
      wcompat7_bound : forall r,
          bnd (clo r) <7= (bnd r \7/ gf (rclo7 clo r))
    }.

Lemma rclo7_mon_gen clo clo' r r' e0 e1 e2 e3 e4 e5 e6
      (IN: @rclo7 clo r e0 e1 e2 e3 e4 e5 e6)
      (LEclo: clo <8= clo')
      (LEr: r <7= r') :
  @rclo7 clo' r' e0 e1 e2 e3 e4 e5 e6.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn7_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo7_mon clo:
  monotone7 (rclo7 clo).
Proof.
  repeat intro. eapply rclo7_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo7_clo clo r:
  clo (rclo7 clo r) <7= rclo7 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo7_step clo r:
  gf (rclo7 clo r) <7= rclo7 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo7_cpn clo r:
  cpn7 (rclo7 clo r) <7= rclo7 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo7_mult clo r:
  rclo7 clo (rclo7 clo r) <7= rclo7 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo7_compose clo r:
  rclo7 (rclo7 clo) r <7= rclo7 clo r.
Proof.
  intros. induction PR.
  - apply rclo7_base, R.
  - apply rclo7_mult.
    eapply rclo7_mon; [apply CLOR'|apply H].
  - apply rclo7_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo7_cpn.
    eapply cpn7_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat7_compat
      clo (WCOM: wcompatible7 clo):
  compatible7 (rclo7 clo).
Proof.
  econstructor; [eapply rclo7_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo7_base. apply PR.
    + eapply gf_mon.
      * eapply (wcompat7_wcompat WCOM).
        eapply (wcompat7_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo7_mult, PR.
    + eapply gf_mon; [apply CLOR'|].
      intros. apply H in PR. apply rclo7_step, PR.
    + eapply gf_mon; [|intros; apply rclo7_cpn, PR].
      apply (compat7_compat cpn7_compat).
      eapply cpn7_mon; [apply CLOR'|apply H].
  - eapply (cbound7_distr bnd_compat) in PR.
    destruct PR. revert x0 x1 x2 x3 x4 x5 x6 PTW.
    induction IN; intros.
    + left. apply PTW, R.
    + specialize (PTW _ CLOR').
      eapply (wcompat7_bound WCOM) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound7_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo7_mult.
        eapply rclo7_mon, R'. apply PR.
    + specialize (PTW _ CLOR').
      eapply (cbound7_compat bnd_compat) in PTW.
      right. eapply gf_mon. apply PTW. intros.
      eapply (cbound7_distr bnd_compat) in PR.
      destruct PR.
      eapply H in IN; [|apply PTW0].
      destruct IN.
      * apply rclo7_cpn, cpn7_bound.
        eapply cbound7_mon. apply H0. apply rclo7_base.
      * apply rclo7_step. apply H0.
    + specialize (PTW _ CLOR').
      apply (compat7_bound cpn7_compat) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound7_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo7_cpn.
        eapply cpn7_mon; [apply PR|].
        intros. apply R', PR0.
Qed.

Lemma wcompat7_sound clo (WCOM: wcompatible7 clo):
  clo <8= cpn7.
Proof.
  intros. exists (rclo7 clo).
  - apply wcompat7_compat, WCOM.
  - apply rclo7_clo.
    eapply (wcompat7_mon WCOM); [apply PR|].
    intros. apply rclo7_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn7_from_upaco r:
  upaco7 fcpn7 r <7= cpn7 r.
Proof.
  intros. destruct PR; [| apply cpn7_base, H].
  exists (rclo7 (paco7 fcpn7)).
  - apply wcompat7_compat.
    econstructor; [apply paco7_mon| |].
    + intros. _punfold PR; [|apply fcpn7_mon].
      eapply gf_mon; [apply PR|].
      intros. apply rclo7_cpn.
      eapply cpn7_mon; [apply PR0|].
      intros. destruct PR1.
      * apply rclo7_clo.
        eapply paco7_mon; [apply H0|].
        intros. apply rclo7_step.
        eapply gf_mon; [apply PR1|].
        intros. apply rclo7_base, PR2.
      * apply rclo7_step.
        eapply gf_mon; [apply H0|].
        intros. apply rclo7_base, PR1.
    + intros. right.
      eapply gf_mon, rclo7_cpn.
      eapply gf_mon, cpn7_bound.
      apply (cbound7_compat bnd_compat).
      eapply cbound7_mon. apply PR.
      intros. _punfold PR0; [|apply fcpn7_mon].
      eapply gf_mon. apply PR0.
      intros. apply rclo7_cpn.
      eapply cpn7_mon. apply PR1.
      intros. destruct PR2.
      * apply rclo7_clo.
        eapply paco7_mon. apply H0.
        intros. apply rclo7_base. apply PR2.
      * apply rclo7_base. apply H0.
  - apply rclo7_clo.
    eapply paco7_mon; [apply H|].
    intros. apply rclo7_base, PR.
Qed.

Lemma cpn7_from_paco r:
  paco7 fcpn7 r <7= cpn7 r.
Proof. intros. apply cpn7_from_upaco. left. apply PR. Qed.

Lemma fcpn7_from_paco r:
  paco7 fcpn7 r <7= fcpn7 r.
Proof.
  intros. _punfold PR; [|apply fcpn7_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn7_cpn.
  eapply cpn7_mon; [apply PR0|].
  apply cpn7_from_upaco.
Qed.

Lemma fcpn7_to_paco r:
  fcpn7 r <7= paco7 fcpn7 r.
Proof.
  intros. pfold. eapply fcpn7_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn7_complete:
  paco7 gf bot7 <7= cpn7 bot7.
Proof.
  intros. apply cpn7_from_paco.
  eapply paco7_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn7_base].
  - intros. apply PR0.
Qed.

Lemma cpn7_init:
  cpn7 bot7 <7= paco7 gf bot7.
Proof.
  intros. apply fcpn7_sound, fcpn7_to_paco, (compat7_compat cpn7_compat).
  eapply cpn7_mon; [apply PR|contradiction].
Qed.

Lemma cpn7_clo
      r clo (LE: clo <8= cpn7):
  clo (cpn7 r) <7= cpn7 r.
Proof.
  intros. apply cpn7_cpn, LE, PR.
Qed.

Lemma cpn7_unfold:
  cpn7 bot7 <7= fcpn7 bot7.
Proof.
  intros. apply cpn7_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn7_complete, PR0.
Qed.

Lemma cpn7_unfold_bound r
      (BASE: forall r, r <7= bnd r):
  cpn7 r <7= (bnd r \7/ fcpn7 r).
Proof.
  intros. apply BASE in PR.
  eapply compat7_bound in PR.
  - apply PR.
  - apply cpn7_compat.
Qed.

Lemma cpn7_step r:
  fcpn7 r <7= cpn7 r.
Proof.
  intros. eapply cpn7_clo, PR.
  intros. eapply wcompat7_sound, PR0.
  econstructor; [apply gf_mon| |].
  - intros. eapply gf_mon; [apply PR1|].
    intros. apply rclo7_step.
    eapply gf_mon; [apply PR2|].
    intros. apply rclo7_base, PR3.
  - intros. apply (cbound7_compat bnd_compat) in PR1.
    right. eapply gf_mon. apply PR1.
    intros. apply rclo7_cpn, cpn7_bound.
    eapply cbound7_mon. apply PR2.
    intros. apply rclo7_base, PR3.
Qed.

Lemma fcpn7_clo
      r clo (LE: clo <8= cpn7):
  clo (fcpn7 r) <7= fcpn7 r.
Proof.
  intros. apply LE, (compat7_compat cpn7_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn7_cpn, PR0.
Qed.

Lemma cpn7_final: forall r, upaco7 gf r <7= cpn7 r.
Proof.
  intros. eapply cpn7_from_upaco.
  intros. eapply upaco7_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn7_base, PR1.
Qed.

Lemma fcpn7_final: forall r, paco7 gf r <7= fcpn7 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn7_final].
Qed.

Lemma cpn7_algebra r :
  r <7= gf r -> r <7= cpn7 bot7.
Proof.
  intros. apply cpn7_final. left.
  revert x0 x1 x2 x3 x4 x5 x6 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion7_main.

Lemma cbound7_bot gf:
  compatible_bound7 gf bot8.
Proof.
  econstructor; intros; contradiction.
Qed.

Lemma cpn7_mon_bot (gf gf': rel -> rel) bnd bnd' e0 e1 e2 e3 e4 e5 e6 r
      (IN: @cpn7 gf bnd bot7 e0 e1 e2 e3 e4 e5 e6)
      (MON: monotone7 gf)
      (MON': monotone7 gf')
      (BASE: compatible_bound7 gf bnd)
      (BASE': compatible_bound7 gf' bnd')
      (LE: gf <8= gf'):
  @cpn7 gf' bnd' r e0 e1 e2 e3 e4 e5 e6.
Proof.
  apply cpn7_init in IN; [|apply MON|apply BASE].
  apply cpn7_final; [apply MON'|apply BASE'|].
  left. eapply paco7_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn7_mon_bot (gf gf': rel -> rel) bnd bnd' e0 e1 e2 e3 e4 e5 e6 r
      (IN: @fcpn7 gf bnd bot7 e0 e1 e2 e3 e4 e5 e6)
      (MON: monotone7 gf)
      (MON': monotone7 gf')
      (BASE: compatible_bound7 gf bnd)
      (BASE': compatible_bound7 gf' bnd')
      (LE: gf <8= gf'):
  @fcpn7 gf' bnd' r e0 e1 e2 e3 e4 e5 e6.
Proof.
  apply LE. eapply MON. apply IN.
  intros. eapply cpn7_mon_bot; eassumption.
Qed.

End Companion7.

Hint Unfold fcpn7 : paco.
Hint Resolve cpn7_base : paco.
Hint Resolve cpn7_step : paco.
Hint Resolve cbound7_bot : paco.

Hint Constructors rclo7 : rclo.
Hint Resolve rclo7_clo rclo7_step rclo7_cpn : rclo.

