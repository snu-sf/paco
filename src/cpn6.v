Require Export Program.Basics. Open Scope program_scope.
Require Import paco6 pacotac.
Set Implicit Arguments.

Section Companion6.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.

Local Notation rel := (rel6 T0 T1 T2 T3 T4 T5).

Section Companion6_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone6 gf.

(** 
  Bounded Compatibility, Companion & Guarded Companion
*)

Inductive pointwise_union (bnd: rel -> rel) (r: rel) e0 e1 e2 e3 e4 e5 : Prop :=
| pw_union_ d0 d1 d2 d3 d4 d5
            (IN: r d0 d1 d2 d3 d4 d5)
            (PTW: forall (s: rel), s d0 d1 d2 d3 d4 d5 -> bnd s e0 e1 e2 e3 e4 e5)
.

Structure compatible_bound6 (bnd: rel -> rel) : Prop :=
  cbound6_intro {
      cbound6_distr : forall r,
          bnd r <6= pointwise_union bnd r;
      cbound6_compat: forall r,
          bnd (gf r) <6= gf (bnd r);
      cbound6_bound: forall r,
          bnd (bnd r) <6= (bnd r \6/ gf (bnd r));
    }.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound6 bnd.

Structure compatible6 (clo: rel -> rel) : Prop :=
  compat6_intro {
      compat6_mon: monotone6 clo;
      compat6_compat : forall r,
          clo (gf r) <6= gf (clo r);
      compat6_bound : forall r,
          bnd (clo r) <6= (bnd r \6/ gf (clo r))
    }.

Inductive cpn6 (r: rel) e0 e1 e2 e3 e4 e5 : Prop :=
| cpn6_intro
    clo
    (COM: compatible6 clo)
    (CLO: clo r e0 e1 e2 e3 e4 e5)
.

Definition fcpn6 := compose gf cpn6.

Lemma cbound6_union r1 r2 : bnd (r1 \6/ r2) <6= (bnd r1 \6/ bnd r2).
Proof.
  intros. eapply cbound6_distr in PR; [|apply bnd_compat].
  destruct PR. destruct IN.
  - left. apply PTW, H.
  - right. apply PTW, H.
Qed.

Lemma cbound6_mon: monotone6 bnd.
Proof.
  repeat intro.
  apply (cbound6_distr bnd_compat) in IN.
  destruct IN.
  apply PTW, LE, IN.
Qed.

Lemma cpn6_mon: monotone6 cpn6.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat6_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn6_compat: compatible6 cpn6.
Proof.
  econstructor; [apply cpn6_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (compat6_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - eapply (cbound6_distr bnd_compat) in PR.
    destruct PR. destruct IN.
    specialize (PTW (clo r) CLO).
    apply (compat6_bound COM) in PTW.
    destruct PTW.
    + left. apply H.
    + right. eapply gf_mon; [apply H|].
      intros. econstructor;[apply COM|apply PR].
Qed.

Lemma cpn6_greatest: forall clo (COM: compatible6 clo), clo <7= cpn6.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn6_base: forall r, r <6= cpn6 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
    + left. apply PR0.
  - apply PR.
Qed.

Lemma cpn6_bound : forall r, bnd r <6= cpn6 r.
Proof.
  intros. exists bnd.
  - econstructor; repeat intro.
    + eapply cbound6_mon. apply IN. apply LE.
    + apply (cbound6_compat bnd_compat), PR0.
    + apply (cbound6_bound bnd_compat), PR0.
  - apply PR.
Qed.

Lemma cpn6_cpn: forall r,
    cpn6 (cpn6 r) <6= cpn6 r.
Proof.
  intros. exists (compose cpn6 cpn6); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn6_mon; [apply IN|].
    intros. eapply cpn6_mon; [apply PR0|apply LE].
  - intros. eapply (compat6_compat cpn6_compat).
    eapply cpn6_mon; [apply PR0|].
    intros. eapply (compat6_compat cpn6_compat), PR1.
  - intros. eapply (compat6_bound cpn6_compat) in PR0.
    destruct PR0; [|right; apply H].
    eapply (compat6_bound cpn6_compat) in H.
    destruct H; [left; apply H|].
    right. eapply gf_mon; [apply H|].
    intros. apply cpn6_base. apply PR0.
Qed.

Lemma fcpn6_mon: monotone6 fcpn6.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn6_mon; [apply PR|apply LE].
Qed.

Lemma fcpn6_sound:
  paco6 fcpn6 bot6 <6= paco6 gf bot6.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \6/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn6 n (paco6 fcpn6 bot6) x0 x1 x2 x3 x4 x5) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn6 n (paco6 fcpn6 bot6) <6= gf (rclo cpn6 (S n) (paco6 fcpn6 bot6))).
  { intro X. revert x0 x1 x2 x3 x4 x5 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply fcpn6_mon].
    + intros. right. eapply cpn6_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat6_compat cpn6_compat).
        eapply (compat6_mon cpn6_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo6 (clo: rel->rel) (r: rel): rel :=
| rclo6_base
    e0 e1 e2 e3 e4 e5
    (R: r e0 e1 e2 e3 e4 e5):
    @rclo6 clo r e0 e1 e2 e3 e4 e5
| rclo6_clo'
    r' e0 e1 e2 e3 e4 e5
    (R': r' <6= rclo6 clo r)
    (CLOR': clo r' e0 e1 e2 e3 e4 e5):
    @rclo6 clo r e0 e1 e2 e3 e4 e5
| rclo6_step'
    r' e0 e1 e2 e3 e4 e5
    (R': r' <6= rclo6 clo r)
    (CLOR': @gf r' e0 e1 e2 e3 e4 e5):
    @rclo6 clo r e0 e1 e2 e3 e4 e5
| rclo6_cpn'
    r' e0 e1 e2 e3 e4 e5
    (R': r' <6= rclo6 clo r)
    (CLOR': @cpn6 r' e0 e1 e2 e3 e4 e5):
    @rclo6 clo r e0 e1 e2 e3 e4 e5
.

Structure wcompatible6 (clo: rel -> rel) : Prop :=
  wcompat6_intro {
      wcompat6_mon: monotone6 clo;
      wcompat6_wcompat: forall r,
          clo (gf r) <6= gf (rclo6 clo r);
      wcompat6_bound : forall r,
          bnd (clo r) <6= (bnd r \6/ gf (rclo6 clo r))
    }.

Lemma rclo6_mon_gen clo clo' r r' e0 e1 e2 e3 e4 e5
      (IN: @rclo6 clo r e0 e1 e2 e3 e4 e5)
      (LEclo: clo <7= clo')
      (LEr: r <6= r') :
  @rclo6 clo' r' e0 e1 e2 e3 e4 e5.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn6_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo6_mon clo:
  monotone6 (rclo6 clo).
Proof.
  repeat intro. eapply rclo6_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo6_clo clo r:
  clo (rclo6 clo r) <6= rclo6 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo6_step clo r:
  gf (rclo6 clo r) <6= rclo6 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo6_cpn clo r:
  cpn6 (rclo6 clo r) <6= rclo6 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo6_mult clo r:
  rclo6 clo (rclo6 clo r) <6= rclo6 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo6_compose clo r:
  rclo6 (rclo6 clo) r <6= rclo6 clo r.
Proof.
  intros. induction PR.
  - apply rclo6_base, R.
  - apply rclo6_mult.
    eapply rclo6_mon; [apply CLOR'|apply H].
  - apply rclo6_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo6_cpn.
    eapply cpn6_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat6_compat
      clo (WCOM: wcompatible6 clo):
  compatible6 (rclo6 clo).
Proof.
  econstructor; [eapply rclo6_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo6_base. apply PR.
    + eapply gf_mon.
      * eapply (wcompat6_wcompat WCOM).
        eapply (wcompat6_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo6_mult, PR.
    + eapply gf_mon; [apply CLOR'|].
      intros. apply H in PR. apply rclo6_step, PR.
    + eapply gf_mon; [|intros; apply rclo6_cpn, PR].
      apply (compat6_compat cpn6_compat).
      eapply cpn6_mon; [apply CLOR'|apply H].
  - eapply (cbound6_distr bnd_compat) in PR.
    destruct PR. revert x0 x1 x2 x3 x4 x5 PTW.
    induction IN; intros.
    + left. apply PTW, R.
    + specialize (PTW _ CLOR').
      eapply (wcompat6_bound WCOM) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound6_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo6_mult.
        eapply rclo6_mon, R'. apply PR.
    + specialize (PTW _ CLOR').
      eapply (cbound6_compat bnd_compat) in PTW.
      right. eapply gf_mon. apply PTW. intros.
      eapply (cbound6_distr bnd_compat) in PR.
      destruct PR.
      eapply H in IN; [|apply PTW0].
      destruct IN.
      * apply rclo6_cpn, cpn6_bound.
        eapply cbound6_mon. apply H0. apply rclo6_base.
      * apply rclo6_step. apply H0.
    + specialize (PTW _ CLOR').
      apply (compat6_bound cpn6_compat) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound6_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo6_cpn.
        eapply cpn6_mon; [apply PR|].
        intros. apply R', PR0.
Qed.

Lemma wcompat6_sound clo (WCOM: wcompatible6 clo):
  clo <7= cpn6.
Proof.
  intros. exists (rclo6 clo).
  - apply wcompat6_compat, WCOM.
  - apply rclo6_clo.
    eapply (wcompat6_mon WCOM); [apply PR|].
    intros. apply rclo6_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn6_from_upaco r:
  upaco6 fcpn6 r <6= cpn6 r.
Proof.
  intros. destruct PR; [| apply cpn6_base, H].
  exists (rclo6 (paco6 fcpn6)).
  - apply wcompat6_compat.
    econstructor; [apply paco6_mon| |].
    + intros. _punfold PR; [|apply fcpn6_mon].
      eapply gf_mon; [apply PR|].
      intros. apply rclo6_cpn.
      eapply cpn6_mon; [apply PR0|].
      intros. destruct PR1.
      * apply rclo6_clo.
        eapply paco6_mon; [apply H0|].
        intros. apply rclo6_step.
        eapply gf_mon; [apply PR1|].
        intros. apply rclo6_base, PR2.
      * apply rclo6_step.
        eapply gf_mon; [apply H0|].
        intros. apply rclo6_base, PR1.
    + intros. right.
      eapply gf_mon, rclo6_cpn.
      eapply gf_mon, cpn6_bound.
      apply (cbound6_compat bnd_compat).
      eapply cbound6_mon. apply PR.
      intros. _punfold PR0; [|apply fcpn6_mon].
      eapply gf_mon. apply PR0.
      intros. apply rclo6_cpn.
      eapply cpn6_mon. apply PR1.
      intros. destruct PR2.
      * apply rclo6_clo.
        eapply paco6_mon. apply H0.
        intros. apply rclo6_base. apply PR2.
      * apply rclo6_base. apply H0.
  - apply rclo6_clo.
    eapply paco6_mon; [apply H|].
    intros. apply rclo6_base, PR.
Qed.

Lemma cpn6_from_paco r:
  paco6 fcpn6 r <6= cpn6 r.
Proof. intros. apply cpn6_from_upaco. left. apply PR. Qed.

Lemma fcpn6_from_paco r:
  paco6 fcpn6 r <6= fcpn6 r.
Proof.
  intros. _punfold PR; [|apply fcpn6_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn6_cpn.
  eapply cpn6_mon; [apply PR0|].
  apply cpn6_from_upaco.
Qed.

Lemma fcpn6_to_paco r:
  fcpn6 r <6= paco6 fcpn6 r.
Proof.
  intros. pfold. eapply fcpn6_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn6_complete:
  paco6 gf bot6 <6= cpn6 bot6.
Proof.
  intros. apply cpn6_from_paco.
  eapply paco6_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn6_base].
  - intros. apply PR0.
Qed.

Lemma cpn6_init:
  cpn6 bot6 <6= paco6 gf bot6.
Proof.
  intros. apply fcpn6_sound, fcpn6_to_paco, (compat6_compat cpn6_compat).
  eapply cpn6_mon; [apply PR|contradiction].
Qed.

Lemma cpn6_clo
      r clo (LE: clo <7= cpn6):
  clo (cpn6 r) <6= cpn6 r.
Proof.
  intros. apply cpn6_cpn, LE, PR.
Qed.

Lemma cpn6_unfold:
  cpn6 bot6 <6= fcpn6 bot6.
Proof.
  intros. apply cpn6_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn6_complete, PR0.
Qed.

Lemma cpn6_unfold_bound r
      (BASE: forall r, r <6= bnd r):
  cpn6 r <6= (bnd r \6/ fcpn6 r).
Proof.
  intros. apply BASE in PR.
  eapply compat6_bound in PR.
  - apply PR.
  - apply cpn6_compat.
Qed.

Lemma cpn6_step r:
  fcpn6 r <6= cpn6 r.
Proof.
  intros. eapply cpn6_clo, PR.
  intros. eapply wcompat6_sound, PR0.
  econstructor; [apply gf_mon| |].
  - intros. eapply gf_mon; [apply PR1|].
    intros. apply rclo6_step.
    eapply gf_mon; [apply PR2|].
    intros. apply rclo6_base, PR3.
  - intros. apply (cbound6_compat bnd_compat) in PR1.
    right. eapply gf_mon. apply PR1.
    intros. apply rclo6_cpn, cpn6_bound.
    eapply cbound6_mon. apply PR2.
    intros. apply rclo6_base, PR3.
Qed.

Lemma fcpn6_clo
      r clo (LE: clo <7= cpn6):
  clo (fcpn6 r) <6= fcpn6 r.
Proof.
  intros. apply LE, (compat6_compat cpn6_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn6_cpn, PR0.
Qed.

Lemma cpn6_final: forall r, upaco6 gf r <6= cpn6 r.
Proof.
  intros. eapply cpn6_from_upaco.
  intros. eapply upaco6_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn6_base, PR1.
Qed.

Lemma fcpn6_final: forall r, paco6 gf r <6= fcpn6 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn6_final].
Qed.

Lemma cpn6_algebra r :
  r <6= gf r -> r <6= cpn6 bot6.
Proof.
  intros. apply cpn6_final. left.
  revert x0 x1 x2 x3 x4 x5 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion6_main.

Lemma cbound6_bot gf:
  compatible_bound6 gf bot7.
Proof.
  econstructor; intros; contradiction.
Qed.

Lemma cpn6_mon_bot (gf gf': rel -> rel) bnd bnd' e0 e1 e2 e3 e4 e5 r
      (IN: @cpn6 gf bnd bot6 e0 e1 e2 e3 e4 e5)
      (MON: monotone6 gf)
      (MON': monotone6 gf')
      (BASE: compatible_bound6 gf bnd)
      (BASE': compatible_bound6 gf' bnd')
      (LE: gf <7= gf'):
  @cpn6 gf' bnd' r e0 e1 e2 e3 e4 e5.
Proof.
  apply cpn6_init in IN; [|apply MON|apply BASE].
  apply cpn6_final; [apply MON'|apply BASE'|].
  left. eapply paco6_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn6_mon_bot (gf gf': rel -> rel) bnd bnd' e0 e1 e2 e3 e4 e5 r
      (IN: @fcpn6 gf bnd bot6 e0 e1 e2 e3 e4 e5)
      (MON: monotone6 gf)
      (MON': monotone6 gf')
      (BASE: compatible_bound6 gf bnd)
      (BASE': compatible_bound6 gf' bnd')
      (LE: gf <7= gf'):
  @fcpn6 gf' bnd' r e0 e1 e2 e3 e4 e5.
Proof.
  apply LE. eapply MON. apply IN.
  intros. eapply cpn6_mon_bot; eassumption.
Qed.

End Companion6.

Hint Unfold fcpn6 : paco.
Hint Resolve cpn6_base : paco.
Hint Resolve cpn6_step : paco.
Hint Resolve cbound6_bot : paco.

Hint Constructors rclo6 : rclo.
Hint Resolve rclo6_clo rclo6_step rclo6_cpn : rclo.

