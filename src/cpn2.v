Require Export Program.Basics. Open Scope program_scope.
Require Import paco2 pacotac.
Set Implicit Arguments.

Section Companion2.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.

Local Notation rel := (rel2 T0 T1).

Section Companion2_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone2 gf.

(** 
  Bounded Compatibility, Companion & Guarded Companion
*)

Inductive pointwise_union (bnd: rel -> rel) (r: rel) e0 e1 : Prop :=
| pw_union_ d0 d1
            (IN: r d0 d1)
            (PTW: forall (s: rel), s d0 d1 -> bnd s e0 e1)
.

Structure compatible_bound2 (bnd: rel -> rel) : Prop :=
  cbound2_intro {
      cbound2_distr : forall r,
          bnd r <2= pointwise_union bnd r;
      cbound2_compat: forall r,
          bnd (gf r) <2= gf (bnd r);
      cbound2_bound: forall r,
          bnd (bnd r) <2= (bnd r \2/ gf (bnd r));
    }.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound2 bnd.

Structure compatible2 (clo: rel -> rel) : Prop :=
  compat2_intro {
      compat2_mon: monotone2 clo;
      compat2_compat : forall r,
          clo (gf r) <2= gf (clo r);
      compat2_bound : forall r,
          bnd (clo r) <2= (bnd r \2/ gf (clo r))
    }.

Inductive cpn2 (r: rel) e0 e1 : Prop :=
| cpn2_intro
    clo
    (COM: compatible2 clo)
    (CLO: clo r e0 e1)
.

Definition fcpn2 := compose gf cpn2.

Lemma cbound2_union r1 r2 : bnd (r1 \2/ r2) <2= (bnd r1 \2/ bnd r2).
Proof.
  intros. eapply cbound2_distr in PR; [|apply bnd_compat].
  destruct PR. destruct IN.
  - left. apply PTW, H.
  - right. apply PTW, H.
Qed.

Lemma cbound2_mon: monotone2 bnd.
Proof.
  repeat intro.
  apply (cbound2_distr bnd_compat) in IN.
  destruct IN.
  apply PTW, LE, IN.
Qed.

Lemma cpn2_mon: monotone2 cpn2.
Proof.
  red. intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply compat2_mon; [apply COM|apply CLO|apply LE].
Qed.

Lemma cpn2_compat: compatible2 cpn2.
Proof.
  econstructor; [apply cpn2_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (compat2_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - eapply (cbound2_distr bnd_compat) in PR.
    destruct PR. destruct IN.
    specialize (PTW (clo r) CLO).
    apply (compat2_bound COM) in PTW.
    destruct PTW.
    + left. apply H.
    + right. eapply gf_mon; [apply H|].
      intros. econstructor;[apply COM|apply PR].
Qed.

Lemma cpn2_greatest: forall clo (COM: compatible2 clo), clo <3= cpn2.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn2_base: forall r, r <2= cpn2 r.
Proof.
  intros. exists id.
  - econstructor; repeat intro.
    + apply LE, IN.
    + apply PR0.
    + left. apply PR0.
  - apply PR.
Qed.

Lemma cpn2_bound : forall r, bnd r <2= cpn2 r.
Proof.
  intros. exists bnd.
  - econstructor; repeat intro.
    + eapply cbound2_mon. apply IN. apply LE.
    + apply (cbound2_compat bnd_compat), PR0.
    + apply (cbound2_bound bnd_compat), PR0.
  - apply PR.
Qed.

Lemma cpn2_cpn: forall r,
    cpn2 (cpn2 r) <2= cpn2 r.
Proof.
  intros. exists (compose cpn2 cpn2); [|apply PR].
  econstructor.
  - repeat intro. eapply cpn2_mon; [apply IN|].
    intros. eapply cpn2_mon; [apply PR0|apply LE].
  - intros. eapply (compat2_compat cpn2_compat).
    eapply cpn2_mon; [apply PR0|].
    intros. eapply (compat2_compat cpn2_compat), PR1.
  - intros. eapply (compat2_bound cpn2_compat) in PR0.
    destruct PR0; [|right; apply H].
    eapply (compat2_bound cpn2_compat) in H.
    destruct H; [left; apply H|].
    right. eapply gf_mon; [apply H|].
    intros. apply cpn2_base. apply PR0.
Qed.

Lemma fcpn2_mon: monotone2 fcpn2.
Proof.
  repeat intro. eapply gf_mon; [eapply IN|].
  intros. eapply cpn2_mon; [apply PR|apply LE].
Qed.

Lemma fcpn2_sound:
  paco2 fcpn2 bot2 <2= paco2 gf bot2.
Proof.
  intros.
  set (rclo := fix rclo clo n (r: rel) :=
         match n with
         | 0 => r
         | S n' => rclo clo n' r \2/ clo (rclo clo n' r)
         end).
  assert (RC: exists n, rclo cpn2 n (paco2 fcpn2 bot2) x0 x1) by (exists 0; apply PR); clear PR.
  
  cut (forall n, rclo cpn2 n (paco2 fcpn2 bot2) <2= gf (rclo cpn2 (S n) (paco2 fcpn2 bot2))).
  { intro X. revert x0 x1 RC; pcofix CIH; intros.
    pfold. eapply gf_mon.
    - apply X. apply RC.
    - intros. right. eapply CIH. apply PR.
  }

  induction n; intros.
  - eapply gf_mon.
    + _punfold PR; [apply PR|apply fcpn2_mon].
    + intros. right. eapply cpn2_mon; [apply PR0|].
      intros. pclearbot. apply PR1.
  - destruct PR.
    + eapply gf_mon; [eapply IHn, H|]. intros. left. apply PR.
    + eapply gf_mon.
      * eapply (compat2_compat cpn2_compat).
        eapply (compat2_mon cpn2_compat); [apply H|apply IHn].
      * intros. econstructor 2. apply PR.
Qed.

(** 
  Recursive Closure & Weak Compatibility
*)

Inductive rclo2 (clo: rel->rel) (r: rel): rel :=
| rclo2_base
    e0 e1
    (R: r e0 e1):
    @rclo2 clo r e0 e1
| rclo2_clo'
    r' e0 e1
    (R': r' <2= rclo2 clo r)
    (CLOR': clo r' e0 e1):
    @rclo2 clo r e0 e1
| rclo2_step'
    r' e0 e1
    (R': r' <2= rclo2 clo r)
    (CLOR': @gf r' e0 e1):
    @rclo2 clo r e0 e1
| rclo2_cpn'
    r' e0 e1
    (R': r' <2= rclo2 clo r)
    (CLOR': @cpn2 r' e0 e1):
    @rclo2 clo r e0 e1
.

Structure wcompatible2 (clo: rel -> rel) : Prop :=
  wcompat2_intro {
      wcompat2_mon: monotone2 clo;
      wcompat2_wcompat: forall r,
          clo (gf r) <2= gf (rclo2 clo r);
      wcompat2_bound : forall r,
          bnd (clo r) <2= (bnd r \2/ gf (rclo2 clo r))
    }.

Lemma rclo2_mon_gen clo clo' r r' e0 e1
      (IN: @rclo2 clo r e0 e1)
      (LEclo: clo <3= clo')
      (LEr: r <2= r') :
  @rclo2 clo' r' e0 e1.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|apply CLOR'].
  - econstructor 4; [intros; eapply H, PR|].
    eapply cpn2_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo2_mon clo:
  monotone2 (rclo2 clo).
Proof.
  repeat intro. eapply rclo2_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo2_clo clo r:
  clo (rclo2 clo r) <2= rclo2 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo2_step clo r:
  gf (rclo2 clo r) <2= rclo2 clo r.
Proof.
  intros. econstructor 3; [|apply PR].
  intros. apply PR0.
Qed.

Lemma rclo2_cpn clo r:
  cpn2 (rclo2 clo r) <2= rclo2 clo r.
Proof.
  intros. econstructor 4; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo2_mult clo r:
  rclo2 clo (rclo2 clo r) <2= rclo2 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
  - econstructor 4; [eapply H | eapply CLOR'].
Qed.

Lemma rclo2_compose clo r:
  rclo2 (rclo2 clo) r <2= rclo2 clo r.
Proof.
  intros. induction PR.
  - apply rclo2_base, R.
  - apply rclo2_mult.
    eapply rclo2_mon; [apply CLOR'|apply H].
  - apply rclo2_step.
    eapply gf_mon; [apply CLOR'|apply H].
  - apply rclo2_cpn.
    eapply cpn2_mon; [apply CLOR'|apply H].
Qed.

Lemma wcompat2_compat
      clo (WCOM: wcompatible2 clo):
  compatible2 (rclo2 clo).
Proof.
  econstructor; [eapply rclo2_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo2_base. apply PR.
    + eapply gf_mon.
      * eapply (wcompat2_wcompat WCOM).
        eapply (wcompat2_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo2_mult, PR.
    + eapply gf_mon; [apply CLOR'|].
      intros. apply H in PR. apply rclo2_step, PR.
    + eapply gf_mon; [|intros; apply rclo2_cpn, PR].
      apply (compat2_compat cpn2_compat).
      eapply cpn2_mon; [apply CLOR'|apply H].
  - eapply (cbound2_distr bnd_compat) in PR.
    destruct PR. revert x0 x1 PTW.
    induction IN; intros.
    + left. apply PTW, R.
    + specialize (PTW _ CLOR').
      eapply (wcompat2_bound WCOM) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound2_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo2_mult.
        eapply rclo2_mon, R'. apply PR.
    + specialize (PTW _ CLOR').
      eapply (cbound2_compat bnd_compat) in PTW.
      right. eapply gf_mon. apply PTW. intros.
      eapply (cbound2_distr bnd_compat) in PR.
      destruct PR.
      eapply H in IN; [|apply PTW0].
      destruct IN.
      * apply rclo2_cpn, cpn2_bound.
        eapply cbound2_mon. apply H0. apply rclo2_base.
      * apply rclo2_step. apply H0.
    + specialize (PTW _ CLOR').
      apply (compat2_bound cpn2_compat) in PTW.
      destruct PTW as [PTW|PTW].
      * eapply (cbound2_distr bnd_compat) in PTW.
        destruct PTW.
        eapply H; [apply IN | apply PTW].
      * right. eapply gf_mon; [apply PTW|].
        intros. apply rclo2_cpn.
        eapply cpn2_mon; [apply PR|].
        intros. apply R', PR0.
Qed.

Lemma wcompat2_sound clo (WCOM: wcompatible2 clo):
  clo <3= cpn2.
Proof.
  intros. exists (rclo2 clo).
  - apply wcompat2_compat, WCOM.
  - apply rclo2_clo.
    eapply (wcompat2_mon WCOM); [apply PR|].
    intros. apply rclo2_base, PR0.
Qed.

(** 
  Lemmas for tactics
*)

Lemma cpn2_from_upaco r:
  upaco2 fcpn2 r <2= cpn2 r.
Proof.
  intros. destruct PR; [| apply cpn2_base, H].
  exists (rclo2 (paco2 fcpn2)).
  - apply wcompat2_compat.
    econstructor; [apply paco2_mon| |].
    + intros. _punfold PR; [|apply fcpn2_mon].
      eapply gf_mon; [apply PR|].
      intros. apply rclo2_cpn.
      eapply cpn2_mon; [apply PR0|].
      intros. destruct PR1.
      * apply rclo2_clo.
        eapply paco2_mon; [apply H0|].
        intros. apply rclo2_step.
        eapply gf_mon; [apply PR1|].
        intros. apply rclo2_base, PR2.
      * apply rclo2_step.
        eapply gf_mon; [apply H0|].
        intros. apply rclo2_base, PR1.
    + intros. right.
      eapply gf_mon, rclo2_cpn.
      eapply gf_mon, cpn2_bound.
      apply (cbound2_compat bnd_compat).
      eapply cbound2_mon. apply PR.
      intros. _punfold PR0; [|apply fcpn2_mon].
      eapply gf_mon. apply PR0.
      intros. apply rclo2_cpn.
      eapply cpn2_mon. apply PR1.
      intros. destruct PR2.
      * apply rclo2_clo.
        eapply paco2_mon. apply H0.
        intros. apply rclo2_base. apply PR2.
      * apply rclo2_base. apply H0.
  - apply rclo2_clo.
    eapply paco2_mon; [apply H|].
    intros. apply rclo2_base, PR.
Qed.

Lemma cpn2_from_paco r:
  paco2 fcpn2 r <2= cpn2 r.
Proof. intros. apply cpn2_from_upaco. left. apply PR. Qed.

Lemma fcpn2_from_paco r:
  paco2 fcpn2 r <2= fcpn2 r.
Proof.
  intros. _punfold PR; [|apply fcpn2_mon].
  eapply gf_mon; [apply PR|].
  intros. apply cpn2_cpn.
  eapply cpn2_mon; [apply PR0|].
  apply cpn2_from_upaco.
Qed.

Lemma fcpn2_to_paco r:
  fcpn2 r <2= paco2 fcpn2 r.
Proof.
  intros. pfold. eapply fcpn2_mon; [apply PR|].
  intros. right. apply PR0.
Qed.  

Lemma cpn2_complete:
  paco2 gf bot2 <2= cpn2 bot2.
Proof.
  intros. apply cpn2_from_paco.
  eapply paco2_mon_gen.
  - apply PR.
  - intros. eapply gf_mon; [apply PR0|apply cpn2_base].
  - intros. apply PR0.
Qed.

Lemma cpn2_init:
  cpn2 bot2 <2= paco2 gf bot2.
Proof.
  intros. apply fcpn2_sound, fcpn2_to_paco, (compat2_compat cpn2_compat).
  eapply cpn2_mon; [apply PR|contradiction].
Qed.

Lemma cpn2_clo
      r clo (LE: clo <3= cpn2):
  clo (cpn2 r) <2= cpn2 r.
Proof.
  intros. apply cpn2_cpn, LE, PR.
Qed.

Lemma cpn2_unfold:
  cpn2 bot2 <2= fcpn2 bot2.
Proof.
  intros. apply cpn2_init in PR. punfold PR.
  eapply gf_mon; [apply PR|].
  intros. pclearbot. apply cpn2_complete, PR0.
Qed.

Lemma cpn2_unfold_bound r
      (BASE: forall r, r <2= bnd r):
  cpn2 r <2= (bnd r \2/ fcpn2 r).
Proof.
  intros. apply BASE in PR.
  eapply compat2_bound in PR.
  - apply PR.
  - apply cpn2_compat.
Qed.

Lemma cpn2_step r:
  fcpn2 r <2= cpn2 r.
Proof.
  intros. eapply cpn2_clo, PR.
  intros. eapply wcompat2_sound, PR0.
  econstructor; [apply gf_mon| |].
  - intros. eapply gf_mon; [apply PR1|].
    intros. apply rclo2_step.
    eapply gf_mon; [apply PR2|].
    intros. apply rclo2_base, PR3.
  - intros. apply (cbound2_compat bnd_compat) in PR1.
    right. eapply gf_mon. apply PR1.
    intros. apply rclo2_cpn, cpn2_bound.
    eapply cbound2_mon. apply PR2.
    intros. apply rclo2_base, PR3.
Qed.

Lemma fcpn2_clo
      r clo (LE: clo <3= cpn2):
  clo (fcpn2 r) <2= fcpn2 r.
Proof.
  intros. apply LE, (compat2_compat cpn2_compat) in PR.
  eapply gf_mon; [apply PR|].
  intros. apply cpn2_cpn, PR0.
Qed.

Lemma cpn2_final: forall r, upaco2 gf r <2= cpn2 r.
Proof.
  intros. eapply cpn2_from_upaco.
  intros. eapply upaco2_mon_gen; [apply PR| |intros; apply PR0].
  intros. eapply gf_mon; [apply PR0|].
  intros. apply cpn2_base, PR1.
Qed.

Lemma fcpn2_final: forall r, paco2 gf r <2= fcpn2 r.
Proof.
  intros. _punfold PR; [|apply gf_mon].
  eapply gf_mon; [apply PR | apply cpn2_final].
Qed.

Lemma cpn2_algebra r :
  r <2= gf r -> r <2= cpn2 bot2.
Proof.
  intros. apply cpn2_final. left.
  revert x0 x1 PR.
  pcofix CIH. intros.
  pfold. eapply gf_mon. apply H, PR.
  intros. right. apply CIH, PR0.
Qed.

End Companion2_main.

Lemma cbound2_bot gf:
  compatible_bound2 gf bot3.
Proof.
  econstructor; intros; contradiction.
Qed.

Lemma cpn2_mon_bot (gf gf': rel -> rel) bnd bnd' e0 e1 r
      (IN: @cpn2 gf bnd bot2 e0 e1)
      (MON: monotone2 gf)
      (MON': monotone2 gf')
      (BASE: compatible_bound2 gf bnd)
      (BASE': compatible_bound2 gf' bnd')
      (LE: gf <3= gf'):
  @cpn2 gf' bnd' r e0 e1.
Proof.
  apply cpn2_init in IN; [|apply MON|apply BASE].
  apply cpn2_final; [apply MON'|apply BASE'|].
  left. eapply paco2_mon_gen; [apply IN| apply LE| contradiction].
Qed.

Lemma fcpn2_mon_bot (gf gf': rel -> rel) bnd bnd' e0 e1 r
      (IN: @fcpn2 gf bnd bot2 e0 e1)
      (MON: monotone2 gf)
      (MON': monotone2 gf')
      (BASE: compatible_bound2 gf bnd)
      (BASE': compatible_bound2 gf' bnd')
      (LE: gf <3= gf'):
  @fcpn2 gf' bnd' r e0 e1.
Proof.
  apply LE. eapply MON. apply IN.
  intros. eapply cpn2_mon_bot; eassumption.
Qed.

End Companion2.

Hint Unfold fcpn2 : paco.
Hint Resolve cpn2_base : paco.
Hint Resolve cpn2_step : paco.
Hint Resolve cbound2_bot : paco.

Hint Constructors rclo2 : rclo.
Hint Resolve rclo2_clo rclo2_step rclo2_cpn : rclo.

