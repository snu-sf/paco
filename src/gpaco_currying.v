Require Export Program.Basics. Open Scope program_scope.
From Paco Require Export paco_rel.
From Paco Require Import gpaco_internal.

Set Implicit Arguments.
Set Universe Polymorphism.

Section INTERNAL.

Universe u v w.
Context {n : nat} {t : arity@{u v w} n}.

Notation rel := (rel t).
Notation _rel := (_rel t).
Local Infix "<=" := le.

Definition _rclo (clo: rel->rel) (r: rel) : rel :=
  curry (rclo (uncurry_relT clo) (uncurry r)).

Lemma le_transport (r0 r0' : _rel) :
  r0 <1= r0' ->
  forall r1 r1',
  _le r1 r0 ->
  _le r0' r1' ->
  _le r1 r1'.
Proof.
  red; auto.
Qed.

Lemma monotone_transport {gf gf' : _rel -> _rel}
      {gf_mon : paco_internal.monotone gf}
      {gf_mon' : paco_internal.monotone gf'} :
  forall r0 r0',
  gf r0 <1= gf' r0' ->
  forall r1 r1',
  _le r1 r0 ->
  _le r0' r1' ->
  _le (gf r1) (gf' r1').
Proof.
  red; intros.
  eapply le_transport; [ apply H | .. | eassumption ].
  - eapply gf_mon; assumption.
  - eapply gf_mon'; eassumption.
Qed.

Lemma rclo_transport {clo0 clo0' : _rel -> _rel} {r0 r0' : _rel} :
  rclo clo0 r0 <1= rclo clo0' r0' ->
  forall clo1 clo1' r1 r1',
  _le_relT clo1 clo0 ->
  _le_relT clo0' clo1' ->
  _le r1 r0 ->
  _le r0' r1' ->
  _le (rclo clo1 r1) (rclo clo1' r1').
Proof.
  red; intros.
  eapply le_transport; [ apply H | .. | eassumption ];
    red; eapply rclo_mon_gen; assumption.
Qed.

Lemma gpaco_transport {gf0 gf0' : _rel -> _rel} {clo0 clo0' : _rel -> _rel} {r0 r0' s0 s0' : _rel} :
  gpaco gf0 clo0 r0 s0 <1= gpaco gf0' clo0' r0' s0' ->
  __monotone gf0' ->
  forall gf1 gf1' clo1 clo1' r1 r1' s1 s1',
  __monotone gf1 ->
  _le_relT gf1 gf0 ->
  _le_relT gf0' gf1' ->
  _le_relT clo1 clo0 ->
  _le_relT clo0' clo1' ->
  _le r1 r0 ->
  _le r0' r1' ->
  _le s1 s0 ->
  _le s0' s1' ->
  _le (gpaco gf1 clo1 r1 s1) (gpaco gf1' clo1' r1' s1').
Proof.
  red; intros.
  eapply le_transport; [ apply H | .. | eassumption ].
  all: red; apply gpaco_mon_gen; assumption.
Qed.

Lemma le_uncurry_curry_l (gf gf' : _rel) :
  _le gf gf' ->
  _le (uncurry (curry gf)) gf'.
Proof.
  red; intros.
  eapply H, uncurry_curry; assumption.
Qed.

Ltac simpl_le etc :=
  repeat 
    lazymatch goal with
    | [ |- _le_relT _ _ ] => let r := fresh "r" in intros r
    | [ |- forall r : rel1 _, _ ] =>
      let r := fresh r in intros r
    | _ => apply Reflexive_le_ + apply le_uncurry_curry_l + (red; apply rclo_mon_gen) + etc
    end.

Ltac finish_translate etc _L_ :=
  lazymatch goal with
  | [ |- le _ _ ] =>
    apply (proj2 (curry_le _ _)) + apply curry_le_r;
    try ((red; apply _L_) + apply le_transport with (1 := _L_); simpl_le etc)
  | [ |- _monotone _ ] =>
    apply curry_monotone;
    try (apply _L_)
  end.

Ltac translate_ etc X :=
  let _L_ := fresh "_L_" in
  pose proof X as _L_;
  repeat lazymatch goal with
  | [ |- forall clo : rel -> rel, _ ] =>
    let clo := fresh clo in
    intros clo;
    specialize (_L_ (uncurry_relT clo))
  | [ |- forall r : rel, _ ] =>
    let r := fresh r in
    intros r;
    specialize (_L_ (uncurry r))
  | [ |- forall H : le_relT _ _, _ ] =>
    let H := fresh H in
    intros H;
    apply uncurry_relT_le_relT in H;
    specialize (_L_ H);
    clear H
  | [ |- forall H : le _ _, _ ] =>
    let H := fresh H in
    intros H;
    apply uncurry_le in H;
    specialize (_L_ H);
    clear H
  | _ => finish_translate etc _L_
  end.

Section A.

Ltac translate X := translate_ fail (@X (tuple t)).

Lemma _rclo_mon_gen : forall clo clo' r r'
      (LEclo: le_relT clo clo')
      (LEr: r <= r'),
  _rclo clo r <= _rclo clo' r'.
Proof.
  translate rclo_mon_gen.
Qed.

Lemma _rclo_mon clo : _monotone (_rclo clo).
Proof.
  translate rclo_mon.
Qed.

Lemma _rclo_clo : forall clo r,
  clo (_rclo clo r) <= _rclo clo r.
Proof.
  translate rclo_clo.
Qed.

Lemma _rclo_rclo : forall clo r,
  _rclo clo (_rclo clo r) <= _rclo clo r.
Proof.
  translate rclo_rclo.
Qed.

Lemma _rclo_compose : forall clo r,
  _rclo (_rclo clo) r <= _rclo clo r.
Proof.
  translate rclo_compose.
Qed.

End A.

Definition _gpaco (gf : rel -> rel) (clo : rel -> rel) (r rg : rel) : rel :=
  curry (gpaco (uncurry_relT gf) (uncurry_relT clo) (uncurry r) (uncurry rg)).

Definition _gupaco gf clo r := _gpaco gf clo r r.

Lemma _gupaco_equiv gf clo r x :
  uncurry (_gupaco gf clo r) x <->
  gupaco (uncurry_relT gf) (uncurry_relT clo) (uncurry r) x.
Proof.
  unfold _gupaco, _gpaco.
  apply uncurry_curry.
Qed.

Lemma __monotone_equiv (gf : rel -> rel) (gf' : _rel -> _rel) :
  (forall r x, uncurry (gf r) x <-> gf' (uncurry r) x) ->
  __monotone gf' ->
  _monotone gf.
Proof.
  intros H MON r r' Hr.
  apply uncurry_le.
  intros u. rewrite 2 H.
  apply MON.
  apply uncurry_le, Hr.
Qed.

Section GPaco.

Ltac simpl_paco :=
  (red; apply gpaco_mon_gen) +
  (apply uncurry_monotone; assumption) +
  (intros _r; unfold uncurry_relT; match goal with
              | [ |- ?G ] =>
                match G with
                | context _ctx [ curry (uncurry ?r) ] =>
                  destruct (paco_sigma.eq_sym (curry_uncurry _ _ r))
                end
              end).

Ltac translate' := translate_ simpl_paco.
Ltac translate X := translate' (@X (tuple t)).

Lemma _gpaco_mon : forall gf clo r r' rg rg'
      (LEr: r <= r')
      (LErg: rg <= rg'),
  _gpaco gf clo r rg <= _gpaco gf clo r' rg'.
Proof.
  translate gpaco_mon.
Qed.

Lemma _gupaco_mon : forall gf clo, _monotone (_gupaco gf clo).
Proof.
  intros; eapply __monotone_equiv; [ apply _gupaco_equiv | apply gupaco_mon ].
Qed.

Lemma _gpaco_base : forall gf clo r rg, r <= _gpaco gf clo r rg.
Proof.
  translate gpaco_base.
Qed.

Lemma _gpaco_gen_guard gf (gf_mon : _monotone gf) : forall clo r rg,
  _gpaco gf clo r (union rg r) <= _gpaco gf clo r rg.
Proof.
  translate' (@gpaco_gen_guard (tuple t) (uncurry_relT gf)).
Qed.

Lemma _gpaco_rclo : forall gf clo r rg,
  _rclo clo r <= _gpaco gf clo r rg.
Proof.
  translate gpaco_rclo.
Qed.

Lemma _gpaco_clo : forall gf clo r rg,
  clo r <= _gpaco gf clo r rg.
Proof.
  translate gpaco_clo.
Qed.

End GPaco.

Section GPacoMon.

Lemma gpaco_def_mon : clo : monotone (compose gf (rclo clo)).
Proof using gf_mon.
  typeclasses eauto.
Qed.

Hint Resolve gpaco_def_mon : paco.

Lemma gpaco_gen_rclo clo r rg:
  gpaco (rclo clo) r rg <1= gpaco clo r rg.
Proof.
  intros. destruct PR. econstructor.
  apply rclo_compose.
  monotonic rclo_mon IN.
  destruct 1; [|right; apply H].
  left. monotonic paco_mon_gen H.
  - intro; eapply gf_mon, rclo_compose.
  - trivial.
Qed.

Lemma gpaco_step_gen clo r rg:
  gf (gpaco clo (rg \1/ r) (rg \1/ r)) <1= gpaco clo r rg.
Proof.
  intros. econstructor. apply rclo_base. left.
  apply paco_fold. monotonic gf_mon PR.
  destruct 1. monotonic rclo_mon IN.
  destruct 1.
  - left. monotonic paco_mon H. destruct 1; trivial.
  - right. trivial.
Qed.

Lemma gpaco_step clo r rg:
  gf (gpaco clo rg rg) <1= gpaco clo r rg.
Proof.
  intros. apply gpaco_step_gen.
  monotonic gf_mon PR; apply gpaco_mon; auto.
Qed.

Lemma gpaco_final clo r rg:
  (r \1/ paco gf rg) <1= gpaco clo r rg.
Proof.
  intros. destruct PR. apply gpaco_base, H.
  econstructor. apply rclo_base.
  left. monotonic paco_mon_gen H.
  - intros. monotonic gf_mon PR; apply rclo_base.
  - auto.
Qed.

Lemma gpaco_unfold clo r rg:
  gpaco clo r rg <1= rclo clo (gf (gupaco clo (rg \1/ r)) \1/ r).
Proof.
  intros. destruct PR.
  monotonic rclo_mon IN.
  intros. destruct PR; cycle 1. right; apply H.
  left. apply paco_unfold in H; [|apply gpaco_def_mon].
  monotonic gf_mon H.
  intros. econstructor.
  monotonic rclo_mon PR.
  destruct 1 as [H|H]; [| right; apply H].
  left. monotonic paco_mon H.
  auto.
Qed.

Lemma gpaco_cofix clo r rg 
      l (OBG: forall rr (INC: rg <1= rr) (CIH: l <1= rr), l <1= gpaco clo r rr):
  l <1= gpaco clo r rg.
Proof.
  assert (IN: l <1= gpaco clo r (rg \1/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. constructor.
  monotonic rclo_mon IN0.
  intros x0 H; destruct H as [H|H]; [left|right; apply H].
  revert x0 H. pcofix_ CIH.
  intros x SIM; apply paco_unfold in SIM; [..| apply gpaco_def_mon].
  apply paco_fold.
  monotonic gf_mon SIM. intros x PR.
  apply rclo_rclo. monotonic rclo_mon PR.
  destruct 1 as [H|H].
  - apply rclo_base. right. apply CIH, H. 
  - destruct H as [[] | ].
    + apply rclo_base. right. apply Hr0. left. apply H.
    + apply IN in H. destruct H.
      monotonic rclo_mon IN0.
      destruct 1.
      * right. apply CIH. apply H.      
      * right. apply Hr0. right. apply H.
    + apply rclo_base. right. apply Hr0. right. apply H.
Qed.

Lemma gpaco_gupaco clo r rg:
  gupaco clo (gpaco clo r rg) <1= gpaco clo r rg.
Proof.
  eapply gpaco_cofix.
  intros; destruct PR. econstructor.
  apply rclo_rclo. monotonic rclo_mon IN.
  intros. destruct PR.
  - apply rclo_base. left.
    monotonic paco_mon H.
    intros. left; apply CIH.
    econstructor. apply rclo_base. right.
    destruct PR; apply H.
  - destruct H. monotonic rclo_mon IN.
    intros. destruct PR; [| right; apply H].
    left. monotonic paco_mon H.
    intros. destruct PR as [H|H].
    + left. apply INC, H.
    + right. apply H.
Qed.

Lemma gpaco_gpaco clo r rg:
  gpaco clo (gpaco clo r rg) (gupaco clo (rg \1/ r)) <1= gpaco clo r rg.
Proof.
  intros. apply gpaco_unfold in PR.
  econstructor. apply rclo_rclo. eapply rclo_mon; [| apply PR]. clear x0 PR. intros.
  destruct PR; [|destruct H; apply IN].
  apply rclo_base. left. apply paco_fold.
  monotonic gf_mon H. intros.
  enough (@gupaco clo (rg \1/ r) x0).
  { destruct H. monotonic rclo_mon IN.
    destruct 1; [|right; apply H].
    left. monotonic paco_mon H. destruct 1 as [H|H]; apply H.
  }
  apply gpaco_gupaco. monotonic gupaco_mon PR.
  destruct 1; [apply H|].
  monotonic gpaco_mon H; [right|left]; apply PR.
Qed.

Lemma gpaco_uclo uclo clo r rg 
      (LEclo: uclo <2= gupaco clo) :
  uclo (gpaco clo r rg) <1= gpaco clo r rg.
Proof.
  intros. apply gpaco_gupaco. apply LEclo, PR.
Qed.

Lemma gpaco_weaken  clo r rg:
  gpaco (gupaco clo) r rg <1= gpaco clo r rg.
Proof.
  intros. apply gpaco_unfold in PR.
  induction PR.
  - destruct IN; cycle 1. apply gpaco_base, H.
    apply gpaco_step_gen. monotonic gf_mon H.
    eapply gpaco_cofix. intros.
    apply gpaco_unfold in PR.
    induction PR.
    + destruct IN; [| apply gpaco_base, H].
      apply gpaco_step. monotonic gf_mon H.
      intros. apply gpaco_base. apply CIH.
      monotonic gupaco_mon PR.
      destruct 1 as [H|H]; apply H.
    + apply gpaco_gupaco.
      monotonic gupaco_mon IN. apply H.
  - apply gpaco_gupaco.
    monotonic gupaco_mon IN. apply H.
Qed.

End GPacoMon.

End Main.

Hint Resolve gpaco_def_mon : paco.

Section GeneralMonotonicity.

Context {gf: rel -> rel} {gf_mon : monotone gf}.
  
Lemma gpaco_mon_gen (gf' clo clo': rel -> rel) r r' rg rg'
      (LEgf: gf <2= gf')
      (LEclo: clo <2= clo')
      (LEr: r <1= r')
      (LErg: rg <1= rg') :
  @gpaco gf clo r rg <1= @gpaco gf' clo' r' rg'.
Proof.
  intros x0 IN. eapply gpaco_mon; [apply LEr|apply LErg| ].
  destruct IN. econstructor.
  monotonic rclo_mon_gen IN. apply LEclo.
  destruct 1 as [H|H]; [left|right; apply H].
  monotonic paco_mon_gen H.
  - intros. eapply LEgf.
    monotonic gf_mon PR.
    intros. monotonic rclo_mon_gen PR. apply LEclo. trivial.
  - trivial.
Qed.

Lemma gpaco_mon_bot (gf' clo clo': rel -> rel) r' rg'
      (LEgf: gf <2= gf')
      (LEclo: clo <2= clo'):
  @gpaco gf clo bot1 bot1 <1= @gpaco gf' clo' r' rg'.
Proof.
  apply gpaco_mon_gen; assumption + contradiction.
Qed.

Lemma gupaco_mon_gen
      (gf' clo clo': rel -> rel) r r'
      (LEgf: gf <2= gf')
      (LEclo: clo <2= clo')
      (LEr: r <1= r'):
  @gupaco gf clo r <1= @gupaco gf' clo' r'.
Proof.
  apply gpaco_mon_gen; assumption.
Qed.

End GeneralMonotonicity.

Section CompatibilityDef.

Variable gf: rel -> rel.

Structure compatible (clo: rel -> rel) : Prop :=
  compat_intro {
      compat_mon: monotone clo;
      compat_compat : forall r,
          clo (gf r) <1= gf (clo r);
    }.

Structure wcompatible clo : Prop :=
  wcompat_intro {
      wcompat_mon: monotone clo;
      wcompat_wcompat : forall r,
          clo (gf r) <1= gf (gupaco gf clo r);
    }.

End CompatibilityDef.

Section Compatibility.

Context {gf : rel -> rel} {gf_mon: monotone gf}.

Local Notation compatible := (compatible gf).
Local Notation wcompatible := (wcompatible gf).

Lemma rclo_dist clo
      (MON: monotone clo)
      (DIST: forall r1 r2, clo (r1 \1/ r2) <1= (clo r1 \1/ clo r2)):
  forall r1 r2, rclo clo (r1 \1/ r2) <1= (rclo clo r1 \1/ rclo clo r2).
Proof.
  intros. induction PR.
  + destruct IN; [left|right]; apply rclo_base, H.
  + assert (REL: clo (rclo clo r1 \1/ rclo clo r2) x0).
    { monotonic MON IN. apply H. }
    apply DIST in REL. destruct REL; [left|right]; apply rclo_clo, H0.
Qed.

Lemma rclo_compat clo
      (COM: compatible clo):
  compatible (rclo clo).
Proof.
  econstructor; [ typeclasses eauto | ].
  intros. induction PR.
  - monotonic gf_mon IN.
    intros. eapply rclo_base. apply PR.
  - eapply gf_mon.
    + intros. eapply rclo_clo. apply PR.
    + eapply COM. eapply COM. apply H. apply IN.
Qed.

Lemma rclo_wcompat clo
      (COM: wcompatible clo):
  wcompatible (rclo clo).
Proof.
  econstructor; [ typeclasses eauto | ].
  intros. induction PR.
  - monotonic gf_mon IN.
    intros. apply gpaco_base. apply PR.
  - eapply gf_mon.
    + intros. apply gpaco_gupaco.
      monotonic gupaco_mon_gen PR; [trivial| |eauto].
      intros ? ?; eapply rclo_clo'. apply rclo_base.
    + eapply COM. eapply COM. apply H. apply IN.
Qed.

Lemma compat_wcompat clo
      (CMP: compatible clo):
  wcompatible clo.
Proof.
  econstructor. apply CMP.
  intros. apply CMP in PR.
  monotonic gf_mon PR.
  intros. apply gpaco_clo, PR.
Qed.

Lemma wcompat_compat clo
      (WCMP: wcompatible clo) :
  compatible (gupaco gf clo).
Proof.
  econstructor; [ typeclasses eauto | ].
  intros. apply gpaco_unfold in PR.
  induction PR.
  - destruct IN; cycle 1.
    + monotonic gf_mon H.
      intros. apply gpaco_base, PR.
    + monotonic gf_mon H.
      intros. apply gpaco_gupaco.
      monotonic gupaco_mon PR.
      intros. apply gpaco_step.
      apply (or_ind (fun x => x) (fun x => x)) in PR.
      monotonic gf_mon PR.
      apply gpaco_base.
  - eapply gf_mon; [ apply gpaco_gupaco | ].
    apply WCMP. eapply WCMP. apply H. apply IN.
Qed.

Lemma wcompat_union clo1 clo2
      (WCMP1: wcompatible clo1)
      (WCMP2: wcompatible clo2):
  wcompatible (clo1 \2/ clo2).
Proof.
  econstructor.
  - apply monotone_union. apply WCMP1. apply WCMP2.
  - intros. destruct PR.
    + apply WCMP1 in H. monotonic gf_mon H.
      intros. monotonic gupaco_mon_gen PR; auto.
    + apply WCMP2 in H. monotonic gf_mon H.
      intros. monotonic gupaco_mon_gen PR; auto.
Qed.

End Compatibility.

Section Soundness.

Context {gf: rel -> rel} {gf_mon: monotone gf}.

Lemma gpaco_compat_init clo
      (CMP: compatible gf clo):
  gpaco gf clo bot1 bot1 <1= paco gf bot1.
Proof.
  intros. destruct PR. revert x0 IN.
  pcofix_ CIH. intros x H. apply paco_fold.
  eapply gf_mon; [right; apply CIH, rclo_rclo, PR |].
  apply compat_compat with (gf:=gf). apply rclo_compat. apply CMP.
  monotonic rclo_mon H.
  intros. destruct PR; [|contradiction]. apply paco_unfold in H; [..|apply gpaco_def_mon ].
  monotonic gpaco_def_mon H.
  intros. destruct PR; [left; apply H|destruct H; contradiction].
Qed.

Lemma gpaco_init clo
      (WCMP: wcompatible gf clo):
  gpaco gf clo bot1 bot1 <1= paco gf bot1.
Proof.
  intros. eapply gpaco_compat_init.
  - apply wcompat_compat, WCMP.
  - monotonic gpaco_mon_bot PR. intros; apply PR.
    intros. apply gpaco_clo, PR.
Qed.

Lemma gpaco_unfold_bot clo
      (WCMP: wcompatible gf clo):
  gpaco gf clo bot1 bot1 <1= gf (gpaco gf clo bot1 bot1).
Proof.
  intros. apply gpaco_init in PR; [|apply WCMP].
  apply paco_unfold in PR; [..|apply gf_mon].
  monotonic gf_mon PR.
  intros. destruct PR; [|contradiction]. apply gpaco_final; auto.
Qed.

End Soundness.

Section Distributivity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone gf.

Lemma gpaco_dist clo r rg
      (CMP: wcompatible gf clo)
      (DIST: forall r1 r2, clo (r1 \1/ r2) <1= (clo r1 \1/ clo r2)):
  gpaco gf clo r rg <1= (paco gf (rclo clo (rg \1/ r)) \1/ rclo clo r).
Proof.
  intros x PR. apply gpaco_unfold in PR.
  apply rclo_dist in PR; [|apply CMP|apply DIST].
  destruct PR; [|right; apply H].
  left. revert x H.
  pcofix_ CIH; intros x PR.
  apply rclo_wcompat in PR; [|apply CMP].
  apply paco_fold. monotonic gf_mon PR. intros x PR.
  apply gpaco_unfold in PR.
  apply rclo_compose in PR.
  apply rclo_dist in PR; [|apply CMP|apply DIST].
  destruct PR as [PR|PR].
  - right. apply CIH.
    monotonic rclo_mon PR. apply gf_mon. intros x PR.
    apply gpaco_gupaco.
    apply gpaco_gen_rclo.
    monotonic gupaco_mon PR. intros x PR.
    destruct PR as [PR|PR]; apply PR.
  - assert (REL: @rclo clo (rclo clo (gf (gupaco gf clo ((rg \1/ r) \1/ (rg \1/ r))) \1/ (rg \1/ r))) x).
    { monotonic rclo_mon PR. intros. apply gpaco_unfold in PR; assumption. }
    apply rclo_rclo in REL.
    apply rclo_dist in REL; [|apply CMP|apply DIST].
    right. destruct REL as [REL|REL]; [| apply Hr0, REL].
    apply CIH.
    monotonic rclo_mon REL. apply gf_mon, gupaco_mon.
    destruct 1 as [PR1|PR1]; apply PR1.
Qed.

Lemma gpaco_dist_reverse clo r rg:
  (paco gf (rclo clo (rg \1/ r)) \1/ rclo clo r) <1= gpaco gf clo r rg.
Proof.
  intros. destruct PR; cycle 1.
  - eapply gpaco_rclo. apply H.
  - econstructor. apply rclo_base. left.
    revert x0 H. pcofix_ CIH; intros x PR.
    apply paco_unfold in PR; [|apply gf_mon].
    apply paco_fold.
    monotonic gf_mon PR. intros x PR.
    destruct PR as [PR|PR].
    + apply rclo_base. auto.
    + monotonic rclo_mon PR. auto.
Qed.

End Distributivity.

Section Companion.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone gf.

Inductive cpn (r: rel) x0 : Prop :=
| cpn_intro
    clo
    (COM: compatible gf clo)
    (CLO: clo r x0)
.

Lemma cpn_mon: monotone cpn.
Proof.
  red; red. destruct 2. exists clo.
  - apply COM.
  - eapply compat_mon; [apply COM|apply LE|apply CLO].
Qed.

Lemma cpn_greatest: forall clo (COM: compatible gf clo), clo <2= cpn.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn_compat: compatible gf cpn.
Proof.
  econstructor; [apply cpn_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - intros. econstructor; [apply COM|apply PR].
  - eapply (compat_compat COM); apply CLO.
Qed.

Lemma cpn_wcompat: wcompatible gf cpn.
Proof. apply compat_wcompat, cpn_compat. Qed.

Lemma cpn_gupaco:
  gupaco gf cpn <2= cpn.
Proof.
  intros. eapply cpn_greatest, PR. apply wcompat_compat. apply cpn_wcompat.
Qed.

Lemma cpn_cpn r:
  cpn (cpn r) <1= cpn r.
Proof.
  intros. apply cpn_gupaco, gpaco_gupaco, gpaco_clo.
  eapply cpn_mon; [ apply gpaco_clo | apply PR ].
Qed.

Lemma cpn_base r:
  r <1= cpn r.
Proof.
  intros. apply cpn_gupaco. apply gpaco_base, PR.
Qed.

Lemma cpn_clo
      r clo (LE: clo <2= cpn):
  clo (cpn r) <1= cpn r.
Proof.
  intros. apply cpn_cpn, LE, PR.
Qed.

Lemma cpn_step r:
  gf (cpn r) <1= cpn r.
Proof.
  intros. apply cpn_gupaco. apply gpaco_step.
  monotonic gf_mon PR; apply gpaco_clo.
Qed.

Lemma cpn_uclo uclo
      (MON: monotone uclo)
      (WCOM: forall r, uclo (gf r) <1= gf (gupaco gf (uclo \2/ cpn) r)):
  uclo <2= gupaco gf cpn.
Proof.
  intros. apply gpaco_clo.
  exists (gupaco gf (uclo \2/ cpn)).
  - apply wcompat_compat.
    econstructor.
    + apply monotone_union. apply MON. apply cpn_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat_compat with (gf:=gf) in H; [| apply cpn_compat].
        monotonic gf_mon H. intros.
        apply gpaco_clo. right. apply PR0.
  - apply gpaco_clo. left. apply PR.
Qed.

End Companion.
End GeneralizedPaco.
