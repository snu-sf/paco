Require Export paconotation.
Require Import paconotation_internal pacotac_internal paco_internal.
Set Implicit Arguments.

Section PACO6.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.

(** ** Signatures *)

Record sig6T  :=
  exist6T {
      proj6T0: @T0;
      proj6T1: @T1 proj6T0;
      proj6T2: @T2 proj6T0 proj6T1;
      proj6T3: @T3 proj6T0 proj6T1 proj6T2;
      proj6T4: @T4 proj6T0 proj6T1 proj6T2 proj6T3;
      proj6T5: @T5 proj6T0 proj6T1 proj6T2 proj6T3 proj6T4;
    }.
Definition uncurry6  (R: rel6 T0 T1 T2 T3 T4 T5): rel1 sig6T :=
  fun x => R (proj6T0 x) (proj6T1 x) (proj6T2 x) (proj6T3 x) (proj6T4 x) (proj6T5 x).
Definition curry6  (R: rel1 sig6T): rel6 T0 T1 T2 T3 T4 T5 :=
  fun x0 x1 x2 x3 x4 x5 => R (@exist6T x0 x1 x2 x3 x4 x5).

Lemma uncurry_map6 r0 r1 (LE : r0 <6== r1) : uncurry6 r0 <1== uncurry6 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev6 r0 r1 (LE: uncurry6 r0 <1== uncurry6 r1) : r0 <6== r1.
Proof.
  red; intros. apply (LE (@exist6T x0 x1 x2 x3 x4 x5) PR).
Qed.

Lemma curry_map6 r0 r1 (LE: r0 <1== r1) : curry6 r0 <6== curry6 r1.
Proof. 
  red; intros. apply (LE (@exist6T x0 x1 x2 x3 x4 x5) PR).
Qed.

Lemma curry_map_rev6 r0 r1 (LE: curry6 r0 <6== curry6 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_6 r : curry6 (uncurry6 r) <6== r.
Proof. unfold le6. intros. apply PR. Qed.

Lemma uncurry_bij2_6 r : r <6== curry6 (uncurry6 r).
Proof. unfold le6. intros. apply PR. Qed.

Lemma curry_bij1_6 r : uncurry6 (curry6 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_6 r : r <1== uncurry6 (curry6 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_6 r0 r1 (LE: uncurry6 r0 <1== r1) : r0 <6== curry6 r1.
Proof.
  apply uncurry_map_rev6. eapply le1_trans; [apply LE|]. apply curry_bij2_6.
Qed.

Lemma uncurry_adjoint2_6 r0 r1 (LE: r0 <6== curry6 r1) : uncurry6 r0 <1== r1.
Proof.
  apply curry_map_rev6. eapply le6_trans; [|apply LE]. apply uncurry_bij2_6.
Qed.

Lemma curry_adjoint1_6 r0 r1 (LE: curry6 r0 <6== r1) : r0 <1== uncurry6 r1.
Proof.
  apply curry_map_rev6. eapply le6_trans; [apply LE|]. apply uncurry_bij2_6.
Qed.

Lemma curry_adjoint2_6 r0 r1 (LE: r0 <1== uncurry6 r1) : curry6 r0 <6== r1.
Proof.
  apply uncurry_map_rev6. eapply le1_trans; [|apply LE]. apply curry_bij1_6.
Qed.

(** ** Predicates of Arity 6
*)

Definition paco6(gf : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5)(r: rel6 T0 T1 T2 T3 T4 T5) : rel6 T0 T1 T2 T3 T4 T5 :=
  curry6 (paco (fun R0 => uncurry6 (gf (curry6 R0))) (uncurry6 r)).

Definition upaco6(gf : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5)(r: rel6 T0 T1 T2 T3 T4 T5) := paco6 gf r \6/ r.
Arguments paco6 : clear implicits.
Arguments upaco6 : clear implicits.
Hint Unfold upaco6.

Definition monotone6 (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) :=
  forall x0 x1 x2 x3 x4 x5 r r' (IN: gf r x0 x1 x2 x3 x4 x5) (LE: r <6= r'), gf r' x0 x1 x2 x3 x4 x5.

Definition _monotone6 (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) :=
  forall r r'(LE: r <6= r'), gf r <6== gf r'.

Lemma monotone6_eq (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) :
  monotone6 gf <-> _monotone6 gf.
Proof. unfold monotone6, _monotone6, le6. split; intros; eapply H; eassumption. Qed.

Lemma monotone6_map (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5)
      (MON: _monotone6 gf) :
  _monotone (fun R0 => uncurry6 (gf (curry6 R0))).
Proof.
  red; intros. apply uncurry_map6. apply MON; apply curry_map6; assumption.
Qed.

Lemma _paco6_mon_gen (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) r r'
    (LEgf: gf <7= gf')
    (LEr: r <6= r'):
  paco6 gf r <6== paco6 gf' r'.
Proof.
  apply curry_map6. red; intros. eapply paco_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma paco6_mon_gen (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) r r' x0 x1 x2 x3 x4 x5
    (REL: paco6 gf r x0 x1 x2 x3 x4 x5)
    (LEgf: gf <7= gf')
    (LEr: r <6= r'):
  paco6 gf' r' x0 x1 x2 x3 x4 x5.
Proof.
  eapply _paco6_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma paco6_mon_bot (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) r' x0 x1 x2 x3 x4 x5
    (REL: paco6 gf bot6 x0 x1 x2 x3 x4 x5)
    (LEgf: gf <7= gf'):
  paco6 gf' r' x0 x1 x2 x3 x4 x5.
Proof.
  eapply paco6_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upaco6_mon_gen (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) r r' x0 x1 x2 x3 x4 x5
    (REL: upaco6 gf r x0 x1 x2 x3 x4 x5)
    (LEgf: gf <7= gf')
    (LEr: r <6= r'):
  upaco6 gf' r' x0 x1 x2 x3 x4 x5.
Proof.
  destruct REL.
  - left. eapply paco6_mon_gen; [apply H | apply LEgf | apply LEr].
  - right. apply LEr, H.
Qed.

Lemma upaco6_mon_bot (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) r' x0 x1 x2 x3 x4 x5
    (REL: upaco6 gf bot6 x0 x1 x2 x3 x4 x5)
    (LEgf: gf <7= gf'):
  upaco6 gf' r' x0 x1 x2 x3 x4 x5.
Proof.
  eapply upaco6_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Section Arg6.

Variable gf : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5.
Arguments gf : clear implicits.

Theorem _paco6_mon: _monotone6 (paco6 gf).
Proof.
  red; intros. eapply curry_map6, _paco_mon; apply uncurry_map6; assumption.
Qed.

Theorem _paco6_acc: forall
  l r (OBG: forall rr (INC: r <6== rr) (CIH: l <6== rr), l <6== paco6 gf rr),
  l <6== paco6 gf r.
Proof.
  intros. apply uncurry_adjoint1_6.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_6 in INC. apply uncurry_adjoint1_6 in CIH.
  apply uncurry_adjoint2_6.
  eapply le6_trans. eapply (OBG _ INC CIH).
  apply curry_map6.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_6.
Qed.

Theorem _paco6_mult_strong: forall r,
  paco6 gf (upaco6 gf r) <6== paco6 gf r.
Proof.
  intros. apply curry_map6.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco6_fold: forall r,
  gf (upaco6 gf r) <6== paco6 gf r.
Proof.
  intros. apply uncurry_adjoint1_6.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco6_unfold: forall (MON: _monotone6 gf) r,
  paco6 gf r <6== gf (upaco6 gf r).
Proof.
  intros. apply curry_adjoint2_6.
  eapply _paco_unfold; apply monotone6_map; assumption.
Qed.

Theorem paco6_acc: forall
  l r (OBG: forall rr (INC: r <6= rr) (CIH: l <6= rr), l <6= paco6 gf rr),
  l <6= paco6 gf r.
Proof.
  apply _paco6_acc.
Qed.

Theorem paco6_mon: monotone6 (paco6 gf).
Proof.
  apply monotone6_eq.
  apply _paco6_mon.
Qed.

Theorem upaco6_mon: monotone6 (upaco6 gf).
Proof.
  red; intros.
  destruct IN.
  - left. eapply paco6_mon. apply H. apply LE.
  - right. apply LE, H.
Qed.

Theorem paco6_mult_strong: forall r,
  paco6 gf (upaco6 gf r) <6= paco6 gf r.
Proof.
  apply _paco6_mult_strong.
Qed.

Corollary paco6_mult: forall r,
  paco6 gf (paco6 gf r) <6= paco6 gf r.
Proof. intros; eapply paco6_mult_strong, paco6_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco6_fold: forall r,
  gf (upaco6 gf r) <6= paco6 gf r.
Proof.
  apply _paco6_fold.
Qed.

Theorem paco6_unfold: forall (MON: monotone6 gf) r,
  paco6 gf r <6= gf (upaco6 gf r).
Proof.
  intro. eapply _paco6_unfold; apply monotone6_eq; assumption.
Qed.

End Arg6.

Arguments paco6_acc : clear implicits.
Arguments paco6_mon : clear implicits.
Arguments upaco6_mon : clear implicits.
Arguments paco6_mult_strong : clear implicits.
Arguments paco6_mult : clear implicits.
Arguments paco6_fold : clear implicits.
Arguments paco6_unfold : clear implicits.

Global Instance paco6_inst  (gf : rel6 T0 T1 T2 T3 T4 T5->_) r x0 x1 x2 x3 x4 x5 : paco_class (paco6 gf r x0 x1 x2 x3 x4 x5) :=
{ pacoacc    := paco6_acc gf;
  pacomult   := paco6_mult gf;
  pacofold   := paco6_fold gf;
  pacounfold := paco6_unfold gf }.

End PACO6.

Global Opaque paco6.

Hint Unfold upaco6.
Hint Resolve paco6_fold.
Hint Unfold monotone6.

