Require Export paconotation.
Require Import paconotation_internal pacotac_internal paco_internal.
Set Implicit Arguments.

Section PACO4.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.

(** ** Signatures *)

Record sig4T  :=
  exist4T {
      proj4T0: @T0;
      proj4T1: @T1 proj4T0;
      proj4T2: @T2 proj4T0 proj4T1;
      proj4T3: @T3 proj4T0 proj4T1 proj4T2;
    }.
Definition uncurry4  (R: rel4 T0 T1 T2 T3): rel1 sig4T :=
  fun x => R (proj4T0 x) (proj4T1 x) (proj4T2 x) (proj4T3 x).
Definition curry4  (R: rel1 sig4T): rel4 T0 T1 T2 T3 :=
  fun x0 x1 x2 x3 => R (exist4T x3).

Lemma uncurry_map4 r0 r1 (LE : r0 <4== r1) : uncurry4 r0 <1== uncurry4 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev4 r0 r1 (LE: uncurry4 r0 <1== uncurry4 r1) : r0 <4== r1.
Proof.
  repeat_intros 4. intros H. apply (LE (exist4T x3) H).
Qed.

Lemma curry_map4 r0 r1 (LE: r0 <1== r1) : curry4 r0 <4== curry4 r1.
Proof. 
  repeat_intros 4. intros H. apply (LE (exist4T x3) H).
Qed.

Lemma curry_map_rev4 r0 r1 (LE: curry4 r0 <4== curry4 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_4 r : curry4 (uncurry4 r) <4== r.
Proof. unfold le4. repeat_intros 4. intros H. apply H. Qed.

Lemma uncurry_bij2_4 r : r <4== curry4 (uncurry4 r).
Proof. unfold le4. repeat_intros 4. intros H. apply H. Qed.

Lemma curry_bij1_4 r : uncurry4 (curry4 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_4 r : r <1== uncurry4 (curry4 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_4 r0 r1 (LE: uncurry4 r0 <1== r1) : r0 <4== curry4 r1.
Proof.
  apply uncurry_map_rev4. eapply le1_trans; [apply LE|]. apply curry_bij2_4.
Qed.

Lemma uncurry_adjoint2_4 r0 r1 (LE: r0 <4== curry4 r1) : uncurry4 r0 <1== r1.
Proof.
  apply curry_map_rev4. eapply le4_trans; [|apply LE]. apply uncurry_bij2_4.
Qed.

Lemma curry_adjoint1_4 r0 r1 (LE: curry4 r0 <4== r1) : r0 <1== uncurry4 r1.
Proof.
  apply curry_map_rev4. eapply le4_trans; [apply LE|]. apply uncurry_bij2_4.
Qed.

Lemma curry_adjoint2_4 r0 r1 (LE: r0 <1== uncurry4 r1) : curry4 r0 <4== r1.
Proof.
  apply uncurry_map_rev4. eapply le1_trans; [|apply LE]. apply curry_bij1_4.
Qed.

(** ** Predicates of Arity 4
*)

Definition paco4(gf : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3)(r: rel4 T0 T1 T2 T3) : rel4 T0 T1 T2 T3 :=
  curry4 (paco (fun R0 => uncurry4 (gf (curry4 R0))) (uncurry4 r)).

Definition upaco4(gf : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3)(r: rel4 T0 T1 T2 T3) := paco4 gf r \4/ r.
Arguments paco4 : clear implicits.
Arguments upaco4 : clear implicits.
Hint Unfold upaco4.

Definition monotone4 (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :=
  forall x0 x1 x2 x3 r r' (IN: gf r x0 x1 x2 x3) (LE: r <4= r'), gf r' x0 x1 x2 x3.

Definition _monotone4 (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :=
  forall r r'(LE: r <4= r'), gf r <4== gf r'.

Lemma monotone4_eq (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :
  monotone4 gf <-> _monotone4 gf.
Proof. unfold monotone4, _monotone4, le4. split; intros; eapply H; eassumption. Qed.

Lemma monotone4_map (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3)
      (MON: _monotone4 gf) :
  _monotone (fun R0 => uncurry4 (gf (curry4 R0))).
Proof.
  repeat_intros 3. apply uncurry_map4. apply MON; apply curry_map4; assumption.
Qed.

Lemma _paco4_mon_gen (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) r r'
    (LEgf: gf <5= gf')
    (LEr: r <4= r'):
  paco4 gf r <4== paco4 gf' r'.
Proof.
  apply curry_map4. red; intros. eapply paco_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma paco4_mon_gen (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) r r' x0 x1 x2 x3
    (REL: paco4 gf r x0 x1 x2 x3)
    (LEgf: gf <5= gf')
    (LEr: r <4= r'):
  paco4 gf' r' x0 x1 x2 x3.
Proof.
  eapply _paco4_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma paco4_mon_bot (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) r' x0 x1 x2 x3
    (REL: paco4 gf bot4 x0 x1 x2 x3)
    (LEgf: gf <5= gf'):
  paco4 gf' r' x0 x1 x2 x3.
Proof.
  eapply paco4_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upaco4_mon_gen (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) r r' x0 x1 x2 x3
    (REL: upaco4 gf r x0 x1 x2 x3)
    (LEgf: gf <5= gf')
    (LEr: r <4= r'):
  upaco4 gf' r' x0 x1 x2 x3.
Proof.
  destruct REL.
  - left. eapply paco4_mon_gen; [apply H | apply LEgf | apply LEr].
  - right. apply LEr, H.
Qed.

Lemma upaco4_mon_bot (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) r' x0 x1 x2 x3
    (REL: upaco4 gf bot4 x0 x1 x2 x3)
    (LEgf: gf <5= gf'):
  upaco4 gf' r' x0 x1 x2 x3.
Proof.
  eapply upaco4_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Section Arg4.

Variable gf : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3.
Arguments gf : clear implicits.

Theorem _paco4_mon: _monotone4 (paco4 gf).
Proof.
  repeat_intros 3. eapply curry_map4, _paco_mon; apply uncurry_map4; assumption.
Qed.

Theorem _paco4_acc: forall
  l r (OBG: forall rr (INC: r <4== rr) (CIH: l <4== rr), l <4== paco4 gf rr),
  l <4== paco4 gf r.
Proof.
  intros. apply uncurry_adjoint1_4.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_4 in INC. apply uncurry_adjoint1_4 in CIH.
  apply uncurry_adjoint2_4.
  eapply le4_trans. eapply (OBG _ INC CIH).
  apply curry_map4.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_4.
Qed.

Theorem _paco4_mult_strong: forall r,
  paco4 gf (upaco4 gf r) <4== paco4 gf r.
Proof.
  intros. apply curry_map4.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco4_fold: forall r,
  gf (upaco4 gf r) <4== paco4 gf r.
Proof.
  intros. apply uncurry_adjoint1_4.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco4_unfold: forall (MON: _monotone4 gf) r,
  paco4 gf r <4== gf (upaco4 gf r).
Proof.
  intros. apply curry_adjoint2_4.
  eapply _paco_unfold; apply monotone4_map; assumption.
Qed.

Theorem _paco4_algebra (MON: _monotone4 gf) r :
  r <4== gf r -> r <4== paco4 gf bot4.
Proof.
  intros. apply uncurry_adjoint1_4.
  apply _paco_algebra.
  apply monotone4_map; assumption.
  apply curry_adjoint1_4.
  apply H.
Qed.

Theorem paco4_acc: forall
  l r (OBG: forall rr (INC: r <4= rr) (CIH: l <4= rr), l <4= paco4 gf rr),
  l <4= paco4 gf r.
Proof.
  apply _paco4_acc.
Qed.

Theorem paco4_mon: monotone4 (paco4 gf).
Proof.
  apply monotone4_eq.
  apply _paco4_mon.
Qed.

Theorem upaco4_mon: monotone4 (upaco4 gf).
Proof.
  repeat_intros 6. intros R  LE0.
  destruct R.
  - left. eapply paco4_mon. apply H. apply LE0.
  - right. apply LE0, H.
Qed.

Theorem paco4_mult_strong: forall r,
  paco4 gf (upaco4 gf r) <4= paco4 gf r.
Proof.
  apply _paco4_mult_strong.
Qed.

Corollary paco4_mult: forall r,
  paco4 gf (paco4 gf r) <4= paco4 gf r.
Proof. intros; eapply paco4_mult_strong, paco4_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco4_fold: forall r,
  gf (upaco4 gf r) <4= paco4 gf r.
Proof.
  apply _paco4_fold.
Qed.

Theorem paco4_unfold: forall (MON: monotone4 gf) r,
  paco4 gf r <4= gf (upaco4 gf r).
Proof.
  repeat_intros 1. eapply _paco4_unfold; apply monotone4_eq; assumption.
Qed.

Theorem paco4_algebra r (MON: monotone4 gf) :
  r <4= gf r -> r <4= paco4 gf bot4.
Proof.
  repeat_intros 1. eapply _paco4_algebra. apply monotone4_eq; assumption.
  repeat intro. apply x0, PR.
Qed.

End Arg4.

Arguments paco4_acc : clear implicits.
Arguments paco4_mon : clear implicits.
Arguments upaco4_mon : clear implicits.
Arguments paco4_mult_strong : clear implicits.
Arguments paco4_mult : clear implicits.
Arguments paco4_fold : clear implicits.
Arguments paco4_unfold : clear implicits.

Global Instance paco4_inst  (gf : rel4 T0 T1 T2 T3->_) r x0 x1 x2 x3 : paco_class (paco4 gf r x0 x1 x2 x3) :=
{ pacoacc    := paco4_acc gf;
  pacomult   := paco4_mult gf;
  pacofold   := paco4_fold gf;
  pacounfold := paco4_unfold gf }.

End PACO4.

Global Opaque paco4.

Hint Unfold upaco4.
Hint Resolve paco4_fold.
Hint Unfold monotone4.

