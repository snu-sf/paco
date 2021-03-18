From Paco Require Import hpattern.
From Paco Require Export paconotation_internal paconotation.
Set Implicit Arguments.

(** * Tactic support for [paco] library

    This file defines tactics for converting the conclusion to the right form so
    that the accumulation lemmas can be usefully applied. These tactics are used
    in both internal and external approaches.

    Our main tactic, [pcofix], is defined at the end of the file and
    works for predicates of arity up to 14.
*)

(** ** Internal tactics *)

Inductive _paco_mark := _paco_mark_cons.

Inductive _paco_foo := _paco_foo_cons.

Definition _paco_id {A} (a : A) : A := a.

Ltac paco_generalize_hyp mark :=
  let y := fresh "_paco_rel_" in
  match goal with
  | [x: ?A |- _] =>
    match A with
    | mark => clear x
    | _ => intro y;
      match type of y with
        | context[x] => revert x y;
          match goal with [|-forall x, @?f x -> _] =>
            intros x y; generalize (ex_intro f x y)
          end
        | _ => generalize (conj (ex_intro _ x _paco_foo_cons) y)
      end; clear x y; paco_generalize_hyp mark
    end
  end.

Ltac paco_destruct_hyp mark :=
  match goal with
  | [x: ?A |- _] =>
    match A with
    | mark => idtac
    | _paco_foo => clear x; paco_destruct_hyp mark
    | exists n, ?p => let n' := fresh n in destruct x as (n', x); paco_destruct_hyp mark
    | ?p /\ ?q => let x' := fresh x in destruct x as (x,x'); paco_destruct_hyp mark
    end
  end.

Ltac paco_revert_hyp mark :=
  match goal with [x: ?A |- _] =>
  match A with
    | mark => clear x
    | _ => revert x; paco_revert_hyp mark
  end end.

Ltac paco_post_var INC pr cr := let TMP := fresh "_paco_tmp_" in
  repeat (
    match goal with [H: context f [pr] |-_] =>
      let cih := context f [cr] in rename H into TMP;
      assert(H : cih) by (repeat intro; eapply INC, TMP; eassumption); clear TMP
    end);
  clear INC pr.

Ltac paco_rename_last :=
  let x := fresh "_paco_xxx_" in match goal with [H: _|-_] => rename H into x end.

Ltac paco_simp_hyp CIH :=
  let EP := fresh "_paco_EP_" in
  let FP := fresh "_paco_FF_" in
  let TP := fresh "_paco_TP_" in
  let XP := fresh "_paco_XP_" in
  let PP := type of CIH in
  evar (EP: Prop);
  assert (TP: False -> PP) by (
    intros FP; generalize _paco_mark_cons;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_revert_hyp _paco_mark;
    let con := get_concl in set (TP:=con); revert EP; instantiate (1:= con); destruct FP);
  clear TP;
  assert (XP: EP) by (unfold EP; clear -CIH; repeat intro; apply CIH;
    first [
      (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       try (reflexivity);
       first [eassumption|apply _paco_foo_cons]); fail
    | (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       (try unfold _paco_id); eauto using _paco_foo_cons)]);
  unfold EP in *; clear EP CIH; rename XP into CIH.

Ltac paco_post_simp CIH :=
  let CIH := fresh CIH in
  intro CIH; paco_simp_hyp CIH;
  first [try(match goal with [ |- context[_paco_id] ] => fail 2 | [ |- context[_paco_foo] ] => fail 2 end) |
    let TMP := fresh "_paco_TMP_" in
    generalize _paco_mark_cons; intro TMP;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_revert_hyp _paco_mark
  ].

Ltac paco_ren_r nr cr :=
  first [rename cr into nr | let nr := fresh nr in rename cr into nr].

Ltac paco_ren_pr pr cr := rename cr into pr.

Ltac paco_revert :=
  match goal with [H: _ |- _] => revert H end.

Section SIG0.


(** ** Signatures *)

Record sig0T  :=
  exist0T {
    }.
Definition uncurry0  (R: rel0): rel1 sig0T :=
  fun x => R.
Definition curry0  (R: rel1 sig0T): rel0 :=
   R (@exist0T).

Lemma uncurry_map0 r0 r1 (LE : r0 <0== r1) : uncurry0 r0 <1== uncurry0 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev0 r0 r1 (LE: uncurry0 r0 <1== uncurry0 r1) : r0 <0== r1.
Proof.
  red; intros. apply (LE (@exist0T) PR).
Qed.

Lemma curry_map0 r0 r1 (LE: r0 <1== r1) : curry0 r0 <0== curry0 r1.
Proof. 
  red; intros. apply (LE (@exist0T) PR).
Qed.

Lemma curry_map_rev0 r0 r1 (LE: curry0 r0 <0== curry0 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_0 r : curry0 (uncurry0 r) <0== r.
Proof. unfold le0. intros. apply PR. Qed.

Lemma uncurry_bij2_0 r : r <0== curry0 (uncurry0 r).
Proof. unfold le0. intros. apply PR. Qed.

Lemma curry_bij1_0 r : uncurry0 (curry0 r) <1== r.
Proof. intros [] H. apply H. Qed.

Lemma curry_bij2_0 r : r <1== uncurry0 (curry0 r).
Proof. intros [] H. apply H. Qed.

Lemma uncurry_adjoint1_0 r0 r1 (LE: uncurry0 r0 <1== r1) : r0 <0== curry0 r1.
Proof.
  apply uncurry_map_rev0. eapply le1_trans; [apply LE|]. apply curry_bij2_0.
Qed.

Lemma uncurry_adjoint2_0 r0 r1 (LE: r0 <0== curry0 r1) : uncurry0 r0 <1== r1.
Proof.
  apply curry_map_rev0. eapply le0_trans; [|apply LE]. apply uncurry_bij2_0.
Qed.

Lemma curry_adjoint1_0 r0 r1 (LE: curry0 r0 <0== r1) : r0 <1== uncurry0 r1.
Proof.
  apply curry_map_rev0. eapply le0_trans; [apply LE|]. apply uncurry_bij2_0.
Qed.

Lemma curry_adjoint2_0 r0 r1 (LE: r0 <1== uncurry0 r1) : curry0 r0 <0== r1.
Proof.
  apply uncurry_map_rev0. eapply le1_trans; [|apply LE]. apply curry_bij1_0.
Qed.

End SIG0.
Section SIG1.

Variable T0 : Type.

(** ** Signatures *)

Record sig1T  :=
  exist1T {
      proj1T0: @T0;
    }.
Definition uncurry1  (R: rel1 T0): rel1 sig1T :=
  fun x => R (proj1T0 x).
Definition curry1  (R: rel1 sig1T): rel1 T0 :=
  fun x0 => R (@exist1T x0).

Lemma uncurry_map1 r0 r1 (LE : r0 <1== r1) : uncurry1 r0 <1== uncurry1 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev1 r0 r1 (LE: uncurry1 r0 <1== uncurry1 r1) : r0 <1== r1.
Proof.
  red; intros. apply (LE (@exist1T x0) PR).
Qed.

Lemma curry_map1 r0 r1 (LE: r0 <1== r1) : curry1 r0 <1== curry1 r1.
Proof. 
  red; intros. apply (LE (@exist1T x0) PR).
Qed.

Lemma curry_map_rev1 r0 r1 (LE: curry1 r0 <1== curry1 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_1 r : curry1 (uncurry1 r) <1== r.
Proof. unfold le1. intros. apply PR. Qed.

Lemma uncurry_bij2_1 r : r <1== curry1 (uncurry1 r).
Proof. unfold le1. intros. apply PR. Qed.

Lemma curry_bij1_1 r : uncurry1 (curry1 r) <1== r.
Proof. intros [] H. apply H. Qed.

Lemma curry_bij2_1 r : r <1== uncurry1 (curry1 r).
Proof. intros [] H. apply H. Qed.

Lemma uncurry_adjoint1_1 r0 r1 (LE: uncurry1 r0 <1== r1) : r0 <1== curry1 r1.
Proof.
  apply uncurry_map_rev1. eapply le1_trans; [apply LE|]. apply curry_bij2_1.
Qed.

Lemma uncurry_adjoint2_1 r0 r1 (LE: r0 <1== curry1 r1) : uncurry1 r0 <1== r1.
Proof.
  apply curry_map_rev1. eapply le1_trans; [|apply LE]. apply uncurry_bij2_1.
Qed.

Lemma curry_adjoint1_1 r0 r1 (LE: curry1 r0 <1== r1) : r0 <1== uncurry1 r1.
Proof.
  apply curry_map_rev1. eapply le1_trans; [apply LE|]. apply uncurry_bij2_1.
Qed.

Lemma curry_adjoint2_1 r0 r1 (LE: r0 <1== uncurry1 r1) : curry1 r0 <1== r1.
Proof.
  apply uncurry_map_rev1. eapply le1_trans; [|apply LE]. apply curry_bij1_1.
Qed.

End SIG1.
Section SIG2.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.

(** ** Signatures *)

Record sig2T  :=
  exist2T {
      proj2T0: @T0;
      proj2T1: @T1 proj2T0;
    }.
Definition uncurry2  (R: rel2 T0 T1): rel1 sig2T :=
  fun x => R (proj2T0 x) (proj2T1 x).
Definition curry2  (R: rel1 sig2T): rel2 T0 T1 :=
  fun x0 x1 => R (@exist2T x0 x1).

Lemma uncurry_map2 r0 r1 (LE : r0 <2== r1) : uncurry2 r0 <1== uncurry2 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev2 r0 r1 (LE: uncurry2 r0 <1== uncurry2 r1) : r0 <2== r1.
Proof.
  red; intros. apply (LE (@exist2T x0 x1) PR).
Qed.

Lemma curry_map2 r0 r1 (LE: r0 <1== r1) : curry2 r0 <2== curry2 r1.
Proof. 
  red; intros. apply (LE (@exist2T x0 x1) PR).
Qed.

Lemma curry_map_rev2 r0 r1 (LE: curry2 r0 <2== curry2 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_2 r : curry2 (uncurry2 r) <2== r.
Proof. unfold le2. intros. apply PR. Qed.

Lemma uncurry_bij2_2 r : r <2== curry2 (uncurry2 r).
Proof. unfold le2. intros. apply PR. Qed.

Lemma curry_bij1_2 r : uncurry2 (curry2 r) <1== r.
Proof. intros [] H. apply H. Qed.

Lemma curry_bij2_2 r : r <1== uncurry2 (curry2 r).
Proof. intros [] H. apply H. Qed.

Lemma uncurry_adjoint1_2 r0 r1 (LE: uncurry2 r0 <1== r1) : r0 <2== curry2 r1.
Proof.
  apply uncurry_map_rev2. eapply le1_trans; [apply LE|]. apply curry_bij2_2.
Qed.

Lemma uncurry_adjoint2_2 r0 r1 (LE: r0 <2== curry2 r1) : uncurry2 r0 <1== r1.
Proof.
  apply curry_map_rev2. eapply le2_trans; [|apply LE]. apply uncurry_bij2_2.
Qed.

Lemma curry_adjoint1_2 r0 r1 (LE: curry2 r0 <2== r1) : r0 <1== uncurry2 r1.
Proof.
  apply curry_map_rev2. eapply le2_trans; [apply LE|]. apply uncurry_bij2_2.
Qed.

Lemma curry_adjoint2_2 r0 r1 (LE: r0 <1== uncurry2 r1) : curry2 r0 <2== r1.
Proof.
  apply uncurry_map_rev2. eapply le1_trans; [|apply LE]. apply curry_bij1_2.
Qed.

End SIG2.
Section SIG3.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.

(** ** Signatures *)

Record sig3T  :=
  exist3T {
      proj3T0: @T0;
      proj3T1: @T1 proj3T0;
      proj3T2: @T2 proj3T0 proj3T1;
    }.
Definition uncurry3  (R: rel3 T0 T1 T2): rel1 sig3T :=
  fun x => R (proj3T0 x) (proj3T1 x) (proj3T2 x).
Definition curry3  (R: rel1 sig3T): rel3 T0 T1 T2 :=
  fun x0 x1 x2 => R (@exist3T x0 x1 x2).

Lemma uncurry_map3 r0 r1 (LE : r0 <3== r1) : uncurry3 r0 <1== uncurry3 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev3 r0 r1 (LE: uncurry3 r0 <1== uncurry3 r1) : r0 <3== r1.
Proof.
  red; intros. apply (LE (@exist3T x0 x1 x2) PR).
Qed.

Lemma curry_map3 r0 r1 (LE: r0 <1== r1) : curry3 r0 <3== curry3 r1.
Proof. 
  red; intros. apply (LE (@exist3T x0 x1 x2) PR).
Qed.

Lemma curry_map_rev3 r0 r1 (LE: curry3 r0 <3== curry3 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_3 r : curry3 (uncurry3 r) <3== r.
Proof. unfold le3. intros. apply PR. Qed.

Lemma uncurry_bij2_3 r : r <3== curry3 (uncurry3 r).
Proof. unfold le3. intros. apply PR. Qed.

Lemma curry_bij1_3 r : uncurry3 (curry3 r) <1== r.
Proof. intros [] H. apply H. Qed.

Lemma curry_bij2_3 r : r <1== uncurry3 (curry3 r).
Proof. intros [] H. apply H. Qed.

Lemma uncurry_adjoint1_3 r0 r1 (LE: uncurry3 r0 <1== r1) : r0 <3== curry3 r1.
Proof.
  apply uncurry_map_rev3. eapply le1_trans; [apply LE|]. apply curry_bij2_3.
Qed.

Lemma uncurry_adjoint2_3 r0 r1 (LE: r0 <3== curry3 r1) : uncurry3 r0 <1== r1.
Proof.
  apply curry_map_rev3. eapply le3_trans; [|apply LE]. apply uncurry_bij2_3.
Qed.

Lemma curry_adjoint1_3 r0 r1 (LE: curry3 r0 <3== r1) : r0 <1== uncurry3 r1.
Proof.
  apply curry_map_rev3. eapply le3_trans; [apply LE|]. apply uncurry_bij2_3.
Qed.

Lemma curry_adjoint2_3 r0 r1 (LE: r0 <1== uncurry3 r1) : curry3 r0 <3== r1.
Proof.
  apply uncurry_map_rev3. eapply le1_trans; [|apply LE]. apply curry_bij1_3.
Qed.

End SIG3.
Section SIG4.

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
  fun x0 x1 x2 x3 => R (@exist4T x0 x1 x2 x3).

Lemma uncurry_map4 r0 r1 (LE : r0 <4== r1) : uncurry4 r0 <1== uncurry4 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev4 r0 r1 (LE: uncurry4 r0 <1== uncurry4 r1) : r0 <4== r1.
Proof.
  red; intros. apply (LE (@exist4T x0 x1 x2 x3) PR).
Qed.

Lemma curry_map4 r0 r1 (LE: r0 <1== r1) : curry4 r0 <4== curry4 r1.
Proof. 
  red; intros. apply (LE (@exist4T x0 x1 x2 x3) PR).
Qed.

Lemma curry_map_rev4 r0 r1 (LE: curry4 r0 <4== curry4 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_4 r : curry4 (uncurry4 r) <4== r.
Proof. unfold le4. intros. apply PR. Qed.

Lemma uncurry_bij2_4 r : r <4== curry4 (uncurry4 r).
Proof. unfold le4. intros. apply PR. Qed.

Lemma curry_bij1_4 r : uncurry4 (curry4 r) <1== r.
Proof. intros [] H. apply H. Qed.

Lemma curry_bij2_4 r : r <1== uncurry4 (curry4 r).
Proof. intros [] H. apply H. Qed.

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

End SIG4.
Section SIG5.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.

(** ** Signatures *)

Record sig5T  :=
  exist5T {
      proj5T0: @T0;
      proj5T1: @T1 proj5T0;
      proj5T2: @T2 proj5T0 proj5T1;
      proj5T3: @T3 proj5T0 proj5T1 proj5T2;
      proj5T4: @T4 proj5T0 proj5T1 proj5T2 proj5T3;
    }.
Definition uncurry5  (R: rel5 T0 T1 T2 T3 T4): rel1 sig5T :=
  fun x => R (proj5T0 x) (proj5T1 x) (proj5T2 x) (proj5T3 x) (proj5T4 x).
Definition curry5  (R: rel1 sig5T): rel5 T0 T1 T2 T3 T4 :=
  fun x0 x1 x2 x3 x4 => R (@exist5T x0 x1 x2 x3 x4).

Lemma uncurry_map5 r0 r1 (LE : r0 <5== r1) : uncurry5 r0 <1== uncurry5 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev5 r0 r1 (LE: uncurry5 r0 <1== uncurry5 r1) : r0 <5== r1.
Proof.
  red; intros. apply (LE (@exist5T x0 x1 x2 x3 x4) PR).
Qed.

Lemma curry_map5 r0 r1 (LE: r0 <1== r1) : curry5 r0 <5== curry5 r1.
Proof. 
  red; intros. apply (LE (@exist5T x0 x1 x2 x3 x4) PR).
Qed.

Lemma curry_map_rev5 r0 r1 (LE: curry5 r0 <5== curry5 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_5 r : curry5 (uncurry5 r) <5== r.
Proof. unfold le5. intros. apply PR. Qed.

Lemma uncurry_bij2_5 r : r <5== curry5 (uncurry5 r).
Proof. unfold le5. intros. apply PR. Qed.

Lemma curry_bij1_5 r : uncurry5 (curry5 r) <1== r.
Proof. intros [] H. apply H. Qed.

Lemma curry_bij2_5 r : r <1== uncurry5 (curry5 r).
Proof. intros [] H. apply H. Qed.

Lemma uncurry_adjoint1_5 r0 r1 (LE: uncurry5 r0 <1== r1) : r0 <5== curry5 r1.
Proof.
  apply uncurry_map_rev5. eapply le1_trans; [apply LE|]. apply curry_bij2_5.
Qed.

Lemma uncurry_adjoint2_5 r0 r1 (LE: r0 <5== curry5 r1) : uncurry5 r0 <1== r1.
Proof.
  apply curry_map_rev5. eapply le5_trans; [|apply LE]. apply uncurry_bij2_5.
Qed.

Lemma curry_adjoint1_5 r0 r1 (LE: curry5 r0 <5== r1) : r0 <1== uncurry5 r1.
Proof.
  apply curry_map_rev5. eapply le5_trans; [apply LE|]. apply uncurry_bij2_5.
Qed.

Lemma curry_adjoint2_5 r0 r1 (LE: r0 <1== uncurry5 r1) : curry5 r0 <5== r1.
Proof.
  apply uncurry_map_rev5. eapply le1_trans; [|apply LE]. apply curry_bij1_5.
Qed.

End SIG5.
Section SIG6.

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
Proof. intros [] H. apply H. Qed.

Lemma curry_bij2_6 r : r <1== uncurry6 (curry6 r).
Proof. intros [] H. apply H. Qed.

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

End SIG6.
Section SIG7.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.

(** ** Signatures *)

Record sig7T  :=
  exist7T {
      proj7T0: @T0;
      proj7T1: @T1 proj7T0;
      proj7T2: @T2 proj7T0 proj7T1;
      proj7T3: @T3 proj7T0 proj7T1 proj7T2;
      proj7T4: @T4 proj7T0 proj7T1 proj7T2 proj7T3;
      proj7T5: @T5 proj7T0 proj7T1 proj7T2 proj7T3 proj7T4;
      proj7T6: @T6 proj7T0 proj7T1 proj7T2 proj7T3 proj7T4 proj7T5;
    }.
Definition uncurry7  (R: rel7 T0 T1 T2 T3 T4 T5 T6): rel1 sig7T :=
  fun x => R (proj7T0 x) (proj7T1 x) (proj7T2 x) (proj7T3 x) (proj7T4 x) (proj7T5 x) (proj7T6 x).
Definition curry7  (R: rel1 sig7T): rel7 T0 T1 T2 T3 T4 T5 T6 :=
  fun x0 x1 x2 x3 x4 x5 x6 => R (@exist7T x0 x1 x2 x3 x4 x5 x6).

Lemma uncurry_map7 r0 r1 (LE : r0 <7== r1) : uncurry7 r0 <1== uncurry7 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev7 r0 r1 (LE: uncurry7 r0 <1== uncurry7 r1) : r0 <7== r1.
Proof.
  red; intros. apply (LE (@exist7T x0 x1 x2 x3 x4 x5 x6) PR).
Qed.

Lemma curry_map7 r0 r1 (LE: r0 <1== r1) : curry7 r0 <7== curry7 r1.
Proof. 
  red; intros. apply (LE (@exist7T x0 x1 x2 x3 x4 x5 x6) PR).
Qed.

Lemma curry_map_rev7 r0 r1 (LE: curry7 r0 <7== curry7 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_7 r : curry7 (uncurry7 r) <7== r.
Proof. unfold le7. intros. apply PR. Qed.

Lemma uncurry_bij2_7 r : r <7== curry7 (uncurry7 r).
Proof. unfold le7. intros. apply PR. Qed.

Lemma curry_bij1_7 r : uncurry7 (curry7 r) <1== r.
Proof. intros [] H. apply H. Qed.

Lemma curry_bij2_7 r : r <1== uncurry7 (curry7 r).
Proof. intros [] H. apply H. Qed.

Lemma uncurry_adjoint1_7 r0 r1 (LE: uncurry7 r0 <1== r1) : r0 <7== curry7 r1.
Proof.
  apply uncurry_map_rev7. eapply le1_trans; [apply LE|]. apply curry_bij2_7.
Qed.

Lemma uncurry_adjoint2_7 r0 r1 (LE: r0 <7== curry7 r1) : uncurry7 r0 <1== r1.
Proof.
  apply curry_map_rev7. eapply le7_trans; [|apply LE]. apply uncurry_bij2_7.
Qed.

Lemma curry_adjoint1_7 r0 r1 (LE: curry7 r0 <7== r1) : r0 <1== uncurry7 r1.
Proof.
  apply curry_map_rev7. eapply le7_trans; [apply LE|]. apply uncurry_bij2_7.
Qed.

Lemma curry_adjoint2_7 r0 r1 (LE: r0 <1== uncurry7 r1) : curry7 r0 <7== r1.
Proof.
  apply uncurry_map_rev7. eapply le1_trans; [|apply LE]. apply curry_bij1_7.
Qed.

End SIG7.
Section SIG8.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.

(** ** Signatures *)

Record sig8T  :=
  exist8T {
      proj8T0: @T0;
      proj8T1: @T1 proj8T0;
      proj8T2: @T2 proj8T0 proj8T1;
      proj8T3: @T3 proj8T0 proj8T1 proj8T2;
      proj8T4: @T4 proj8T0 proj8T1 proj8T2 proj8T3;
      proj8T5: @T5 proj8T0 proj8T1 proj8T2 proj8T3 proj8T4;
      proj8T6: @T6 proj8T0 proj8T1 proj8T2 proj8T3 proj8T4 proj8T5;
      proj8T7: @T7 proj8T0 proj8T1 proj8T2 proj8T3 proj8T4 proj8T5 proj8T6;
    }.
Definition uncurry8  (R: rel8 T0 T1 T2 T3 T4 T5 T6 T7): rel1 sig8T :=
  fun x => R (proj8T0 x) (proj8T1 x) (proj8T2 x) (proj8T3 x) (proj8T4 x) (proj8T5 x) (proj8T6 x) (proj8T7 x).
Definition curry8  (R: rel1 sig8T): rel8 T0 T1 T2 T3 T4 T5 T6 T7 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 => R (@exist8T x0 x1 x2 x3 x4 x5 x6 x7).

Lemma uncurry_map8 r0 r1 (LE : r0 <8== r1) : uncurry8 r0 <1== uncurry8 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev8 r0 r1 (LE: uncurry8 r0 <1== uncurry8 r1) : r0 <8== r1.
Proof.
  red; intros. apply (LE (@exist8T x0 x1 x2 x3 x4 x5 x6 x7) PR).
Qed.

Lemma curry_map8 r0 r1 (LE: r0 <1== r1) : curry8 r0 <8== curry8 r1.
Proof. 
  red; intros. apply (LE (@exist8T x0 x1 x2 x3 x4 x5 x6 x7) PR).
Qed.

Lemma curry_map_rev8 r0 r1 (LE: curry8 r0 <8== curry8 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_8 r : curry8 (uncurry8 r) <8== r.
Proof. unfold le8. intros. apply PR. Qed.

Lemma uncurry_bij2_8 r : r <8== curry8 (uncurry8 r).
Proof. unfold le8. intros. apply PR. Qed.

Lemma curry_bij1_8 r : uncurry8 (curry8 r) <1== r.
Proof. intros [] H. apply H. Qed.

Lemma curry_bij2_8 r : r <1== uncurry8 (curry8 r).
Proof. intros [] H. apply H. Qed.

Lemma uncurry_adjoint1_8 r0 r1 (LE: uncurry8 r0 <1== r1) : r0 <8== curry8 r1.
Proof.
  apply uncurry_map_rev8. eapply le1_trans; [apply LE|]. apply curry_bij2_8.
Qed.

Lemma uncurry_adjoint2_8 r0 r1 (LE: r0 <8== curry8 r1) : uncurry8 r0 <1== r1.
Proof.
  apply curry_map_rev8. eapply le8_trans; [|apply LE]. apply uncurry_bij2_8.
Qed.

Lemma curry_adjoint1_8 r0 r1 (LE: curry8 r0 <8== r1) : r0 <1== uncurry8 r1.
Proof.
  apply curry_map_rev8. eapply le8_trans; [apply LE|]. apply uncurry_bij2_8.
Qed.

Lemma curry_adjoint2_8 r0 r1 (LE: r0 <1== uncurry8 r1) : curry8 r0 <8== r1.
Proof.
  apply uncurry_map_rev8. eapply le1_trans; [|apply LE]. apply curry_bij1_8.
Qed.

End SIG8.
Section SIG9.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.

(** ** Signatures *)

Record sig9T  :=
  exist9T {
      proj9T0: @T0;
      proj9T1: @T1 proj9T0;
      proj9T2: @T2 proj9T0 proj9T1;
      proj9T3: @T3 proj9T0 proj9T1 proj9T2;
      proj9T4: @T4 proj9T0 proj9T1 proj9T2 proj9T3;
      proj9T5: @T5 proj9T0 proj9T1 proj9T2 proj9T3 proj9T4;
      proj9T6: @T6 proj9T0 proj9T1 proj9T2 proj9T3 proj9T4 proj9T5;
      proj9T7: @T7 proj9T0 proj9T1 proj9T2 proj9T3 proj9T4 proj9T5 proj9T6;
      proj9T8: @T8 proj9T0 proj9T1 proj9T2 proj9T3 proj9T4 proj9T5 proj9T6 proj9T7;
    }.
Definition uncurry9  (R: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8): rel1 sig9T :=
  fun x => R (proj9T0 x) (proj9T1 x) (proj9T2 x) (proj9T3 x) (proj9T4 x) (proj9T5 x) (proj9T6 x) (proj9T7 x) (proj9T8 x).
Definition curry9  (R: rel1 sig9T): rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 => R (@exist9T x0 x1 x2 x3 x4 x5 x6 x7 x8).

Lemma uncurry_map9 r0 r1 (LE : r0 <9== r1) : uncurry9 r0 <1== uncurry9 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev9 r0 r1 (LE: uncurry9 r0 <1== uncurry9 r1) : r0 <9== r1.
Proof.
  red; intros. apply (LE (@exist9T x0 x1 x2 x3 x4 x5 x6 x7 x8) PR).
Qed.

Lemma curry_map9 r0 r1 (LE: r0 <1== r1) : curry9 r0 <9== curry9 r1.
Proof. 
  red; intros. apply (LE (@exist9T x0 x1 x2 x3 x4 x5 x6 x7 x8) PR).
Qed.

Lemma curry_map_rev9 r0 r1 (LE: curry9 r0 <9== curry9 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_9 r : curry9 (uncurry9 r) <9== r.
Proof. unfold le9. intros. apply PR. Qed.

Lemma uncurry_bij2_9 r : r <9== curry9 (uncurry9 r).
Proof. unfold le9. intros. apply PR. Qed.

Lemma curry_bij1_9 r : uncurry9 (curry9 r) <1== r.
Proof. intros [] H. apply H. Qed.

Lemma curry_bij2_9 r : r <1== uncurry9 (curry9 r).
Proof. intros [] H. apply H. Qed.

Lemma uncurry_adjoint1_9 r0 r1 (LE: uncurry9 r0 <1== r1) : r0 <9== curry9 r1.
Proof.
  apply uncurry_map_rev9. eapply le1_trans; [apply LE|]. apply curry_bij2_9.
Qed.

Lemma uncurry_adjoint2_9 r0 r1 (LE: r0 <9== curry9 r1) : uncurry9 r0 <1== r1.
Proof.
  apply curry_map_rev9. eapply le9_trans; [|apply LE]. apply uncurry_bij2_9.
Qed.

Lemma curry_adjoint1_9 r0 r1 (LE: curry9 r0 <9== r1) : r0 <1== uncurry9 r1.
Proof.
  apply curry_map_rev9. eapply le9_trans; [apply LE|]. apply uncurry_bij2_9.
Qed.

Lemma curry_adjoint2_9 r0 r1 (LE: r0 <1== uncurry9 r1) : curry9 r0 <9== r1.
Proof.
  apply uncurry_map_rev9. eapply le1_trans; [|apply LE]. apply curry_bij1_9.
Qed.

End SIG9.
Section SIG10.

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

(** ** Signatures *)

Record sig10T  :=
  exist10T {
      proj10T0: @T0;
      proj10T1: @T1 proj10T0;
      proj10T2: @T2 proj10T0 proj10T1;
      proj10T3: @T3 proj10T0 proj10T1 proj10T2;
      proj10T4: @T4 proj10T0 proj10T1 proj10T2 proj10T3;
      proj10T5: @T5 proj10T0 proj10T1 proj10T2 proj10T3 proj10T4;
      proj10T6: @T6 proj10T0 proj10T1 proj10T2 proj10T3 proj10T4 proj10T5;
      proj10T7: @T7 proj10T0 proj10T1 proj10T2 proj10T3 proj10T4 proj10T5 proj10T6;
      proj10T8: @T8 proj10T0 proj10T1 proj10T2 proj10T3 proj10T4 proj10T5 proj10T6 proj10T7;
      proj10T9: @T9 proj10T0 proj10T1 proj10T2 proj10T3 proj10T4 proj10T5 proj10T6 proj10T7 proj10T8;
    }.
Definition uncurry10  (R: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9): rel1 sig10T :=
  fun x => R (proj10T0 x) (proj10T1 x) (proj10T2 x) (proj10T3 x) (proj10T4 x) (proj10T5 x) (proj10T6 x) (proj10T7 x) (proj10T8 x) (proj10T9 x).
Definition curry10  (R: rel1 sig10T): rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 => R (@exist10T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9).

Lemma uncurry_map10 r0 r1 (LE : r0 <10== r1) : uncurry10 r0 <1== uncurry10 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev10 r0 r1 (LE: uncurry10 r0 <1== uncurry10 r1) : r0 <10== r1.
Proof.
  red; intros. apply (LE (@exist10T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) PR).
Qed.

Lemma curry_map10 r0 r1 (LE: r0 <1== r1) : curry10 r0 <10== curry10 r1.
Proof. 
  red; intros. apply (LE (@exist10T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) PR).
Qed.

Lemma curry_map_rev10 r0 r1 (LE: curry10 r0 <10== curry10 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_10 r : curry10 (uncurry10 r) <10== r.
Proof. unfold le10. intros. apply PR. Qed.

Lemma uncurry_bij2_10 r : r <10== curry10 (uncurry10 r).
Proof. unfold le10. intros. apply PR. Qed.

Lemma curry_bij1_10 r : uncurry10 (curry10 r) <1== r.
Proof. intros [] H. apply H. Qed.

Lemma curry_bij2_10 r : r <1== uncurry10 (curry10 r).
Proof. intros [] H. apply H. Qed.

Lemma uncurry_adjoint1_10 r0 r1 (LE: uncurry10 r0 <1== r1) : r0 <10== curry10 r1.
Proof.
  apply uncurry_map_rev10. eapply le1_trans; [apply LE|]. apply curry_bij2_10.
Qed.

Lemma uncurry_adjoint2_10 r0 r1 (LE: r0 <10== curry10 r1) : uncurry10 r0 <1== r1.
Proof.
  apply curry_map_rev10. eapply le10_trans; [|apply LE]. apply uncurry_bij2_10.
Qed.

Lemma curry_adjoint1_10 r0 r1 (LE: curry10 r0 <10== r1) : r0 <1== uncurry10 r1.
Proof.
  apply curry_map_rev10. eapply le10_trans; [apply LE|]. apply uncurry_bij2_10.
Qed.

Lemma curry_adjoint2_10 r0 r1 (LE: r0 <1== uncurry10 r1) : curry10 r0 <10== r1.
Proof.
  apply uncurry_map_rev10. eapply le1_trans; [|apply LE]. apply curry_bij1_10.
Qed.

End SIG10.
Section SIG11.

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

(** ** Signatures *)

Record sig11T  :=
  exist11T {
      proj11T0: @T0;
      proj11T1: @T1 proj11T0;
      proj11T2: @T2 proj11T0 proj11T1;
      proj11T3: @T3 proj11T0 proj11T1 proj11T2;
      proj11T4: @T4 proj11T0 proj11T1 proj11T2 proj11T3;
      proj11T5: @T5 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4;
      proj11T6: @T6 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5;
      proj11T7: @T7 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5 proj11T6;
      proj11T8: @T8 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5 proj11T6 proj11T7;
      proj11T9: @T9 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5 proj11T6 proj11T7 proj11T8;
      proj11T10: @T10 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5 proj11T6 proj11T7 proj11T8 proj11T9;
    }.
Definition uncurry11  (R: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10): rel1 sig11T :=
  fun x => R (proj11T0 x) (proj11T1 x) (proj11T2 x) (proj11T3 x) (proj11T4 x) (proj11T5 x) (proj11T6 x) (proj11T7 x) (proj11T8 x) (proj11T9 x) (proj11T10 x).
Definition curry11  (R: rel1 sig11T): rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 => R (@exist11T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10).

Lemma uncurry_map11 r0 r1 (LE : r0 <11== r1) : uncurry11 r0 <1== uncurry11 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev11 r0 r1 (LE: uncurry11 r0 <1== uncurry11 r1) : r0 <11== r1.
Proof.
  red; intros. apply (LE (@exist11T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) PR).
Qed.

Lemma curry_map11 r0 r1 (LE: r0 <1== r1) : curry11 r0 <11== curry11 r1.
Proof. 
  red; intros. apply (LE (@exist11T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) PR).
Qed.

Lemma curry_map_rev11 r0 r1 (LE: curry11 r0 <11== curry11 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_11 r : curry11 (uncurry11 r) <11== r.
Proof. unfold le11. intros. apply PR. Qed.

Lemma uncurry_bij2_11 r : r <11== curry11 (uncurry11 r).
Proof. unfold le11. intros. apply PR. Qed.

Lemma curry_bij1_11 r : uncurry11 (curry11 r) <1== r.
Proof. intros [] H. apply H. Qed.

Lemma curry_bij2_11 r : r <1== uncurry11 (curry11 r).
Proof. intros [] H. apply H. Qed.

Lemma uncurry_adjoint1_11 r0 r1 (LE: uncurry11 r0 <1== r1) : r0 <11== curry11 r1.
Proof.
  apply uncurry_map_rev11. eapply le1_trans; [apply LE|]. apply curry_bij2_11.
Qed.

Lemma uncurry_adjoint2_11 r0 r1 (LE: r0 <11== curry11 r1) : uncurry11 r0 <1== r1.
Proof.
  apply curry_map_rev11. eapply le11_trans; [|apply LE]. apply uncurry_bij2_11.
Qed.

Lemma curry_adjoint1_11 r0 r1 (LE: curry11 r0 <11== r1) : r0 <1== uncurry11 r1.
Proof.
  apply curry_map_rev11. eapply le11_trans; [apply LE|]. apply uncurry_bij2_11.
Qed.

Lemma curry_adjoint2_11 r0 r1 (LE: r0 <1== uncurry11 r1) : curry11 r0 <11== r1.
Proof.
  apply uncurry_map_rev11. eapply le1_trans; [|apply LE]. apply curry_bij1_11.
Qed.

End SIG11.
Section SIG12.

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

(** ** Signatures *)

Record sig12T  :=
  exist12T {
      proj12T0: @T0;
      proj12T1: @T1 proj12T0;
      proj12T2: @T2 proj12T0 proj12T1;
      proj12T3: @T3 proj12T0 proj12T1 proj12T2;
      proj12T4: @T4 proj12T0 proj12T1 proj12T2 proj12T3;
      proj12T5: @T5 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4;
      proj12T6: @T6 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4 proj12T5;
      proj12T7: @T7 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4 proj12T5 proj12T6;
      proj12T8: @T8 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4 proj12T5 proj12T6 proj12T7;
      proj12T9: @T9 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4 proj12T5 proj12T6 proj12T7 proj12T8;
      proj12T10: @T10 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4 proj12T5 proj12T6 proj12T7 proj12T8 proj12T9;
      proj12T11: @T11 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4 proj12T5 proj12T6 proj12T7 proj12T8 proj12T9 proj12T10;
    }.
Definition uncurry12  (R: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11): rel1 sig12T :=
  fun x => R (proj12T0 x) (proj12T1 x) (proj12T2 x) (proj12T3 x) (proj12T4 x) (proj12T5 x) (proj12T6 x) (proj12T7 x) (proj12T8 x) (proj12T9 x) (proj12T10 x) (proj12T11 x).
Definition curry12  (R: rel1 sig12T): rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 => R (@exist12T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11).

Lemma uncurry_map12 r0 r1 (LE : r0 <12== r1) : uncurry12 r0 <1== uncurry12 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev12 r0 r1 (LE: uncurry12 r0 <1== uncurry12 r1) : r0 <12== r1.
Proof.
  red; intros. apply (LE (@exist12T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) PR).
Qed.

Lemma curry_map12 r0 r1 (LE: r0 <1== r1) : curry12 r0 <12== curry12 r1.
Proof. 
  red; intros. apply (LE (@exist12T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) PR).
Qed.

Lemma curry_map_rev12 r0 r1 (LE: curry12 r0 <12== curry12 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_12 r : curry12 (uncurry12 r) <12== r.
Proof. unfold le12. intros. apply PR. Qed.

Lemma uncurry_bij2_12 r : r <12== curry12 (uncurry12 r).
Proof. unfold le12. intros. apply PR. Qed.

Lemma curry_bij1_12 r : uncurry12 (curry12 r) <1== r.
Proof. intros [] H. apply H. Qed.

Lemma curry_bij2_12 r : r <1== uncurry12 (curry12 r).
Proof. intros [] H. apply H. Qed.

Lemma uncurry_adjoint1_12 r0 r1 (LE: uncurry12 r0 <1== r1) : r0 <12== curry12 r1.
Proof.
  apply uncurry_map_rev12. eapply le1_trans; [apply LE|]. apply curry_bij2_12.
Qed.

Lemma uncurry_adjoint2_12 r0 r1 (LE: r0 <12== curry12 r1) : uncurry12 r0 <1== r1.
Proof.
  apply curry_map_rev12. eapply le12_trans; [|apply LE]. apply uncurry_bij2_12.
Qed.

Lemma curry_adjoint1_12 r0 r1 (LE: curry12 r0 <12== r1) : r0 <1== uncurry12 r1.
Proof.
  apply curry_map_rev12. eapply le12_trans; [apply LE|]. apply uncurry_bij2_12.
Qed.

Lemma curry_adjoint2_12 r0 r1 (LE: r0 <1== uncurry12 r1) : curry12 r0 <12== r1.
Proof.
  apply uncurry_map_rev12. eapply le1_trans; [|apply LE]. apply curry_bij1_12.
Qed.

End SIG12.
Section SIG13.

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
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.

(** ** Signatures *)

Record sig13T  :=
  exist13T {
      proj13T0: @T0;
      proj13T1: @T1 proj13T0;
      proj13T2: @T2 proj13T0 proj13T1;
      proj13T3: @T3 proj13T0 proj13T1 proj13T2;
      proj13T4: @T4 proj13T0 proj13T1 proj13T2 proj13T3;
      proj13T5: @T5 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4;
      proj13T6: @T6 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5;
      proj13T7: @T7 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6;
      proj13T8: @T8 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7;
      proj13T9: @T9 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7 proj13T8;
      proj13T10: @T10 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7 proj13T8 proj13T9;
      proj13T11: @T11 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7 proj13T8 proj13T9 proj13T10;
      proj13T12: @T12 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7 proj13T8 proj13T9 proj13T10 proj13T11;
    }.
Definition uncurry13  (R: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12): rel1 sig13T :=
  fun x => R (proj13T0 x) (proj13T1 x) (proj13T2 x) (proj13T3 x) (proj13T4 x) (proj13T5 x) (proj13T6 x) (proj13T7 x) (proj13T8 x) (proj13T9 x) (proj13T10 x) (proj13T11 x) (proj13T12 x).
Definition curry13  (R: rel1 sig13T): rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => R (@exist13T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12).

Lemma uncurry_map13 r0 r1 (LE : r0 <13== r1) : uncurry13 r0 <1== uncurry13 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev13 r0 r1 (LE: uncurry13 r0 <1== uncurry13 r1) : r0 <13== r1.
Proof.
  red; intros. apply (LE (@exist13T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) PR).
Qed.

Lemma curry_map13 r0 r1 (LE: r0 <1== r1) : curry13 r0 <13== curry13 r1.
Proof. 
  red; intros. apply (LE (@exist13T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) PR).
Qed.

Lemma curry_map_rev13 r0 r1 (LE: curry13 r0 <13== curry13 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_13 r : curry13 (uncurry13 r) <13== r.
Proof. unfold le13. intros. apply PR. Qed.

Lemma uncurry_bij2_13 r : r <13== curry13 (uncurry13 r).
Proof. unfold le13. intros. apply PR. Qed.

Lemma curry_bij1_13 r : uncurry13 (curry13 r) <1== r.
Proof. intros [] H. apply H. Qed.

Lemma curry_bij2_13 r : r <1== uncurry13 (curry13 r).
Proof. intros [] H. apply H. Qed.

Lemma uncurry_adjoint1_13 r0 r1 (LE: uncurry13 r0 <1== r1) : r0 <13== curry13 r1.
Proof.
  apply uncurry_map_rev13. eapply le1_trans; [apply LE|]. apply curry_bij2_13.
Qed.

Lemma uncurry_adjoint2_13 r0 r1 (LE: r0 <13== curry13 r1) : uncurry13 r0 <1== r1.
Proof.
  apply curry_map_rev13. eapply le13_trans; [|apply LE]. apply uncurry_bij2_13.
Qed.

Lemma curry_adjoint1_13 r0 r1 (LE: curry13 r0 <13== r1) : r0 <1== uncurry13 r1.
Proof.
  apply curry_map_rev13. eapply le13_trans; [apply LE|]. apply uncurry_bij2_13.
Qed.

Lemma curry_adjoint2_13 r0 r1 (LE: r0 <1== uncurry13 r1) : curry13 r0 <13== r1.
Proof.
  apply uncurry_map_rev13. eapply le1_trans; [|apply LE]. apply curry_bij1_13.
Qed.

End SIG13.
Section SIG14.

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
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.

(** ** Signatures *)

Record sig14T  :=
  exist14T {
      proj14T0: @T0;
      proj14T1: @T1 proj14T0;
      proj14T2: @T2 proj14T0 proj14T1;
      proj14T3: @T3 proj14T0 proj14T1 proj14T2;
      proj14T4: @T4 proj14T0 proj14T1 proj14T2 proj14T3;
      proj14T5: @T5 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4;
      proj14T6: @T6 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5;
      proj14T7: @T7 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6;
      proj14T8: @T8 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6 proj14T7;
      proj14T9: @T9 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6 proj14T7 proj14T8;
      proj14T10: @T10 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6 proj14T7 proj14T8 proj14T9;
      proj14T11: @T11 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6 proj14T7 proj14T8 proj14T9 proj14T10;
      proj14T12: @T12 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6 proj14T7 proj14T8 proj14T9 proj14T10 proj14T11;
      proj14T13: @T13 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6 proj14T7 proj14T8 proj14T9 proj14T10 proj14T11 proj14T12;
    }.
Definition uncurry14  (R: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13): rel1 sig14T :=
  fun x => R (proj14T0 x) (proj14T1 x) (proj14T2 x) (proj14T3 x) (proj14T4 x) (proj14T5 x) (proj14T6 x) (proj14T7 x) (proj14T8 x) (proj14T9 x) (proj14T10 x) (proj14T11 x) (proj14T12 x) (proj14T13 x).
Definition curry14  (R: rel1 sig14T): rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 => R (@exist14T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13).

Lemma uncurry_map14 r0 r1 (LE : r0 <14== r1) : uncurry14 r0 <1== uncurry14 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev14 r0 r1 (LE: uncurry14 r0 <1== uncurry14 r1) : r0 <14== r1.
Proof.
  red; intros. apply (LE (@exist14T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) PR).
Qed.

Lemma curry_map14 r0 r1 (LE: r0 <1== r1) : curry14 r0 <14== curry14 r1.
Proof. 
  red; intros. apply (LE (@exist14T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) PR).
Qed.

Lemma curry_map_rev14 r0 r1 (LE: curry14 r0 <14== curry14 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_14 r : curry14 (uncurry14 r) <14== r.
Proof. unfold le14. intros. apply PR. Qed.

Lemma uncurry_bij2_14 r : r <14== curry14 (uncurry14 r).
Proof. unfold le14. intros. apply PR. Qed.

Lemma curry_bij1_14 r : uncurry14 (curry14 r) <1== r.
Proof. intros [] H. apply H. Qed.

Lemma curry_bij2_14 r : r <1== uncurry14 (curry14 r).
Proof. intros [] H. apply H. Qed.

Lemma uncurry_adjoint1_14 r0 r1 (LE: uncurry14 r0 <1== r1) : r0 <14== curry14 r1.
Proof.
  apply uncurry_map_rev14. eapply le1_trans; [apply LE|]. apply curry_bij2_14.
Qed.

Lemma uncurry_adjoint2_14 r0 r1 (LE: r0 <14== curry14 r1) : uncurry14 r0 <1== r1.
Proof.
  apply curry_map_rev14. eapply le14_trans; [|apply LE]. apply uncurry_bij2_14.
Qed.

Lemma curry_adjoint1_14 r0 r1 (LE: curry14 r0 <14== r1) : r0 <1== uncurry14 r1.
Proof.
  apply curry_map_rev14. eapply le14_trans; [apply LE|]. apply uncurry_bij2_14.
Qed.

Lemma curry_adjoint2_14 r0 r1 (LE: r0 <1== uncurry14 r1) : curry14 r0 <14== r1.
Proof.
  apply uncurry_map_rev14. eapply le1_trans; [|apply LE]. apply curry_bij1_14.
Qed.

End SIG14.
(** *** Arity 0
*)

Ltac paco_cont0 :=
generalize _paco_foo_cons; paco_generalize_hyp _paco_mark.

Ltac paco_pre0 :=
generalize _paco_mark_cons; repeat intro; paco_cont0.

Ltac paco_post_match0 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| bot0 -> _ => clear H; tac1 cr
| ?pr -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post0" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match0 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 1
*)

Lemma _paco_convert1: forall T0
(paco1: forall
(y0: @T0)
, Prop)
 y0
(CONVERT: forall
(x0: @T0)
(EQ: _paco_id (@exist1T T0 x0 = @exist1T T0 y0))
, @paco1 x0),
@paco1 y0.
Proof. intros. apply CONVERT; reflexivity. Qed.

Lemma _paco_convert_rev1: forall T0
(paco1: forall
(y0: @T0)
, Prop)
 y0
 x0
(EQ: _paco_id (@exist1T T0 x0 = @exist1T T0 y0))
(PACO: @paco1 y0),
@paco1 x0.
Proof. intros.
apply (@f_equal (@sig1T T0) _ (fun x => @paco1
 x.(proj1T0)
)) in EQ. simpl in EQ. rewrite EQ. apply PACO.
Qed.

Ltac paco_convert_rev1 := match goal with
| [H: _paco_id (@exist1T _ ?x0 = @exist1T _ ?y0) |- _] =>
eapply _paco_convert_rev1; [eapply H; clear H|..]; clear x0 H
end.

Ltac paco_cont1 e0 :=
let x0 := fresh "_paco_v_" in
apply _paco_convert1;
intros x0;
move x0 at top;
paco_generalize_hyp _paco_mark; revert x0.

Lemma _paco_pre1: forall T0 (gf: rel1 T0) x0
(X: let gf' := gf in gf' x0), gf x0.
Proof. intros; apply X. Defined.

Ltac paco_pre1 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre1;
match goal with
| [|- let _ : _ ?T0 := _ in _ ?e0] => intro X; unfold X; clear X;
paco_cont1
 (e0: T0)
end.

Ltac paco_post_match1 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _, bot1 _ -> _ => clear H; tac1 cr
| forall _, ?pr _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Ltac paco_simp_hyp1 CIH :=
  let EP := fresh "_paco_EP_" in
  let FP := fresh "_paco_FF_" in
  let TP := fresh "_paco_TP_" in
  let XP := fresh "_paco_XP_" in
  let PP := type of CIH in
  evar (EP: Prop);
  assert (TP: False -> PP) by (
    intros FP; generalize _paco_mark_cons;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev1; paco_revert_hyp _paco_mark;
    let con := get_concl in set (TP:=con); revert EP; instantiate (1:= con); destruct FP);
  clear TP;
  assert (XP: EP) by (unfold EP; clear -CIH; repeat intro; apply CIH;
    first [
      (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       [..|match goal with [|-_paco_id (?a = ?b)] => unfold _paco_id; reflexivity end];
       first [eassumption|apply _paco_foo_cons]); fail
    | (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       (try unfold _paco_id); eauto using _paco_foo_cons)]);
  unfold EP in *; clear EP CIH; rename XP into CIH.

Ltac paco_post_simp1 CIH :=
  let CIH := fresh CIH in
  intro CIH; paco_simp_hyp1 CIH;
  first [try(match goal with [ |- context[_paco_id] ] => fail 2 | [ |- context[_paco_foo] ] => fail 2 end) |
    let TMP := fresh "_paco_TMP_" in
    generalize _paco_mark_cons; intro TMP;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev1; paco_revert_hyp _paco_mark
  ].

Tactic Notation "paco_post1" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match1 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp1 CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 2
*)

Lemma _paco_convert2: forall T0 T1
(paco2: forall
(y0: @T0)
(y1: @T1 y0)
, Prop)
 y0 y1
(CONVERT: forall
(x0: @T0)
(x1: @T1 x0)
(EQ: _paco_id (@exist2T T0 T1 x0 x1 = @exist2T T0 T1 y0 y1))
, @paco2 x0 x1),
@paco2 y0 y1.
Proof. intros. apply CONVERT; reflexivity. Qed.

Lemma _paco_convert_rev2: forall T0 T1
(paco2: forall
(y0: @T0)
(y1: @T1 y0)
, Prop)
 y0 y1
 x0 x1
(EQ: _paco_id (@exist2T T0 T1 x0 x1 = @exist2T T0 T1 y0 y1))
(PACO: @paco2 y0 y1),
@paco2 x0 x1.
Proof. intros.
apply (@f_equal (@sig2T T0 T1) _ (fun x => @paco2
 x.(proj2T0)
 x.(proj2T1)
)) in EQ. simpl in EQ. rewrite EQ. apply PACO.
Qed.

Ltac paco_convert_rev2 := match goal with
| [H: _paco_id (@exist2T _ _ ?x0 ?x1 = @exist2T _ _ ?y0 ?y1) |- _] =>
eapply _paco_convert_rev2; [eapply H; clear H|..]; clear x0 x1 H
end.

Ltac paco_cont2 e0 e1 :=
let x0 := fresh "_paco_v_" in
let x1 := fresh "_paco_v_" in
apply _paco_convert2;
intros x0 x1;
move x0 at top; move x1 at top;
paco_generalize_hyp _paco_mark; revert x0 x1.

Lemma _paco_pre2: forall T0 T1 (gf: rel2 T0 T1) x0 x1
(X: let gf' := gf in gf' x0 x1), gf x0 x1.
Proof. intros; apply X. Defined.

Ltac paco_pre2 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre2;
match goal with
| [|- let _ : _ ?T0 ?T1 := _ in _ ?e0 ?e1] => intro X; unfold X; clear X;
paco_cont2
 (e0: T0)
 (e1: T1 e0)
end.

Ltac paco_post_match2 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _, bot2 _ _ -> _ => clear H; tac1 cr
| forall _ _, ?pr _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Ltac paco_simp_hyp2 CIH :=
  let EP := fresh "_paco_EP_" in
  let FP := fresh "_paco_FF_" in
  let TP := fresh "_paco_TP_" in
  let XP := fresh "_paco_XP_" in
  let PP := type of CIH in
  evar (EP: Prop);
  assert (TP: False -> PP) by (
    intros FP; generalize _paco_mark_cons;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev2; paco_revert_hyp _paco_mark;
    let con := get_concl in set (TP:=con); revert EP; instantiate (1:= con); destruct FP);
  clear TP;
  assert (XP: EP) by (unfold EP; clear -CIH; repeat intro; apply CIH;
    first [
      (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       [..|match goal with [|-_paco_id (?a = ?b)] => unfold _paco_id; reflexivity end];
       first [eassumption|apply _paco_foo_cons]); fail
    | (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       (try unfold _paco_id); eauto using _paco_foo_cons)]);
  unfold EP in *; clear EP CIH; rename XP into CIH.

Ltac paco_post_simp2 CIH :=
  let CIH := fresh CIH in
  intro CIH; paco_simp_hyp2 CIH;
  first [try(match goal with [ |- context[_paco_id] ] => fail 2 | [ |- context[_paco_foo] ] => fail 2 end) |
    let TMP := fresh "_paco_TMP_" in
    generalize _paco_mark_cons; intro TMP;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev2; paco_revert_hyp _paco_mark
  ].

Tactic Notation "paco_post2" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match2 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp2 CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 3
*)

Lemma _paco_convert3: forall T0 T1 T2
(paco3: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
, Prop)
 y0 y1 y2
(CONVERT: forall
(x0: @T0)
(x1: @T1 x0)
(x2: @T2 x0 x1)
(EQ: _paco_id (@exist3T T0 T1 T2 x0 x1 x2 = @exist3T T0 T1 T2 y0 y1 y2))
, @paco3 x0 x1 x2),
@paco3 y0 y1 y2.
Proof. intros. apply CONVERT; reflexivity. Qed.

Lemma _paco_convert_rev3: forall T0 T1 T2
(paco3: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
, Prop)
 y0 y1 y2
 x0 x1 x2
(EQ: _paco_id (@exist3T T0 T1 T2 x0 x1 x2 = @exist3T T0 T1 T2 y0 y1 y2))
(PACO: @paco3 y0 y1 y2),
@paco3 x0 x1 x2.
Proof. intros.
apply (@f_equal (@sig3T T0 T1 T2) _ (fun x => @paco3
 x.(proj3T0)
 x.(proj3T1)
 x.(proj3T2)
)) in EQ. simpl in EQ. rewrite EQ. apply PACO.
Qed.

Ltac paco_convert_rev3 := match goal with
| [H: _paco_id (@exist3T _ _ _ ?x0 ?x1 ?x2 = @exist3T _ _ _ ?y0 ?y1 ?y2) |- _] =>
eapply _paco_convert_rev3; [eapply H; clear H|..]; clear x0 x1 x2 H
end.

Ltac paco_cont3 e0 e1 e2 :=
let x0 := fresh "_paco_v_" in
let x1 := fresh "_paco_v_" in
let x2 := fresh "_paco_v_" in
apply _paco_convert3;
intros x0 x1 x2;
move x0 at top; move x1 at top; move x2 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2.

Lemma _paco_pre3: forall T0 T1 T2 (gf: rel3 T0 T1 T2) x0 x1 x2
(X: let gf' := gf in gf' x0 x1 x2), gf x0 x1 x2.
Proof. intros; apply X. Defined.

Ltac paco_pre3 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre3;
match goal with
| [|- let _ : _ ?T0 ?T1 ?T2 := _ in _ ?e0 ?e1 ?e2] => intro X; unfold X; clear X;
paco_cont3
 (e0: T0)
 (e1: T1 e0)
 (e2: T2 e0 e1)
end.

Ltac paco_post_match3 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _, bot3 _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _, ?pr _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Ltac paco_simp_hyp3 CIH :=
  let EP := fresh "_paco_EP_" in
  let FP := fresh "_paco_FF_" in
  let TP := fresh "_paco_TP_" in
  let XP := fresh "_paco_XP_" in
  let PP := type of CIH in
  evar (EP: Prop);
  assert (TP: False -> PP) by (
    intros FP; generalize _paco_mark_cons;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev3; paco_revert_hyp _paco_mark;
    let con := get_concl in set (TP:=con); revert EP; instantiate (1:= con); destruct FP);
  clear TP;
  assert (XP: EP) by (unfold EP; clear -CIH; repeat intro; apply CIH;
    first [
      (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       [..|match goal with [|-_paco_id (?a = ?b)] => unfold _paco_id; reflexivity end];
       first [eassumption|apply _paco_foo_cons]); fail
    | (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       (try unfold _paco_id); eauto using _paco_foo_cons)]);
  unfold EP in *; clear EP CIH; rename XP into CIH.

Ltac paco_post_simp3 CIH :=
  let CIH := fresh CIH in
  intro CIH; paco_simp_hyp3 CIH;
  first [try(match goal with [ |- context[_paco_id] ] => fail 2 | [ |- context[_paco_foo] ] => fail 2 end) |
    let TMP := fresh "_paco_TMP_" in
    generalize _paco_mark_cons; intro TMP;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev3; paco_revert_hyp _paco_mark
  ].

Tactic Notation "paco_post3" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match3 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp3 CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 4
*)

Lemma _paco_convert4: forall T0 T1 T2 T3
(paco4: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
, Prop)
 y0 y1 y2 y3
(CONVERT: forall
(x0: @T0)
(x1: @T1 x0)
(x2: @T2 x0 x1)
(x3: @T3 x0 x1 x2)
(EQ: _paco_id (@exist4T T0 T1 T2 T3 x0 x1 x2 x3 = @exist4T T0 T1 T2 T3 y0 y1 y2 y3))
, @paco4 x0 x1 x2 x3),
@paco4 y0 y1 y2 y3.
Proof. intros. apply CONVERT; reflexivity. Qed.

Lemma _paco_convert_rev4: forall T0 T1 T2 T3
(paco4: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
, Prop)
 y0 y1 y2 y3
 x0 x1 x2 x3
(EQ: _paco_id (@exist4T T0 T1 T2 T3 x0 x1 x2 x3 = @exist4T T0 T1 T2 T3 y0 y1 y2 y3))
(PACO: @paco4 y0 y1 y2 y3),
@paco4 x0 x1 x2 x3.
Proof. intros.
apply (@f_equal (@sig4T T0 T1 T2 T3) _ (fun x => @paco4
 x.(proj4T0)
 x.(proj4T1)
 x.(proj4T2)
 x.(proj4T3)
)) in EQ. simpl in EQ. rewrite EQ. apply PACO.
Qed.

Ltac paco_convert_rev4 := match goal with
| [H: _paco_id (@exist4T _ _ _ _ ?x0 ?x1 ?x2 ?x3 = @exist4T _ _ _ _ ?y0 ?y1 ?y2 ?y3) |- _] =>
eapply _paco_convert_rev4; [eapply H; clear H|..]; clear x0 x1 x2 x3 H
end.

Ltac paco_cont4 e0 e1 e2 e3 :=
let x0 := fresh "_paco_v_" in
let x1 := fresh "_paco_v_" in
let x2 := fresh "_paco_v_" in
let x3 := fresh "_paco_v_" in
apply _paco_convert4;
intros x0 x1 x2 x3;
move x0 at top; move x1 at top; move x2 at top; move x3 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3.

Lemma _paco_pre4: forall T0 T1 T2 T3 (gf: rel4 T0 T1 T2 T3) x0 x1 x2 x3
(X: let gf' := gf in gf' x0 x1 x2 x3), gf x0 x1 x2 x3.
Proof. intros; apply X. Defined.

Ltac paco_pre4 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre4;
match goal with
| [|- let _ : _ ?T0 ?T1 ?T2 ?T3 := _ in _ ?e0 ?e1 ?e2 ?e3] => intro X; unfold X; clear X;
paco_cont4
 (e0: T0)
 (e1: T1 e0)
 (e2: T2 e0 e1)
 (e3: T3 e0 e1 e2)
end.

Ltac paco_post_match4 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _, bot4 _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _, ?pr _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Ltac paco_simp_hyp4 CIH :=
  let EP := fresh "_paco_EP_" in
  let FP := fresh "_paco_FF_" in
  let TP := fresh "_paco_TP_" in
  let XP := fresh "_paco_XP_" in
  let PP := type of CIH in
  evar (EP: Prop);
  assert (TP: False -> PP) by (
    intros FP; generalize _paco_mark_cons;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev4; paco_revert_hyp _paco_mark;
    let con := get_concl in set (TP:=con); revert EP; instantiate (1:= con); destruct FP);
  clear TP;
  assert (XP: EP) by (unfold EP; clear -CIH; repeat intro; apply CIH;
    first [
      (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       [..|match goal with [|-_paco_id (?a = ?b)] => unfold _paco_id; reflexivity end];
       first [eassumption|apply _paco_foo_cons]); fail
    | (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       (try unfold _paco_id); eauto using _paco_foo_cons)]);
  unfold EP in *; clear EP CIH; rename XP into CIH.

Ltac paco_post_simp4 CIH :=
  let CIH := fresh CIH in
  intro CIH; paco_simp_hyp4 CIH;
  first [try(match goal with [ |- context[_paco_id] ] => fail 2 | [ |- context[_paco_foo] ] => fail 2 end) |
    let TMP := fresh "_paco_TMP_" in
    generalize _paco_mark_cons; intro TMP;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev4; paco_revert_hyp _paco_mark
  ].

Tactic Notation "paco_post4" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match4 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp4 CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 5
*)

Lemma _paco_convert5: forall T0 T1 T2 T3 T4
(paco5: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
, Prop)
 y0 y1 y2 y3 y4
(CONVERT: forall
(x0: @T0)
(x1: @T1 x0)
(x2: @T2 x0 x1)
(x3: @T3 x0 x1 x2)
(x4: @T4 x0 x1 x2 x3)
(EQ: _paco_id (@exist5T T0 T1 T2 T3 T4 x0 x1 x2 x3 x4 = @exist5T T0 T1 T2 T3 T4 y0 y1 y2 y3 y4))
, @paco5 x0 x1 x2 x3 x4),
@paco5 y0 y1 y2 y3 y4.
Proof. intros. apply CONVERT; reflexivity. Qed.

Lemma _paco_convert_rev5: forall T0 T1 T2 T3 T4
(paco5: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
, Prop)
 y0 y1 y2 y3 y4
 x0 x1 x2 x3 x4
(EQ: _paco_id (@exist5T T0 T1 T2 T3 T4 x0 x1 x2 x3 x4 = @exist5T T0 T1 T2 T3 T4 y0 y1 y2 y3 y4))
(PACO: @paco5 y0 y1 y2 y3 y4),
@paco5 x0 x1 x2 x3 x4.
Proof. intros.
apply (@f_equal (@sig5T T0 T1 T2 T3 T4) _ (fun x => @paco5
 x.(proj5T0)
 x.(proj5T1)
 x.(proj5T2)
 x.(proj5T3)
 x.(proj5T4)
)) in EQ. simpl in EQ. rewrite EQ. apply PACO.
Qed.

Ltac paco_convert_rev5 := match goal with
| [H: _paco_id (@exist5T _ _ _ _ _ ?x0 ?x1 ?x2 ?x3 ?x4 = @exist5T _ _ _ _ _ ?y0 ?y1 ?y2 ?y3 ?y4) |- _] =>
eapply _paco_convert_rev5; [eapply H; clear H|..]; clear x0 x1 x2 x3 x4 H
end.

Ltac paco_cont5 e0 e1 e2 e3 e4 :=
let x0 := fresh "_paco_v_" in
let x1 := fresh "_paco_v_" in
let x2 := fresh "_paco_v_" in
let x3 := fresh "_paco_v_" in
let x4 := fresh "_paco_v_" in
apply _paco_convert5;
intros x0 x1 x2 x3 x4;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4.

Lemma _paco_pre5: forall T0 T1 T2 T3 T4 (gf: rel5 T0 T1 T2 T3 T4) x0 x1 x2 x3 x4
(X: let gf' := gf in gf' x0 x1 x2 x3 x4), gf x0 x1 x2 x3 x4.
Proof. intros; apply X. Defined.

Ltac paco_pre5 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre5;
match goal with
| [|- let _ : _ ?T0 ?T1 ?T2 ?T3 ?T4 := _ in _ ?e0 ?e1 ?e2 ?e3 ?e4] => intro X; unfold X; clear X;
paco_cont5
 (e0: T0)
 (e1: T1 e0)
 (e2: T2 e0 e1)
 (e3: T3 e0 e1 e2)
 (e4: T4 e0 e1 e2 e3)
end.

Ltac paco_post_match5 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _, bot5 _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _, ?pr _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Ltac paco_simp_hyp5 CIH :=
  let EP := fresh "_paco_EP_" in
  let FP := fresh "_paco_FF_" in
  let TP := fresh "_paco_TP_" in
  let XP := fresh "_paco_XP_" in
  let PP := type of CIH in
  evar (EP: Prop);
  assert (TP: False -> PP) by (
    intros FP; generalize _paco_mark_cons;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev5; paco_revert_hyp _paco_mark;
    let con := get_concl in set (TP:=con); revert EP; instantiate (1:= con); destruct FP);
  clear TP;
  assert (XP: EP) by (unfold EP; clear -CIH; repeat intro; apply CIH;
    first [
      (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       [..|match goal with [|-_paco_id (?a = ?b)] => unfold _paco_id; reflexivity end];
       first [eassumption|apply _paco_foo_cons]); fail
    | (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       (try unfold _paco_id); eauto using _paco_foo_cons)]);
  unfold EP in *; clear EP CIH; rename XP into CIH.

Ltac paco_post_simp5 CIH :=
  let CIH := fresh CIH in
  intro CIH; paco_simp_hyp5 CIH;
  first [try(match goal with [ |- context[_paco_id] ] => fail 2 | [ |- context[_paco_foo] ] => fail 2 end) |
    let TMP := fresh "_paco_TMP_" in
    generalize _paco_mark_cons; intro TMP;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev5; paco_revert_hyp _paco_mark
  ].

Tactic Notation "paco_post5" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match5 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp5 CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 6
*)

Lemma _paco_convert6: forall T0 T1 T2 T3 T4 T5
(paco6: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
(y5: @T5 y0 y1 y2 y3 y4)
, Prop)
 y0 y1 y2 y3 y4 y5
(CONVERT: forall
(x0: @T0)
(x1: @T1 x0)
(x2: @T2 x0 x1)
(x3: @T3 x0 x1 x2)
(x4: @T4 x0 x1 x2 x3)
(x5: @T5 x0 x1 x2 x3 x4)
(EQ: _paco_id (@exist6T T0 T1 T2 T3 T4 T5 x0 x1 x2 x3 x4 x5 = @exist6T T0 T1 T2 T3 T4 T5 y0 y1 y2 y3 y4 y5))
, @paco6 x0 x1 x2 x3 x4 x5),
@paco6 y0 y1 y2 y3 y4 y5.
Proof. intros. apply CONVERT; reflexivity. Qed.

Lemma _paco_convert_rev6: forall T0 T1 T2 T3 T4 T5
(paco6: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
(y5: @T5 y0 y1 y2 y3 y4)
, Prop)
 y0 y1 y2 y3 y4 y5
 x0 x1 x2 x3 x4 x5
(EQ: _paco_id (@exist6T T0 T1 T2 T3 T4 T5 x0 x1 x2 x3 x4 x5 = @exist6T T0 T1 T2 T3 T4 T5 y0 y1 y2 y3 y4 y5))
(PACO: @paco6 y0 y1 y2 y3 y4 y5),
@paco6 x0 x1 x2 x3 x4 x5.
Proof. intros.
apply (@f_equal (@sig6T T0 T1 T2 T3 T4 T5) _ (fun x => @paco6
 x.(proj6T0)
 x.(proj6T1)
 x.(proj6T2)
 x.(proj6T3)
 x.(proj6T4)
 x.(proj6T5)
)) in EQ. simpl in EQ. rewrite EQ. apply PACO.
Qed.

Ltac paco_convert_rev6 := match goal with
| [H: _paco_id (@exist6T _ _ _ _ _ _ ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 = @exist6T _ _ _ _ _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5) |- _] =>
eapply _paco_convert_rev6; [eapply H; clear H|..]; clear x0 x1 x2 x3 x4 x5 H
end.

Ltac paco_cont6 e0 e1 e2 e3 e4 e5 :=
let x0 := fresh "_paco_v_" in
let x1 := fresh "_paco_v_" in
let x2 := fresh "_paco_v_" in
let x3 := fresh "_paco_v_" in
let x4 := fresh "_paco_v_" in
let x5 := fresh "_paco_v_" in
apply _paco_convert6;
intros x0 x1 x2 x3 x4 x5;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5.

Lemma _paco_pre6: forall T0 T1 T2 T3 T4 T5 (gf: rel6 T0 T1 T2 T3 T4 T5) x0 x1 x2 x3 x4 x5
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5), gf x0 x1 x2 x3 x4 x5.
Proof. intros; apply X. Defined.

Ltac paco_pre6 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre6;
match goal with
| [|- let _ : _ ?T0 ?T1 ?T2 ?T3 ?T4 ?T5 := _ in _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5] => intro X; unfold X; clear X;
paco_cont6
 (e0: T0)
 (e1: T1 e0)
 (e2: T2 e0 e1)
 (e3: T3 e0 e1 e2)
 (e4: T4 e0 e1 e2 e3)
 (e5: T5 e0 e1 e2 e3 e4)
end.

Ltac paco_post_match6 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _, bot6 _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _, ?pr _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Ltac paco_simp_hyp6 CIH :=
  let EP := fresh "_paco_EP_" in
  let FP := fresh "_paco_FF_" in
  let TP := fresh "_paco_TP_" in
  let XP := fresh "_paco_XP_" in
  let PP := type of CIH in
  evar (EP: Prop);
  assert (TP: False -> PP) by (
    intros FP; generalize _paco_mark_cons;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev6; paco_revert_hyp _paco_mark;
    let con := get_concl in set (TP:=con); revert EP; instantiate (1:= con); destruct FP);
  clear TP;
  assert (XP: EP) by (unfold EP; clear -CIH; repeat intro; apply CIH;
    first [
      (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       [..|match goal with [|-_paco_id (?a = ?b)] => unfold _paco_id; reflexivity end];
       first [eassumption|apply _paco_foo_cons]); fail
    | (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       (try unfold _paco_id); eauto using _paco_foo_cons)]);
  unfold EP in *; clear EP CIH; rename XP into CIH.

Ltac paco_post_simp6 CIH :=
  let CIH := fresh CIH in
  intro CIH; paco_simp_hyp6 CIH;
  first [try(match goal with [ |- context[_paco_id] ] => fail 2 | [ |- context[_paco_foo] ] => fail 2 end) |
    let TMP := fresh "_paco_TMP_" in
    generalize _paco_mark_cons; intro TMP;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev6; paco_revert_hyp _paco_mark
  ].

Tactic Notation "paco_post6" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match6 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp6 CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 7
*)

Lemma _paco_convert7: forall T0 T1 T2 T3 T4 T5 T6
(paco7: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
(y5: @T5 y0 y1 y2 y3 y4)
(y6: @T6 y0 y1 y2 y3 y4 y5)
, Prop)
 y0 y1 y2 y3 y4 y5 y6
(CONVERT: forall
(x0: @T0)
(x1: @T1 x0)
(x2: @T2 x0 x1)
(x3: @T3 x0 x1 x2)
(x4: @T4 x0 x1 x2 x3)
(x5: @T5 x0 x1 x2 x3 x4)
(x6: @T6 x0 x1 x2 x3 x4 x5)
(EQ: _paco_id (@exist7T T0 T1 T2 T3 T4 T5 T6 x0 x1 x2 x3 x4 x5 x6 = @exist7T T0 T1 T2 T3 T4 T5 T6 y0 y1 y2 y3 y4 y5 y6))
, @paco7 x0 x1 x2 x3 x4 x5 x6),
@paco7 y0 y1 y2 y3 y4 y5 y6.
Proof. intros. apply CONVERT; reflexivity. Qed.

Lemma _paco_convert_rev7: forall T0 T1 T2 T3 T4 T5 T6
(paco7: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
(y5: @T5 y0 y1 y2 y3 y4)
(y6: @T6 y0 y1 y2 y3 y4 y5)
, Prop)
 y0 y1 y2 y3 y4 y5 y6
 x0 x1 x2 x3 x4 x5 x6
(EQ: _paco_id (@exist7T T0 T1 T2 T3 T4 T5 T6 x0 x1 x2 x3 x4 x5 x6 = @exist7T T0 T1 T2 T3 T4 T5 T6 y0 y1 y2 y3 y4 y5 y6))
(PACO: @paco7 y0 y1 y2 y3 y4 y5 y6),
@paco7 x0 x1 x2 x3 x4 x5 x6.
Proof. intros.
apply (@f_equal (@sig7T T0 T1 T2 T3 T4 T5 T6) _ (fun x => @paco7
 x.(proj7T0)
 x.(proj7T1)
 x.(proj7T2)
 x.(proj7T3)
 x.(proj7T4)
 x.(proj7T5)
 x.(proj7T6)
)) in EQ. simpl in EQ. rewrite EQ. apply PACO.
Qed.

Ltac paco_convert_rev7 := match goal with
| [H: _paco_id (@exist7T _ _ _ _ _ _ _ ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 = @exist7T _ _ _ _ _ _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6) |- _] =>
eapply _paco_convert_rev7; [eapply H; clear H|..]; clear x0 x1 x2 x3 x4 x5 x6 H
end.

Ltac paco_cont7 e0 e1 e2 e3 e4 e5 e6 :=
let x0 := fresh "_paco_v_" in
let x1 := fresh "_paco_v_" in
let x2 := fresh "_paco_v_" in
let x3 := fresh "_paco_v_" in
let x4 := fresh "_paco_v_" in
let x5 := fresh "_paco_v_" in
let x6 := fresh "_paco_v_" in
apply _paco_convert7;
intros x0 x1 x2 x3 x4 x5 x6;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6.

Lemma _paco_pre7: forall T0 T1 T2 T3 T4 T5 T6 (gf: rel7 T0 T1 T2 T3 T4 T5 T6) x0 x1 x2 x3 x4 x5 x6
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6), gf x0 x1 x2 x3 x4 x5 x6.
Proof. intros; apply X. Defined.

Ltac paco_pre7 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre7;
match goal with
| [|- let _ : _ ?T0 ?T1 ?T2 ?T3 ?T4 ?T5 ?T6 := _ in _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6] => intro X; unfold X; clear X;
paco_cont7
 (e0: T0)
 (e1: T1 e0)
 (e2: T2 e0 e1)
 (e3: T3 e0 e1 e2)
 (e4: T4 e0 e1 e2 e3)
 (e5: T5 e0 e1 e2 e3 e4)
 (e6: T6 e0 e1 e2 e3 e4 e5)
end.

Ltac paco_post_match7 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _, bot7 _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Ltac paco_simp_hyp7 CIH :=
  let EP := fresh "_paco_EP_" in
  let FP := fresh "_paco_FF_" in
  let TP := fresh "_paco_TP_" in
  let XP := fresh "_paco_XP_" in
  let PP := type of CIH in
  evar (EP: Prop);
  assert (TP: False -> PP) by (
    intros FP; generalize _paco_mark_cons;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev7; paco_revert_hyp _paco_mark;
    let con := get_concl in set (TP:=con); revert EP; instantiate (1:= con); destruct FP);
  clear TP;
  assert (XP: EP) by (unfold EP; clear -CIH; repeat intro; apply CIH;
    first [
      (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       [..|match goal with [|-_paco_id (?a = ?b)] => unfold _paco_id; reflexivity end];
       first [eassumption|apply _paco_foo_cons]); fail
    | (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       (try unfold _paco_id); eauto using _paco_foo_cons)]);
  unfold EP in *; clear EP CIH; rename XP into CIH.

Ltac paco_post_simp7 CIH :=
  let CIH := fresh CIH in
  intro CIH; paco_simp_hyp7 CIH;
  first [try(match goal with [ |- context[_paco_id] ] => fail 2 | [ |- context[_paco_foo] ] => fail 2 end) |
    let TMP := fresh "_paco_TMP_" in
    generalize _paco_mark_cons; intro TMP;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev7; paco_revert_hyp _paco_mark
  ].

Tactic Notation "paco_post7" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match7 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp7 CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 8
*)

Lemma _paco_convert8: forall T0 T1 T2 T3 T4 T5 T6 T7
(paco8: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
(y5: @T5 y0 y1 y2 y3 y4)
(y6: @T6 y0 y1 y2 y3 y4 y5)
(y7: @T7 y0 y1 y2 y3 y4 y5 y6)
, Prop)
 y0 y1 y2 y3 y4 y5 y6 y7
(CONVERT: forall
(x0: @T0)
(x1: @T1 x0)
(x2: @T2 x0 x1)
(x3: @T3 x0 x1 x2)
(x4: @T4 x0 x1 x2 x3)
(x5: @T5 x0 x1 x2 x3 x4)
(x6: @T6 x0 x1 x2 x3 x4 x5)
(x7: @T7 x0 x1 x2 x3 x4 x5 x6)
(EQ: _paco_id (@exist8T T0 T1 T2 T3 T4 T5 T6 T7 x0 x1 x2 x3 x4 x5 x6 x7 = @exist8T T0 T1 T2 T3 T4 T5 T6 T7 y0 y1 y2 y3 y4 y5 y6 y7))
, @paco8 x0 x1 x2 x3 x4 x5 x6 x7),
@paco8 y0 y1 y2 y3 y4 y5 y6 y7.
Proof. intros. apply CONVERT; reflexivity. Qed.

Lemma _paco_convert_rev8: forall T0 T1 T2 T3 T4 T5 T6 T7
(paco8: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
(y5: @T5 y0 y1 y2 y3 y4)
(y6: @T6 y0 y1 y2 y3 y4 y5)
(y7: @T7 y0 y1 y2 y3 y4 y5 y6)
, Prop)
 y0 y1 y2 y3 y4 y5 y6 y7
 x0 x1 x2 x3 x4 x5 x6 x7
(EQ: _paco_id (@exist8T T0 T1 T2 T3 T4 T5 T6 T7 x0 x1 x2 x3 x4 x5 x6 x7 = @exist8T T0 T1 T2 T3 T4 T5 T6 T7 y0 y1 y2 y3 y4 y5 y6 y7))
(PACO: @paco8 y0 y1 y2 y3 y4 y5 y6 y7),
@paco8 x0 x1 x2 x3 x4 x5 x6 x7.
Proof. intros.
apply (@f_equal (@sig8T T0 T1 T2 T3 T4 T5 T6 T7) _ (fun x => @paco8
 x.(proj8T0)
 x.(proj8T1)
 x.(proj8T2)
 x.(proj8T3)
 x.(proj8T4)
 x.(proj8T5)
 x.(proj8T6)
 x.(proj8T7)
)) in EQ. simpl in EQ. rewrite EQ. apply PACO.
Qed.

Ltac paco_convert_rev8 := match goal with
| [H: _paco_id (@exist8T _ _ _ _ _ _ _ _ ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 = @exist8T _ _ _ _ _ _ _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7) |- _] =>
eapply _paco_convert_rev8; [eapply H; clear H|..]; clear x0 x1 x2 x3 x4 x5 x6 x7 H
end.

Ltac paco_cont8 e0 e1 e2 e3 e4 e5 e6 e7 :=
let x0 := fresh "_paco_v_" in
let x1 := fresh "_paco_v_" in
let x2 := fresh "_paco_v_" in
let x3 := fresh "_paco_v_" in
let x4 := fresh "_paco_v_" in
let x5 := fresh "_paco_v_" in
let x6 := fresh "_paco_v_" in
let x7 := fresh "_paco_v_" in
apply _paco_convert8;
intros x0 x1 x2 x3 x4 x5 x6 x7;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7.

Lemma _paco_pre8: forall T0 T1 T2 T3 T4 T5 T6 T7 (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7) x0 x1 x2 x3 x4 x5 x6 x7
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7), gf x0 x1 x2 x3 x4 x5 x6 x7.
Proof. intros; apply X. Defined.

Ltac paco_pre8 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre8;
match goal with
| [|- let _ : _ ?T0 ?T1 ?T2 ?T3 ?T4 ?T5 ?T6 ?T7 := _ in _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7] => intro X; unfold X; clear X;
paco_cont8
 (e0: T0)
 (e1: T1 e0)
 (e2: T2 e0 e1)
 (e3: T3 e0 e1 e2)
 (e4: T4 e0 e1 e2 e3)
 (e5: T5 e0 e1 e2 e3 e4)
 (e6: T6 e0 e1 e2 e3 e4 e5)
 (e7: T7 e0 e1 e2 e3 e4 e5 e6)
end.

Ltac paco_post_match8 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _, bot8 _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Ltac paco_simp_hyp8 CIH :=
  let EP := fresh "_paco_EP_" in
  let FP := fresh "_paco_FF_" in
  let TP := fresh "_paco_TP_" in
  let XP := fresh "_paco_XP_" in
  let PP := type of CIH in
  evar (EP: Prop);
  assert (TP: False -> PP) by (
    intros FP; generalize _paco_mark_cons;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev8; paco_revert_hyp _paco_mark;
    let con := get_concl in set (TP:=con); revert EP; instantiate (1:= con); destruct FP);
  clear TP;
  assert (XP: EP) by (unfold EP; clear -CIH; repeat intro; apply CIH;
    first [
      (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       [..|match goal with [|-_paco_id (?a = ?b)] => unfold _paco_id; reflexivity end];
       first [eassumption|apply _paco_foo_cons]); fail
    | (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       (try unfold _paco_id); eauto using _paco_foo_cons)]);
  unfold EP in *; clear EP CIH; rename XP into CIH.

Ltac paco_post_simp8 CIH :=
  let CIH := fresh CIH in
  intro CIH; paco_simp_hyp8 CIH;
  first [try(match goal with [ |- context[_paco_id] ] => fail 2 | [ |- context[_paco_foo] ] => fail 2 end) |
    let TMP := fresh "_paco_TMP_" in
    generalize _paco_mark_cons; intro TMP;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev8; paco_revert_hyp _paco_mark
  ].

Tactic Notation "paco_post8" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match8 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp8 CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 9
*)

Lemma _paco_convert9: forall T0 T1 T2 T3 T4 T5 T6 T7 T8
(paco9: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
(y5: @T5 y0 y1 y2 y3 y4)
(y6: @T6 y0 y1 y2 y3 y4 y5)
(y7: @T7 y0 y1 y2 y3 y4 y5 y6)
(y8: @T8 y0 y1 y2 y3 y4 y5 y6 y7)
, Prop)
 y0 y1 y2 y3 y4 y5 y6 y7 y8
(CONVERT: forall
(x0: @T0)
(x1: @T1 x0)
(x2: @T2 x0 x1)
(x3: @T3 x0 x1 x2)
(x4: @T4 x0 x1 x2 x3)
(x5: @T5 x0 x1 x2 x3 x4)
(x6: @T6 x0 x1 x2 x3 x4 x5)
(x7: @T7 x0 x1 x2 x3 x4 x5 x6)
(x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7)
(EQ: _paco_id (@exist9T T0 T1 T2 T3 T4 T5 T6 T7 T8 x0 x1 x2 x3 x4 x5 x6 x7 x8 = @exist9T T0 T1 T2 T3 T4 T5 T6 T7 T8 y0 y1 y2 y3 y4 y5 y6 y7 y8))
, @paco9 x0 x1 x2 x3 x4 x5 x6 x7 x8),
@paco9 y0 y1 y2 y3 y4 y5 y6 y7 y8.
Proof. intros. apply CONVERT; reflexivity. Qed.

Lemma _paco_convert_rev9: forall T0 T1 T2 T3 T4 T5 T6 T7 T8
(paco9: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
(y5: @T5 y0 y1 y2 y3 y4)
(y6: @T6 y0 y1 y2 y3 y4 y5)
(y7: @T7 y0 y1 y2 y3 y4 y5 y6)
(y8: @T8 y0 y1 y2 y3 y4 y5 y6 y7)
, Prop)
 y0 y1 y2 y3 y4 y5 y6 y7 y8
 x0 x1 x2 x3 x4 x5 x6 x7 x8
(EQ: _paco_id (@exist9T T0 T1 T2 T3 T4 T5 T6 T7 T8 x0 x1 x2 x3 x4 x5 x6 x7 x8 = @exist9T T0 T1 T2 T3 T4 T5 T6 T7 T8 y0 y1 y2 y3 y4 y5 y6 y7 y8))
(PACO: @paco9 y0 y1 y2 y3 y4 y5 y6 y7 y8),
@paco9 x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof. intros.
apply (@f_equal (@sig9T T0 T1 T2 T3 T4 T5 T6 T7 T8) _ (fun x => @paco9
 x.(proj9T0)
 x.(proj9T1)
 x.(proj9T2)
 x.(proj9T3)
 x.(proj9T4)
 x.(proj9T5)
 x.(proj9T6)
 x.(proj9T7)
 x.(proj9T8)
)) in EQ. simpl in EQ. rewrite EQ. apply PACO.
Qed.

Ltac paco_convert_rev9 := match goal with
| [H: _paco_id (@exist9T _ _ _ _ _ _ _ _ _ ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 = @exist9T _ _ _ _ _ _ _ _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8) |- _] =>
eapply _paco_convert_rev9; [eapply H; clear H|..]; clear x0 x1 x2 x3 x4 x5 x6 x7 x8 H
end.

Ltac paco_cont9 e0 e1 e2 e3 e4 e5 e6 e7 e8 :=
let x0 := fresh "_paco_v_" in
let x1 := fresh "_paco_v_" in
let x2 := fresh "_paco_v_" in
let x3 := fresh "_paco_v_" in
let x4 := fresh "_paco_v_" in
let x5 := fresh "_paco_v_" in
let x6 := fresh "_paco_v_" in
let x7 := fresh "_paco_v_" in
let x8 := fresh "_paco_v_" in
apply _paco_convert9;
intros x0 x1 x2 x3 x4 x5 x6 x7 x8;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8.

Lemma _paco_pre9: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) x0 x1 x2 x3 x4 x5 x6 x7 x8
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8), gf x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof. intros; apply X. Defined.

Ltac paco_pre9 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre9;
match goal with
| [|- let _ : _ ?T0 ?T1 ?T2 ?T3 ?T4 ?T5 ?T6 ?T7 ?T8 := _ in _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8] => intro X; unfold X; clear X;
paco_cont9
 (e0: T0)
 (e1: T1 e0)
 (e2: T2 e0 e1)
 (e3: T3 e0 e1 e2)
 (e4: T4 e0 e1 e2 e3)
 (e5: T5 e0 e1 e2 e3 e4)
 (e6: T6 e0 e1 e2 e3 e4 e5)
 (e7: T7 e0 e1 e2 e3 e4 e5 e6)
 (e8: T8 e0 e1 e2 e3 e4 e5 e6 e7)
end.

Ltac paco_post_match9 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _, bot9 _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Ltac paco_simp_hyp9 CIH :=
  let EP := fresh "_paco_EP_" in
  let FP := fresh "_paco_FF_" in
  let TP := fresh "_paco_TP_" in
  let XP := fresh "_paco_XP_" in
  let PP := type of CIH in
  evar (EP: Prop);
  assert (TP: False -> PP) by (
    intros FP; generalize _paco_mark_cons;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev9; paco_revert_hyp _paco_mark;
    let con := get_concl in set (TP:=con); revert EP; instantiate (1:= con); destruct FP);
  clear TP;
  assert (XP: EP) by (unfold EP; clear -CIH; repeat intro; apply CIH;
    first [
      (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       [..|match goal with [|-_paco_id (?a = ?b)] => unfold _paco_id; reflexivity end];
       first [eassumption|apply _paco_foo_cons]); fail
    | (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       (try unfold _paco_id); eauto using _paco_foo_cons)]);
  unfold EP in *; clear EP CIH; rename XP into CIH.

Ltac paco_post_simp9 CIH :=
  let CIH := fresh CIH in
  intro CIH; paco_simp_hyp9 CIH;
  first [try(match goal with [ |- context[_paco_id] ] => fail 2 | [ |- context[_paco_foo] ] => fail 2 end) |
    let TMP := fresh "_paco_TMP_" in
    generalize _paco_mark_cons; intro TMP;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev9; paco_revert_hyp _paco_mark
  ].

Tactic Notation "paco_post9" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match9 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp9 CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 10
*)

Lemma _paco_convert10: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9
(paco10: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
(y5: @T5 y0 y1 y2 y3 y4)
(y6: @T6 y0 y1 y2 y3 y4 y5)
(y7: @T7 y0 y1 y2 y3 y4 y5 y6)
(y8: @T8 y0 y1 y2 y3 y4 y5 y6 y7)
(y9: @T9 y0 y1 y2 y3 y4 y5 y6 y7 y8)
, Prop)
 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9
(CONVERT: forall
(x0: @T0)
(x1: @T1 x0)
(x2: @T2 x0 x1)
(x3: @T3 x0 x1 x2)
(x4: @T4 x0 x1 x2 x3)
(x5: @T5 x0 x1 x2 x3 x4)
(x6: @T6 x0 x1 x2 x3 x4 x5)
(x7: @T7 x0 x1 x2 x3 x4 x5 x6)
(x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7)
(x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8)
(EQ: _paco_id (@exist10T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 = @exist10T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9))
, @paco10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9),
@paco10 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9.
Proof. intros. apply CONVERT; reflexivity. Qed.

Lemma _paco_convert_rev10: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9
(paco10: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
(y5: @T5 y0 y1 y2 y3 y4)
(y6: @T6 y0 y1 y2 y3 y4 y5)
(y7: @T7 y0 y1 y2 y3 y4 y5 y6)
(y8: @T8 y0 y1 y2 y3 y4 y5 y6 y7)
(y9: @T9 y0 y1 y2 y3 y4 y5 y6 y7 y8)
, Prop)
 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9
 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
(EQ: _paco_id (@exist10T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 = @exist10T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9))
(PACO: @paco10 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9),
@paco10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof. intros.
apply (@f_equal (@sig10T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) _ (fun x => @paco10
 x.(proj10T0)
 x.(proj10T1)
 x.(proj10T2)
 x.(proj10T3)
 x.(proj10T4)
 x.(proj10T5)
 x.(proj10T6)
 x.(proj10T7)
 x.(proj10T8)
 x.(proj10T9)
)) in EQ. simpl in EQ. rewrite EQ. apply PACO.
Qed.

Ltac paco_convert_rev10 := match goal with
| [H: _paco_id (@exist10T _ _ _ _ _ _ _ _ _ _ ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 = @exist10T _ _ _ _ _ _ _ _ _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9) |- _] =>
eapply _paco_convert_rev10; [eapply H; clear H|..]; clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 H
end.

Ltac paco_cont10 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 :=
let x0 := fresh "_paco_v_" in
let x1 := fresh "_paco_v_" in
let x2 := fresh "_paco_v_" in
let x3 := fresh "_paco_v_" in
let x4 := fresh "_paco_v_" in
let x5 := fresh "_paco_v_" in
let x6 := fresh "_paco_v_" in
let x7 := fresh "_paco_v_" in
let x8 := fresh "_paco_v_" in
let x9 := fresh "_paco_v_" in
apply _paco_convert10;
intros x0 x1 x2 x3 x4 x5 x6 x7 x8 x9;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.

Lemma _paco_pre10: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof. intros; apply X. Defined.

Ltac paco_pre10 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre10;
match goal with
| [|- let _ : _ ?T0 ?T1 ?T2 ?T3 ?T4 ?T5 ?T6 ?T7 ?T8 ?T9 := _ in _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9] => intro X; unfold X; clear X;
paco_cont10
 (e0: T0)
 (e1: T1 e0)
 (e2: T2 e0 e1)
 (e3: T3 e0 e1 e2)
 (e4: T4 e0 e1 e2 e3)
 (e5: T5 e0 e1 e2 e3 e4)
 (e6: T6 e0 e1 e2 e3 e4 e5)
 (e7: T7 e0 e1 e2 e3 e4 e5 e6)
 (e8: T8 e0 e1 e2 e3 e4 e5 e6 e7)
 (e9: T9 e0 e1 e2 e3 e4 e5 e6 e7 e8)
end.

Ltac paco_post_match10 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _, bot10 _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Ltac paco_simp_hyp10 CIH :=
  let EP := fresh "_paco_EP_" in
  let FP := fresh "_paco_FF_" in
  let TP := fresh "_paco_TP_" in
  let XP := fresh "_paco_XP_" in
  let PP := type of CIH in
  evar (EP: Prop);
  assert (TP: False -> PP) by (
    intros FP; generalize _paco_mark_cons;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev10; paco_revert_hyp _paco_mark;
    let con := get_concl in set (TP:=con); revert EP; instantiate (1:= con); destruct FP);
  clear TP;
  assert (XP: EP) by (unfold EP; clear -CIH; repeat intro; apply CIH;
    first [
      (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       [..|match goal with [|-_paco_id (?a = ?b)] => unfold _paco_id; reflexivity end];
       first [eassumption|apply _paco_foo_cons]); fail
    | (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       (try unfold _paco_id); eauto using _paco_foo_cons)]);
  unfold EP in *; clear EP CIH; rename XP into CIH.

Ltac paco_post_simp10 CIH :=
  let CIH := fresh CIH in
  intro CIH; paco_simp_hyp10 CIH;
  first [try(match goal with [ |- context[_paco_id] ] => fail 2 | [ |- context[_paco_foo] ] => fail 2 end) |
    let TMP := fresh "_paco_TMP_" in
    generalize _paco_mark_cons; intro TMP;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev10; paco_revert_hyp _paco_mark
  ].

Tactic Notation "paco_post10" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match10 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp10 CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 11
*)

Lemma _paco_convert11: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10
(paco11: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
(y5: @T5 y0 y1 y2 y3 y4)
(y6: @T6 y0 y1 y2 y3 y4 y5)
(y7: @T7 y0 y1 y2 y3 y4 y5 y6)
(y8: @T8 y0 y1 y2 y3 y4 y5 y6 y7)
(y9: @T9 y0 y1 y2 y3 y4 y5 y6 y7 y8)
(y10: @T10 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9)
, Prop)
 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10
(CONVERT: forall
(x0: @T0)
(x1: @T1 x0)
(x2: @T2 x0 x1)
(x3: @T3 x0 x1 x2)
(x4: @T4 x0 x1 x2 x3)
(x5: @T5 x0 x1 x2 x3 x4)
(x6: @T6 x0 x1 x2 x3 x4 x5)
(x7: @T7 x0 x1 x2 x3 x4 x5 x6)
(x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7)
(x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8)
(x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
(EQ: _paco_id (@exist11T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 = @exist11T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10))
, @paco11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10),
@paco11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10.
Proof. intros. apply CONVERT; reflexivity. Qed.

Lemma _paco_convert_rev11: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10
(paco11: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
(y5: @T5 y0 y1 y2 y3 y4)
(y6: @T6 y0 y1 y2 y3 y4 y5)
(y7: @T7 y0 y1 y2 y3 y4 y5 y6)
(y8: @T8 y0 y1 y2 y3 y4 y5 y6 y7)
(y9: @T9 y0 y1 y2 y3 y4 y5 y6 y7 y8)
(y10: @T10 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9)
, Prop)
 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10
 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
(EQ: _paco_id (@exist11T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 = @exist11T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10))
(PACO: @paco11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10),
@paco11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof. intros.
apply (@f_equal (@sig11T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) _ (fun x => @paco11
 x.(proj11T0)
 x.(proj11T1)
 x.(proj11T2)
 x.(proj11T3)
 x.(proj11T4)
 x.(proj11T5)
 x.(proj11T6)
 x.(proj11T7)
 x.(proj11T8)
 x.(proj11T9)
 x.(proj11T10)
)) in EQ. simpl in EQ. rewrite EQ. apply PACO.
Qed.

Ltac paco_convert_rev11 := match goal with
| [H: _paco_id (@exist11T _ _ _ _ _ _ _ _ _ _ _ ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 = @exist11T _ _ _ _ _ _ _ _ _ _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10) |- _] =>
eapply _paco_convert_rev11; [eapply H; clear H|..]; clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 H
end.

Ltac paco_cont11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 :=
let x0 := fresh "_paco_v_" in
let x1 := fresh "_paco_v_" in
let x2 := fresh "_paco_v_" in
let x3 := fresh "_paco_v_" in
let x4 := fresh "_paco_v_" in
let x5 := fresh "_paco_v_" in
let x6 := fresh "_paco_v_" in
let x7 := fresh "_paco_v_" in
let x8 := fresh "_paco_v_" in
let x9 := fresh "_paco_v_" in
let x10 := fresh "_paco_v_" in
apply _paco_convert11;
intros x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.

Lemma _paco_pre11: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof. intros; apply X. Defined.

Ltac paco_pre11 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre11;
match goal with
| [|- let _ : _ ?T0 ?T1 ?T2 ?T3 ?T4 ?T5 ?T6 ?T7 ?T8 ?T9 ?T10 := _ in _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10] => intro X; unfold X; clear X;
paco_cont11
 (e0: T0)
 (e1: T1 e0)
 (e2: T2 e0 e1)
 (e3: T3 e0 e1 e2)
 (e4: T4 e0 e1 e2 e3)
 (e5: T5 e0 e1 e2 e3 e4)
 (e6: T6 e0 e1 e2 e3 e4 e5)
 (e7: T7 e0 e1 e2 e3 e4 e5 e6)
 (e8: T8 e0 e1 e2 e3 e4 e5 e6 e7)
 (e9: T9 e0 e1 e2 e3 e4 e5 e6 e7 e8)
 (e10: T10 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9)
end.

Ltac paco_post_match11 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _, bot11 _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Ltac paco_simp_hyp11 CIH :=
  let EP := fresh "_paco_EP_" in
  let FP := fresh "_paco_FF_" in
  let TP := fresh "_paco_TP_" in
  let XP := fresh "_paco_XP_" in
  let PP := type of CIH in
  evar (EP: Prop);
  assert (TP: False -> PP) by (
    intros FP; generalize _paco_mark_cons;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev11; paco_revert_hyp _paco_mark;
    let con := get_concl in set (TP:=con); revert EP; instantiate (1:= con); destruct FP);
  clear TP;
  assert (XP: EP) by (unfold EP; clear -CIH; repeat intro; apply CIH;
    first [
      (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       [..|match goal with [|-_paco_id (?a = ?b)] => unfold _paco_id; reflexivity end];
       first [eassumption|apply _paco_foo_cons]); fail
    | (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       (try unfold _paco_id); eauto using _paco_foo_cons)]);
  unfold EP in *; clear EP CIH; rename XP into CIH.

Ltac paco_post_simp11 CIH :=
  let CIH := fresh CIH in
  intro CIH; paco_simp_hyp11 CIH;
  first [try(match goal with [ |- context[_paco_id] ] => fail 2 | [ |- context[_paco_foo] ] => fail 2 end) |
    let TMP := fresh "_paco_TMP_" in
    generalize _paco_mark_cons; intro TMP;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev11; paco_revert_hyp _paco_mark
  ].

Tactic Notation "paco_post11" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match11 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp11 CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 12
*)

Lemma _paco_convert12: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11
(paco12: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
(y5: @T5 y0 y1 y2 y3 y4)
(y6: @T6 y0 y1 y2 y3 y4 y5)
(y7: @T7 y0 y1 y2 y3 y4 y5 y6)
(y8: @T8 y0 y1 y2 y3 y4 y5 y6 y7)
(y9: @T9 y0 y1 y2 y3 y4 y5 y6 y7 y8)
(y10: @T10 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9)
(y11: @T11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10)
, Prop)
 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11
(CONVERT: forall
(x0: @T0)
(x1: @T1 x0)
(x2: @T2 x0 x1)
(x3: @T3 x0 x1 x2)
(x4: @T4 x0 x1 x2 x3)
(x5: @T5 x0 x1 x2 x3 x4)
(x6: @T6 x0 x1 x2 x3 x4 x5)
(x7: @T7 x0 x1 x2 x3 x4 x5 x6)
(x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7)
(x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8)
(x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
(x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
(EQ: _paco_id (@exist12T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 = @exist12T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11))
, @paco12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11),
@paco12 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11.
Proof. intros. apply CONVERT; reflexivity. Qed.

Lemma _paco_convert_rev12: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11
(paco12: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
(y5: @T5 y0 y1 y2 y3 y4)
(y6: @T6 y0 y1 y2 y3 y4 y5)
(y7: @T7 y0 y1 y2 y3 y4 y5 y6)
(y8: @T8 y0 y1 y2 y3 y4 y5 y6 y7)
(y9: @T9 y0 y1 y2 y3 y4 y5 y6 y7 y8)
(y10: @T10 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9)
(y11: @T11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10)
, Prop)
 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11
 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
(EQ: _paco_id (@exist12T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 = @exist12T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11))
(PACO: @paco12 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11),
@paco12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof. intros.
apply (@f_equal (@sig12T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) _ (fun x => @paco12
 x.(proj12T0)
 x.(proj12T1)
 x.(proj12T2)
 x.(proj12T3)
 x.(proj12T4)
 x.(proj12T5)
 x.(proj12T6)
 x.(proj12T7)
 x.(proj12T8)
 x.(proj12T9)
 x.(proj12T10)
 x.(proj12T11)
)) in EQ. simpl in EQ. rewrite EQ. apply PACO.
Qed.

Ltac paco_convert_rev12 := match goal with
| [H: _paco_id (@exist12T _ _ _ _ _ _ _ _ _ _ _ _ ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 = @exist12T _ _ _ _ _ _ _ _ _ _ _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11) |- _] =>
eapply _paco_convert_rev12; [eapply H; clear H|..]; clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 H
end.

Ltac paco_cont12 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 :=
let x0 := fresh "_paco_v_" in
let x1 := fresh "_paco_v_" in
let x2 := fresh "_paco_v_" in
let x3 := fresh "_paco_v_" in
let x4 := fresh "_paco_v_" in
let x5 := fresh "_paco_v_" in
let x6 := fresh "_paco_v_" in
let x7 := fresh "_paco_v_" in
let x8 := fresh "_paco_v_" in
let x9 := fresh "_paco_v_" in
let x10 := fresh "_paco_v_" in
let x11 := fresh "_paco_v_" in
apply _paco_convert12;
intros x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.

Lemma _paco_pre12: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof. intros; apply X. Defined.

Ltac paco_pre12 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre12;
match goal with
| [|- let _ : _ ?T0 ?T1 ?T2 ?T3 ?T4 ?T5 ?T6 ?T7 ?T8 ?T9 ?T10 ?T11 := _ in _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11] => intro X; unfold X; clear X;
paco_cont12
 (e0: T0)
 (e1: T1 e0)
 (e2: T2 e0 e1)
 (e3: T3 e0 e1 e2)
 (e4: T4 e0 e1 e2 e3)
 (e5: T5 e0 e1 e2 e3 e4)
 (e6: T6 e0 e1 e2 e3 e4 e5)
 (e7: T7 e0 e1 e2 e3 e4 e5 e6)
 (e8: T8 e0 e1 e2 e3 e4 e5 e6 e7)
 (e9: T9 e0 e1 e2 e3 e4 e5 e6 e7 e8)
 (e10: T10 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9)
 (e11: T11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)
end.

Ltac paco_post_match12 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _, bot12 _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Ltac paco_simp_hyp12 CIH :=
  let EP := fresh "_paco_EP_" in
  let FP := fresh "_paco_FF_" in
  let TP := fresh "_paco_TP_" in
  let XP := fresh "_paco_XP_" in
  let PP := type of CIH in
  evar (EP: Prop);
  assert (TP: False -> PP) by (
    intros FP; generalize _paco_mark_cons;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev12; paco_revert_hyp _paco_mark;
    let con := get_concl in set (TP:=con); revert EP; instantiate (1:= con); destruct FP);
  clear TP;
  assert (XP: EP) by (unfold EP; clear -CIH; repeat intro; apply CIH;
    first [
      (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       [..|match goal with [|-_paco_id (?a = ?b)] => unfold _paco_id; reflexivity end];
       first [eassumption|apply _paco_foo_cons]); fail
    | (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       (try unfold _paco_id); eauto using _paco_foo_cons)]);
  unfold EP in *; clear EP CIH; rename XP into CIH.

Ltac paco_post_simp12 CIH :=
  let CIH := fresh CIH in
  intro CIH; paco_simp_hyp12 CIH;
  first [try(match goal with [ |- context[_paco_id] ] => fail 2 | [ |- context[_paco_foo] ] => fail 2 end) |
    let TMP := fresh "_paco_TMP_" in
    generalize _paco_mark_cons; intro TMP;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev12; paco_revert_hyp _paco_mark
  ].

Tactic Notation "paco_post12" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match12 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp12 CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 13
*)

Lemma _paco_convert13: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12
(paco13: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
(y5: @T5 y0 y1 y2 y3 y4)
(y6: @T6 y0 y1 y2 y3 y4 y5)
(y7: @T7 y0 y1 y2 y3 y4 y5 y6)
(y8: @T8 y0 y1 y2 y3 y4 y5 y6 y7)
(y9: @T9 y0 y1 y2 y3 y4 y5 y6 y7 y8)
(y10: @T10 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9)
(y11: @T11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10)
(y12: @T12 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11)
, Prop)
 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12
(CONVERT: forall
(x0: @T0)
(x1: @T1 x0)
(x2: @T2 x0 x1)
(x3: @T3 x0 x1 x2)
(x4: @T4 x0 x1 x2 x3)
(x5: @T5 x0 x1 x2 x3 x4)
(x6: @T6 x0 x1 x2 x3 x4 x5)
(x7: @T7 x0 x1 x2 x3 x4 x5 x6)
(x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7)
(x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8)
(x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
(x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
(x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
(EQ: _paco_id (@exist13T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 = @exist13T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12))
, @paco13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12),
@paco13 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12.
Proof. intros. apply CONVERT; reflexivity. Qed.

Lemma _paco_convert_rev13: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12
(paco13: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
(y5: @T5 y0 y1 y2 y3 y4)
(y6: @T6 y0 y1 y2 y3 y4 y5)
(y7: @T7 y0 y1 y2 y3 y4 y5 y6)
(y8: @T8 y0 y1 y2 y3 y4 y5 y6 y7)
(y9: @T9 y0 y1 y2 y3 y4 y5 y6 y7 y8)
(y10: @T10 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9)
(y11: @T11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10)
(y12: @T12 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11)
, Prop)
 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12
 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
(EQ: _paco_id (@exist13T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 = @exist13T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12))
(PACO: @paco13 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12),
@paco13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof. intros.
apply (@f_equal (@sig13T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) _ (fun x => @paco13
 x.(proj13T0)
 x.(proj13T1)
 x.(proj13T2)
 x.(proj13T3)
 x.(proj13T4)
 x.(proj13T5)
 x.(proj13T6)
 x.(proj13T7)
 x.(proj13T8)
 x.(proj13T9)
 x.(proj13T10)
 x.(proj13T11)
 x.(proj13T12)
)) in EQ. simpl in EQ. rewrite EQ. apply PACO.
Qed.

Ltac paco_convert_rev13 := match goal with
| [H: _paco_id (@exist13T _ _ _ _ _ _ _ _ _ _ _ _ _ ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 = @exist13T _ _ _ _ _ _ _ _ _ _ _ _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12) |- _] =>
eapply _paco_convert_rev13; [eapply H; clear H|..]; clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 H
end.

Ltac paco_cont13 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 :=
let x0 := fresh "_paco_v_" in
let x1 := fresh "_paco_v_" in
let x2 := fresh "_paco_v_" in
let x3 := fresh "_paco_v_" in
let x4 := fresh "_paco_v_" in
let x5 := fresh "_paco_v_" in
let x6 := fresh "_paco_v_" in
let x7 := fresh "_paco_v_" in
let x8 := fresh "_paco_v_" in
let x9 := fresh "_paco_v_" in
let x10 := fresh "_paco_v_" in
let x11 := fresh "_paco_v_" in
let x12 := fresh "_paco_v_" in
apply _paco_convert13;
intros x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.

Lemma _paco_pre13: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof. intros; apply X. Defined.

Ltac paco_pre13 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre13;
match goal with
| [|- let _ : _ ?T0 ?T1 ?T2 ?T3 ?T4 ?T5 ?T6 ?T7 ?T8 ?T9 ?T10 ?T11 ?T12 := _ in _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12] => intro X; unfold X; clear X;
paco_cont13
 (e0: T0)
 (e1: T1 e0)
 (e2: T2 e0 e1)
 (e3: T3 e0 e1 e2)
 (e4: T4 e0 e1 e2 e3)
 (e5: T5 e0 e1 e2 e3 e4)
 (e6: T6 e0 e1 e2 e3 e4 e5)
 (e7: T7 e0 e1 e2 e3 e4 e5 e6)
 (e8: T8 e0 e1 e2 e3 e4 e5 e6 e7)
 (e9: T9 e0 e1 e2 e3 e4 e5 e6 e7 e8)
 (e10: T10 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9)
 (e11: T11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)
 (e12: T12 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)
end.

Ltac paco_post_match13 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _, bot13 _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Ltac paco_simp_hyp13 CIH :=
  let EP := fresh "_paco_EP_" in
  let FP := fresh "_paco_FF_" in
  let TP := fresh "_paco_TP_" in
  let XP := fresh "_paco_XP_" in
  let PP := type of CIH in
  evar (EP: Prop);
  assert (TP: False -> PP) by (
    intros FP; generalize _paco_mark_cons;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev13; paco_revert_hyp _paco_mark;
    let con := get_concl in set (TP:=con); revert EP; instantiate (1:= con); destruct FP);
  clear TP;
  assert (XP: EP) by (unfold EP; clear -CIH; repeat intro; apply CIH;
    first [
      (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       [..|match goal with [|-_paco_id (?a = ?b)] => unfold _paco_id; reflexivity end];
       first [eassumption|apply _paco_foo_cons]); fail
    | (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       (try unfold _paco_id); eauto using _paco_foo_cons)]);
  unfold EP in *; clear EP CIH; rename XP into CIH.

Ltac paco_post_simp13 CIH :=
  let CIH := fresh CIH in
  intro CIH; paco_simp_hyp13 CIH;
  first [try(match goal with [ |- context[_paco_id] ] => fail 2 | [ |- context[_paco_foo] ] => fail 2 end) |
    let TMP := fresh "_paco_TMP_" in
    generalize _paco_mark_cons; intro TMP;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev13; paco_revert_hyp _paco_mark
  ].

Tactic Notation "paco_post13" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match13 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp13 CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 14
*)

Lemma _paco_convert14: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13
(paco14: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
(y5: @T5 y0 y1 y2 y3 y4)
(y6: @T6 y0 y1 y2 y3 y4 y5)
(y7: @T7 y0 y1 y2 y3 y4 y5 y6)
(y8: @T8 y0 y1 y2 y3 y4 y5 y6 y7)
(y9: @T9 y0 y1 y2 y3 y4 y5 y6 y7 y8)
(y10: @T10 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9)
(y11: @T11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10)
(y12: @T12 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11)
(y13: @T13 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12)
, Prop)
 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13
(CONVERT: forall
(x0: @T0)
(x1: @T1 x0)
(x2: @T2 x0 x1)
(x3: @T3 x0 x1 x2)
(x4: @T4 x0 x1 x2 x3)
(x5: @T5 x0 x1 x2 x3 x4)
(x6: @T6 x0 x1 x2 x3 x4 x5)
(x7: @T7 x0 x1 x2 x3 x4 x5 x6)
(x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7)
(x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8)
(x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
(x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
(x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
(x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
(EQ: _paco_id (@exist14T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 = @exist14T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13))
, @paco14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13),
@paco14 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13.
Proof. intros. apply CONVERT; reflexivity. Qed.

Lemma _paco_convert_rev14: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13
(paco14: forall
(y0: @T0)
(y1: @T1 y0)
(y2: @T2 y0 y1)
(y3: @T3 y0 y1 y2)
(y4: @T4 y0 y1 y2 y3)
(y5: @T5 y0 y1 y2 y3 y4)
(y6: @T6 y0 y1 y2 y3 y4 y5)
(y7: @T7 y0 y1 y2 y3 y4 y5 y6)
(y8: @T8 y0 y1 y2 y3 y4 y5 y6 y7)
(y9: @T9 y0 y1 y2 y3 y4 y5 y6 y7 y8)
(y10: @T10 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9)
(y11: @T11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10)
(y12: @T12 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11)
(y13: @T13 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12)
, Prop)
 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13
 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
(EQ: _paco_id (@exist14T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 = @exist14T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13))
(PACO: @paco14 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13),
@paco14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof. intros.
apply (@f_equal (@sig14T T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) _ (fun x => @paco14
 x.(proj14T0)
 x.(proj14T1)
 x.(proj14T2)
 x.(proj14T3)
 x.(proj14T4)
 x.(proj14T5)
 x.(proj14T6)
 x.(proj14T7)
 x.(proj14T8)
 x.(proj14T9)
 x.(proj14T10)
 x.(proj14T11)
 x.(proj14T12)
 x.(proj14T13)
)) in EQ. simpl in EQ. rewrite EQ. apply PACO.
Qed.

Ltac paco_convert_rev14 := match goal with
| [H: _paco_id (@exist14T _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?x0 ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 = @exist14T _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13) |- _] =>
eapply _paco_convert_rev14; [eapply H; clear H|..]; clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 H
end.

Ltac paco_cont14 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 :=
let x0 := fresh "_paco_v_" in
let x1 := fresh "_paco_v_" in
let x2 := fresh "_paco_v_" in
let x3 := fresh "_paco_v_" in
let x4 := fresh "_paco_v_" in
let x5 := fresh "_paco_v_" in
let x6 := fresh "_paco_v_" in
let x7 := fresh "_paco_v_" in
let x8 := fresh "_paco_v_" in
let x9 := fresh "_paco_v_" in
let x10 := fresh "_paco_v_" in
let x11 := fresh "_paco_v_" in
let x12 := fresh "_paco_v_" in
let x13 := fresh "_paco_v_" in
apply _paco_convert14;
intros x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top; move x13 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.

Lemma _paco_pre14: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof. intros; apply X. Defined.

Ltac paco_pre14 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre14;
match goal with
| [|- let _ : _ ?T0 ?T1 ?T2 ?T3 ?T4 ?T5 ?T6 ?T7 ?T8 ?T9 ?T10 ?T11 ?T12 ?T13 := _ in _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13] => intro X; unfold X; clear X;
paco_cont14
 (e0: T0)
 (e1: T1 e0)
 (e2: T2 e0 e1)
 (e3: T3 e0 e1 e2)
 (e4: T4 e0 e1 e2 e3)
 (e5: T5 e0 e1 e2 e3 e4)
 (e6: T6 e0 e1 e2 e3 e4 e5)
 (e7: T7 e0 e1 e2 e3 e4 e5 e6)
 (e8: T8 e0 e1 e2 e3 e4 e5 e6 e7)
 (e9: T9 e0 e1 e2 e3 e4 e5 e6 e7 e8)
 (e10: T10 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9)
 (e11: T11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)
 (e12: T12 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)
 (e13: T13 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12)
end.

Ltac paco_post_match14 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _, bot14 _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Ltac paco_simp_hyp14 CIH :=
  let EP := fresh "_paco_EP_" in
  let FP := fresh "_paco_FF_" in
  let TP := fresh "_paco_TP_" in
  let XP := fresh "_paco_XP_" in
  let PP := type of CIH in
  evar (EP: Prop);
  assert (TP: False -> PP) by (
    intros FP; generalize _paco_mark_cons;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev14; paco_revert_hyp _paco_mark;
    let con := get_concl in set (TP:=con); revert EP; instantiate (1:= con); destruct FP);
  clear TP;
  assert (XP: EP) by (unfold EP; clear -CIH; repeat intro; apply CIH;
    first [
      (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       [..|match goal with [|-_paco_id (?a = ?b)] => unfold _paco_id; reflexivity end];
       first [eassumption|apply _paco_foo_cons]); fail
    | (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       (try unfold _paco_id); eauto using _paco_foo_cons)]);
  unfold EP in *; clear EP CIH; rename XP into CIH.

Ltac paco_post_simp14 CIH :=
  let CIH := fresh CIH in
  intro CIH; paco_simp_hyp14 CIH;
  first [try(match goal with [ |- context[_paco_id] ] => fail 2 | [ |- context[_paco_foo] ] => fail 2 end) |
    let TMP := fresh "_paco_TMP_" in
    generalize _paco_mark_cons; intro TMP;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev14; paco_revert_hyp _paco_mark
  ].

Tactic Notation "paco_post14" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match14 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp14 CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** ** External interface *)

(** We provide our main tactics:

    - [pcofix{n} ident using lemma with ident']


    where [ident] is the identifier used to name the generated coinduction hypothesis,
    [lemma] is an expression denoting which accumulation lemma is to be used, and
    [ident'] is the identifier used to name the accumulation variable.
*)

Tactic Notation "pcofix0" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre0; eapply lem; [..|paco_post0 CIH with r].

Tactic Notation "pcofix1" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre1; eapply lem; [..|paco_post1 CIH with r].

Tactic Notation "pcofix2" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre2; eapply lem; [..|paco_post2 CIH with r].

Tactic Notation "pcofix3" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre3; eapply lem; [..|paco_post3 CIH with r].

Tactic Notation "pcofix4" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre4; eapply lem; [..|paco_post4 CIH with r].

Tactic Notation "pcofix5" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre5; eapply lem; [..|paco_post5 CIH with r].

Tactic Notation "pcofix6" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre6; eapply lem; [..|paco_post6 CIH with r].

Tactic Notation "pcofix7" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre7; eapply lem; [..|paco_post7 CIH with r].

Tactic Notation "pcofix8" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre8; eapply lem; [..|paco_post8 CIH with r].

Tactic Notation "pcofix9" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre9; eapply lem; [..|paco_post9 CIH with r].

Tactic Notation "pcofix10" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre10; eapply lem; [..|paco_post10 CIH with r].

Tactic Notation "pcofix11" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre11; eapply lem; [..|paco_post11 CIH with r].

Tactic Notation "pcofix12" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre12; eapply lem; [..|paco_post12 CIH with r].

Tactic Notation "pcofix13" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre13; eapply lem; [..|paco_post13 CIH with r].

Tactic Notation "pcofix14" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre14; eapply lem; [..|paco_post14 CIH with r].

(** [pcofix] automatically figures out the appropriate index [n] from
    the type of the accumulation lemma [lem] and applies [pcofix{n}].
*)

Tactic Notation "pcofix" ident(CIH) "using" constr(lem) "with" ident(nr) :=
  let N := fresh "_paco_N_" in let TMP := fresh "_paco_TMP_" in
  evar (N : nat);
  let P := type of lem in
  assert (TMP: False -> P) by
    (intro TMP; repeat intro; match goal with [H : _ |- _] => revert H end;
     match goal with
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 14)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 13)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 12)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 11)
     | [|- _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 10)
     | [|- _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 9)
     | [|- _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 8)
     | [|- _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 7)
     | [|- _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 6)
     | [|- _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 5)
     | [|- _ _ _ _ _ -> _] => revert N; instantiate (1 := 4)
     | [|- _ _ _ _ -> _] => revert N; instantiate (1 := 3)
     | [|- _ _ _ -> _] => revert N; instantiate (1 := 2)
     | [|- _ _ -> _] => revert N; instantiate (1 := 1)
     | [|- _ -> _] => revert N; instantiate (1 := 0)
     end; destruct TMP);
  clear TMP;
  revert N;
  match goal with
  | [|- let _ := 0 in _] => intros _; pcofix0 CIH using lem with nr
  | [|- let _ := 1 in _] => intros _; pcofix1 CIH using lem with nr
  | [|- let _ := 2 in _] => intros _; pcofix2 CIH using lem with nr
  | [|- let _ := 3 in _] => intros _; pcofix3 CIH using lem with nr
  | [|- let _ := 4 in _] => intros _; pcofix4 CIH using lem with nr
  | [|- let _ := 5 in _] => intros _; pcofix5 CIH using lem with nr
  | [|- let _ := 6 in _] => intros _; pcofix6 CIH using lem with nr
  | [|- let _ := 7 in _] => intros _; pcofix7 CIH using lem with nr
  | [|- let _ := 8 in _] => intros _; pcofix8 CIH using lem with nr
  | [|- let _ := 9 in _] => intros _; pcofix9 CIH using lem with nr
  | [|- let _ := 10 in _] => intros _; pcofix10 CIH using lem with nr
  | [|- let _ := 11 in _] => intros _; pcofix11 CIH using lem with nr
  | [|- let _ := 12 in _] => intros _; pcofix12 CIH using lem with nr
  | [|- let _ := 13 in _] => intros _; pcofix13 CIH using lem with nr
  | [|- let _ := 14 in _] => intros _; pcofix14 CIH using lem with nr
  end.

Tactic Notation "pcofix" ident(CIH) "using" constr(lem) :=
  pcofix CIH using lem with r.


(** ** Type Class for acc, mult, fold and unfold
*)

Class paco_class (A : Prop) :=
{ pacoacctyp: Type
; pacoacc : pacoacctyp
; pacomulttyp: Type
; pacomult : pacomulttyp
; pacofoldtyp: Type
; pacofold : pacofoldtyp
; pacounfoldtyp: Type
; pacounfold : pacounfoldtyp
}.

Create HintDb paco.

