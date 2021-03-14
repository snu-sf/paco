From Paco Require Import paco pacotac_internal.
From Paco Require Import hpattern.
Set Implicit Arguments.


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
                                 (EQ: _paco_id (@exist4T T0 T1 T2 T3 x0 x1 x2 x3 =
                                      @exist4T T0 T1 T2 T3 y0 y1 y2 y3))
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
                                   x0 x1 x2 x3
                                   y0 y1 y2 y3
                                   (EQ: _paco_id (@exist4T T0 T1 T2 T3 x0 x1 x2 x3 =
                                                  @exist4T T0 T1 T2 T3 y0 y1 y2 y3))
                                   (PACO: @paco4 y0 y1 y2 y3),
    @paco4 x0 x1 x2 x3.
Proof.
  intros.
  eapply (@f_equal (@sig4T T0 T1 T2 T3) _ (fun x => @paco4 x.(proj4T0) x.(proj4T1) x.(proj4T2) x.(proj4T3))) in EQ. simpl in EQ. rewrite EQ. auto.
Qed.

Ltac paco_convert_rev4 := match goal with
                          | [H: _paco_id (@exist4T _ _ _ _ ?x0 ?x1 ?x2 ?x3 = @exist4T _ _ _ _ ?y0 ?y1 ?y2 ?y3) |- _] =>
                            eapply _paco_convert_rev4; [eapply H; clear H|..]; clear x0 x1 x2 x3 H
                          end.

(* changed!!! *)
Ltac paco_cont4 e0 e1 e2 e3 :=
let x0 := fresh "_paco_v_" in (* removed *)
let x1 := fresh "_paco_v_" in
let x2 := fresh "_paco_v_" in
let x3 := fresh "_paco_v_" in
apply _paco_convert4;
intros x0 x1 x2 x3; (* modified *)
move x0 at top; move x1 at top; move x2 at top; move x3 at top;
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3.

(** changed!!! added **)
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
    paco_convert_rev4; (* modified *) paco_revert_hyp _paco_mark;
    let con := get_concl in set (TP:=con); revert EP; instantiate (1:= con); destruct FP);
  clear TP;
  assert (XP: EP) by (unfold EP; clear -CIH; repeat intro; apply CIH; repeat eexists (* modified *));
  unfold EP in *; clear EP CIH; rename XP into CIH.

(** changed!!! added **)
Ltac paco_post_simp4 (* modified 4*) CIH :=
  let CIH := fresh CIH in
  intro CIH; paco_simp_hyp4 (* modified 4 *) CIH;
  first [try(match goal with [ |- context[_paco_id] ] => fail 2 | [ |- context[_paco_foo] ] => fail 2 end) |
    let TMP := fresh "_paco_TMP_" in
    generalize _paco_mark_cons; intro TMP;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    paco_convert_rev4; (* modified *) paco_revert_hyp _paco_mark
  ].

(** changed!! **)
Tactic Notation "paco_post4" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match4 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp4 (* modified 4*) CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(* not changed *)
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

(* not changed *)
Tactic Notation "pcofix4" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre4; eapply lem; [..|paco_post4 CIH with r].

(* not changed *)
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

(* not changed *)
Tactic Notation "pcofix" ident(CIH) "using" constr(lem) :=
  pcofix CIH using lem with r.

(* not changed *)
Tactic Notation "pcofix" ident(CIH) "with" ident(r) :=
  let x := fresh "_x_" in
  generalize _paco_mark_cons; repeat intro; repeat red;
  match goal with [|- ?G] =>
  paco_class G (@pacoacc); intro x;
  match goal with [x:=?lem|-_] => clear x;
    paco_revert_hyp _paco_mark;
    pcofix CIH using lem with r
  end end.

(* not changed *)
Tactic Notation "pcofix" ident(CIH) := pcofix CIH with r.




Section TEST.

  Variant ddd (n: nat): Type :=
  | bb
  .

  Definition _bug
             (bug: forall (n: nat) (m: nat), ddd m * nat -> nat * ddd (n + m) -> Prop):
    forall (n: nat) (m: nat), ddd m * nat -> nat * ddd (n + m) -> Prop := bug.

  Lemma bug_mon: monotone4 _bug.
  Proof.
    unfold monotone4. intros. eapply LE, IN.
  Qed.
  Hint Resolve bug_mon: paco.

  Lemma pcofix_bug:
    forall n m,
      paco4 _bug bot4 (n+m) m (bb m, n * m) (n, bb (n+m+m)).
  Proof.
    pcofix CIH.
    intros. pfold. right. eapply CIH.
  Qed.

  Print Assumptions pcofix_bug.
  (* Closed under the global context *)

End TEST.
