Require Import JMeq.
From Paco Require Import hpattern.
From Paco Require Export paconotation.

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

Lemma paco_eq_JMeq: forall A (a b: A), a = b -> _paco_id (JMeq a b).
Proof. intros; subst; apply JMeq_refl. Defined.

Lemma paco_JMeq_eq: forall (A : Type) (x y : A), _paco_id (JMeq x y) -> _paco_id (x = y).
Proof. intros; apply JMeq_eq; auto. Defined.

Ltac simplJM :=
  repeat match goal with [H: ?x |- _] =>
    match x with
    | _paco_id (JMeq _ _) => apply paco_JMeq_eq in H
    | _paco_id (?a = _) => unfold _paco_id in H; subst a
    end
  end.

Tactic Notation "hrewrite_internal" constr(eqn) "at" int_or_var(occ) :=
  first[hrewrite eqn at occ | rewrite eqn].
Ltac hrewrite_last e H := let x := fresh "_paco_x_" in
  first [try (set (x:=e) at 17; fail 1);
    first [try (set (x:=e) at 9; fail 1);
      first [try (set (x:=e) at 5; fail 1);
        first [try (set (x:=e) at 3; fail 1);
          first [try (set (x:=e) at 2; fail 1);
            try (hrewrite_internal H at 1)
          | try (hrewrite_internal H at 2) ]
        | first [try (set (x:=e) at 4; fail 1);
            try (hrewrite_internal H at 3)
          | try (hrewrite_internal H at 4) ] ]
      | first [try (set (x:=e) at 7; fail 1);
          first [try (set (x:=e) at 6; fail 1);
            try (hrewrite_internal H at 5)
          | try (hrewrite_internal H at 6)]
        | first [try (set (x:=e) at 8; fail 1);
            try (hrewrite_internal H at 7)
          | try (hrewrite_internal H at 8) ] ] ]
    | first [try (set (x:=e) at 13; fail 1);
        first [try (set (x:=e) at 11; fail 1);
          first [try (set (x:=e) at 10; fail 1);
            try (hrewrite_internal H at 9)
          | try (hrewrite_internal H at 10) ]
        | first [try (set (x:=e) at 12; fail 1);
            try (hrewrite_internal H at 11)
          | try (hrewrite_internal H at 12) ] ]
      | first [try (set (x:=e) at 15; fail 1);
          first [try (set (x:=e) at 14; fail 1);
            try (hrewrite_internal H at 13)
          | try (hrewrite_internal H at 14)]
        | first [try (set (x:=e) at 16; fail 1);
            try (hrewrite_internal H at 15)
          | try (hrewrite_internal H at 16) ] ] ] ]
  | first [try (set (x:=e) at 25; fail 1);
      first [try (set (x:=e) at 21; fail 1);
        first [try (set (x:=e) at 19; fail 1);
          first [try (set (x:=e) at 18; fail 1);
            try (hrewrite_internal H at 17)
          | try (hrewrite_internal H at 18) ]
        | first [try (set (x:=e) at 20; fail 1);
            try (hrewrite_internal H at 19)
          | try (hrewrite_internal H at 20) ] ]
      | first [try (set (x:=e) at 23; fail 1);
          first [try (set (x:=e) at 22; fail 1);
            try (hrewrite_internal H at 21)
          | try (hrewrite_internal H at 22)]
        | first [try (set (x:=e) at 24; fail 1);
            try (hrewrite_internal H at 23)
          | try (hrewrite_internal H at 24) ] ] ]
    | first [try (set (x:=e) at 29; fail 1);
        first [try (set (x:=e) at 27; fail 1);
          first [try (set (x:=e) at 26; fail 1);
            try (hrewrite_internal H at 25)
          | try (hrewrite_internal H at 26) ]
        | first [try (set (x:=e) at 28; fail 1);
            try (hrewrite_internal H at 27)
          | try (hrewrite_internal H at 28) ] ]
      | first [try (set (x:=e) at 31; fail 1);
          first [try (set (x:=e) at 30; fail 1);
            try (hrewrite_internal H at 29)
          | try (hrewrite_internal H at 30)]
        | first [try (set (x:=e) at 32; fail 1);
            try (hrewrite_internal H at 31)
          | try (hrewrite_internal H at 32) ] ] ] ] ]
.

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

Ltac paco_convert e x EQ :=
  generalize (eq_refl e); generalize e at 2; intros x EQ;
  hrewrite_last e EQ; apply eq_sym, paco_eq_JMeq in EQ; revert x EQ.

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
    simplJM; paco_revert_hyp _paco_mark;
    let con := get_concl in set (TP:=con); revert EP; instantiate (1:= con); destruct FP);
  clear TP;
  assert (XP: EP) by (unfold EP; clear -CIH; repeat intro; apply CIH;
    first [
      (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       try (apply paco_eq_JMeq; reflexivity);
       first [eassumption|apply _paco_foo_cons]); fail
    | (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end;
       eauto using paco_eq_JMeq, _paco_foo_cons)]);
  unfold EP in *; clear EP CIH; rename XP into CIH.

Ltac paco_post_simp CIH :=
  let CIH := fresh CIH in
  intro CIH; paco_simp_hyp CIH;
  first [try(match goal with [ |- context[_paco_id] ] => fail 2 | [ |- context[_paco_foo] ] => fail 2 end) |
    let TMP := fresh "_paco_TMP_" in
    generalize _paco_mark_cons; intro TMP;
    repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
    simplJM; paco_revert_hyp _paco_mark
  ].

Ltac paco_ren_r nr cr :=
  first [rename cr into nr | let nr := fresh nr in rename cr into nr].

Ltac paco_ren_pr pr cr := rename cr into pr.

Ltac paco_revert :=
  match goal with [H: _ |- _] => revert H end.

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
(x0: @T0) (EQ0: _paco_id (@JMeq.JMeq (@T0) x0 (@T0) y0))
, @paco1 x0),
@paco1 y0.
Proof. intros. apply CONVERT; reflexivity. Qed.

Ltac paco_cont1 e0 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
apply _paco_convert1;
intros x0 EQ0;
generalize EQ0; clear EQ0;
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

Tactic Notation "paco_post1" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match1 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
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
(x0: @T0) (EQ0: _paco_id (@JMeq.JMeq (@T0) x0 (@T0) y0))
(x1: @T1 x0) (EQ1: _paco_id (@JMeq.JMeq (@T1 x0) x1 (@T1 y0) y1))
, @paco2 x0 x1),
@paco2 y0 y1.
Proof. intros. apply CONVERT; reflexivity. Qed.

Ltac paco_cont2 e0 e1 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
apply _paco_convert2;
intros x0 EQ0;
intros x1 EQ1;
generalize (conj EQ0 EQ1); clear EQ0 EQ1;
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

Tactic Notation "paco_post2" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match2 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
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
(x0: @T0) (EQ0: _paco_id (@JMeq.JMeq (@T0) x0 (@T0) y0))
(x1: @T1 x0) (EQ1: _paco_id (@JMeq.JMeq (@T1 x0) x1 (@T1 y0) y1))
(x2: @T2 x0 x1) (EQ2: _paco_id (@JMeq.JMeq (@T2 x0 x1) x2 (@T2 y0 y1) y2))
, @paco3 x0 x1 x2),
@paco3 y0 y1 y2.
Proof. intros. apply CONVERT; reflexivity. Qed.

Ltac paco_cont3 e0 e1 e2 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
apply _paco_convert3;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
generalize (conj EQ0 (conj EQ1 EQ2)); clear EQ0 EQ1 EQ2;
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

Tactic Notation "paco_post3" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match3 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
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
(x0: @T0) (EQ0: _paco_id (@JMeq.JMeq (@T0) x0 (@T0) y0))
(x1: @T1 x0) (EQ1: _paco_id (@JMeq.JMeq (@T1 x0) x1 (@T1 y0) y1))
(x2: @T2 x0 x1) (EQ2: _paco_id (@JMeq.JMeq (@T2 x0 x1) x2 (@T2 y0 y1) y2))
(x3: @T3 x0 x1 x2) (EQ3: _paco_id (@JMeq.JMeq (@T3 x0 x1 x2) x3 (@T3 y0 y1 y2) y3))
, @paco4 x0 x1 x2 x3),
@paco4 y0 y1 y2 y3.
Proof. intros. apply CONVERT; reflexivity. Qed.

Ltac paco_cont4 e0 e1 e2 e3 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
apply _paco_convert4;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
generalize (conj EQ0 (conj EQ1 (conj EQ2 EQ3))); clear EQ0 EQ1 EQ2 EQ3;
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

Tactic Notation "paco_post4" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match4 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
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
(x0: @T0) (EQ0: _paco_id (@JMeq.JMeq (@T0) x0 (@T0) y0))
(x1: @T1 x0) (EQ1: _paco_id (@JMeq.JMeq (@T1 x0) x1 (@T1 y0) y1))
(x2: @T2 x0 x1) (EQ2: _paco_id (@JMeq.JMeq (@T2 x0 x1) x2 (@T2 y0 y1) y2))
(x3: @T3 x0 x1 x2) (EQ3: _paco_id (@JMeq.JMeq (@T3 x0 x1 x2) x3 (@T3 y0 y1 y2) y3))
(x4: @T4 x0 x1 x2 x3) (EQ4: _paco_id (@JMeq.JMeq (@T4 x0 x1 x2 x3) x4 (@T4 y0 y1 y2 y3) y4))
, @paco5 x0 x1 x2 x3 x4),
@paco5 y0 y1 y2 y3 y4.
Proof. intros. apply CONVERT; reflexivity. Qed.

Ltac paco_cont5 e0 e1 e2 e3 e4 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
apply _paco_convert5;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 EQ4)))); clear EQ0 EQ1 EQ2 EQ3 EQ4;
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

Tactic Notation "paco_post5" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match5 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
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
(x0: @T0) (EQ0: _paco_id (@JMeq.JMeq (@T0) x0 (@T0) y0))
(x1: @T1 x0) (EQ1: _paco_id (@JMeq.JMeq (@T1 x0) x1 (@T1 y0) y1))
(x2: @T2 x0 x1) (EQ2: _paco_id (@JMeq.JMeq (@T2 x0 x1) x2 (@T2 y0 y1) y2))
(x3: @T3 x0 x1 x2) (EQ3: _paco_id (@JMeq.JMeq (@T3 x0 x1 x2) x3 (@T3 y0 y1 y2) y3))
(x4: @T4 x0 x1 x2 x3) (EQ4: _paco_id (@JMeq.JMeq (@T4 x0 x1 x2 x3) x4 (@T4 y0 y1 y2 y3) y4))
(x5: @T5 x0 x1 x2 x3 x4) (EQ5: _paco_id (@JMeq.JMeq (@T5 x0 x1 x2 x3 x4) x5 (@T5 y0 y1 y2 y3 y4) y5))
, @paco6 x0 x1 x2 x3 x4 x5),
@paco6 y0 y1 y2 y3 y4 y5.
Proof. intros. apply CONVERT; reflexivity. Qed.

Ltac paco_cont6 e0 e1 e2 e3 e4 e5 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
apply _paco_convert6;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
intros x5 EQ5;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 EQ5))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5;
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

Tactic Notation "paco_post6" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match6 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
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
(x0: @T0) (EQ0: _paco_id (@JMeq.JMeq (@T0) x0 (@T0) y0))
(x1: @T1 x0) (EQ1: _paco_id (@JMeq.JMeq (@T1 x0) x1 (@T1 y0) y1))
(x2: @T2 x0 x1) (EQ2: _paco_id (@JMeq.JMeq (@T2 x0 x1) x2 (@T2 y0 y1) y2))
(x3: @T3 x0 x1 x2) (EQ3: _paco_id (@JMeq.JMeq (@T3 x0 x1 x2) x3 (@T3 y0 y1 y2) y3))
(x4: @T4 x0 x1 x2 x3) (EQ4: _paco_id (@JMeq.JMeq (@T4 x0 x1 x2 x3) x4 (@T4 y0 y1 y2 y3) y4))
(x5: @T5 x0 x1 x2 x3 x4) (EQ5: _paco_id (@JMeq.JMeq (@T5 x0 x1 x2 x3 x4) x5 (@T5 y0 y1 y2 y3 y4) y5))
(x6: @T6 x0 x1 x2 x3 x4 x5) (EQ6: _paco_id (@JMeq.JMeq (@T6 x0 x1 x2 x3 x4 x5) x6 (@T6 y0 y1 y2 y3 y4 y5) y6))
, @paco7 x0 x1 x2 x3 x4 x5 x6),
@paco7 y0 y1 y2 y3 y4 y5 y6.
Proof. intros. apply CONVERT; reflexivity. Qed.

Ltac paco_cont7 e0 e1 e2 e3 e4 e5 e6 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
let x6 := fresh "_paco_v_" in let EQ6 := fresh "_paco_EQ_" in
apply _paco_convert7;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
intros x5 EQ5;
intros x6 EQ6;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 EQ6)))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6;
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

Tactic Notation "paco_post7" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match7 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
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
(x0: @T0) (EQ0: _paco_id (@JMeq.JMeq (@T0) x0 (@T0) y0))
(x1: @T1 x0) (EQ1: _paco_id (@JMeq.JMeq (@T1 x0) x1 (@T1 y0) y1))
(x2: @T2 x0 x1) (EQ2: _paco_id (@JMeq.JMeq (@T2 x0 x1) x2 (@T2 y0 y1) y2))
(x3: @T3 x0 x1 x2) (EQ3: _paco_id (@JMeq.JMeq (@T3 x0 x1 x2) x3 (@T3 y0 y1 y2) y3))
(x4: @T4 x0 x1 x2 x3) (EQ4: _paco_id (@JMeq.JMeq (@T4 x0 x1 x2 x3) x4 (@T4 y0 y1 y2 y3) y4))
(x5: @T5 x0 x1 x2 x3 x4) (EQ5: _paco_id (@JMeq.JMeq (@T5 x0 x1 x2 x3 x4) x5 (@T5 y0 y1 y2 y3 y4) y5))
(x6: @T6 x0 x1 x2 x3 x4 x5) (EQ6: _paco_id (@JMeq.JMeq (@T6 x0 x1 x2 x3 x4 x5) x6 (@T6 y0 y1 y2 y3 y4 y5) y6))
(x7: @T7 x0 x1 x2 x3 x4 x5 x6) (EQ7: _paco_id (@JMeq.JMeq (@T7 x0 x1 x2 x3 x4 x5 x6) x7 (@T7 y0 y1 y2 y3 y4 y5 y6) y7))
, @paco8 x0 x1 x2 x3 x4 x5 x6 x7),
@paco8 y0 y1 y2 y3 y4 y5 y6 y7.
Proof. intros. apply CONVERT; reflexivity. Qed.

Ltac paco_cont8 e0 e1 e2 e3 e4 e5 e6 e7 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
let x6 := fresh "_paco_v_" in let EQ6 := fresh "_paco_EQ_" in
let x7 := fresh "_paco_v_" in let EQ7 := fresh "_paco_EQ_" in
apply _paco_convert8;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
intros x5 EQ5;
intros x6 EQ6;
intros x7 EQ7;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 EQ7))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7;
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

Tactic Notation "paco_post8" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match8 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
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
(x0: @T0) (EQ0: _paco_id (@JMeq.JMeq (@T0) x0 (@T0) y0))
(x1: @T1 x0) (EQ1: _paco_id (@JMeq.JMeq (@T1 x0) x1 (@T1 y0) y1))
(x2: @T2 x0 x1) (EQ2: _paco_id (@JMeq.JMeq (@T2 x0 x1) x2 (@T2 y0 y1) y2))
(x3: @T3 x0 x1 x2) (EQ3: _paco_id (@JMeq.JMeq (@T3 x0 x1 x2) x3 (@T3 y0 y1 y2) y3))
(x4: @T4 x0 x1 x2 x3) (EQ4: _paco_id (@JMeq.JMeq (@T4 x0 x1 x2 x3) x4 (@T4 y0 y1 y2 y3) y4))
(x5: @T5 x0 x1 x2 x3 x4) (EQ5: _paco_id (@JMeq.JMeq (@T5 x0 x1 x2 x3 x4) x5 (@T5 y0 y1 y2 y3 y4) y5))
(x6: @T6 x0 x1 x2 x3 x4 x5) (EQ6: _paco_id (@JMeq.JMeq (@T6 x0 x1 x2 x3 x4 x5) x6 (@T6 y0 y1 y2 y3 y4 y5) y6))
(x7: @T7 x0 x1 x2 x3 x4 x5 x6) (EQ7: _paco_id (@JMeq.JMeq (@T7 x0 x1 x2 x3 x4 x5 x6) x7 (@T7 y0 y1 y2 y3 y4 y5 y6) y7))
(x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (EQ8: _paco_id (@JMeq.JMeq (@T8 x0 x1 x2 x3 x4 x5 x6 x7) x8 (@T8 y0 y1 y2 y3 y4 y5 y6 y7) y8))
, @paco9 x0 x1 x2 x3 x4 x5 x6 x7 x8),
@paco9 y0 y1 y2 y3 y4 y5 y6 y7 y8.
Proof. intros. apply CONVERT; reflexivity. Qed.

Ltac paco_cont9 e0 e1 e2 e3 e4 e5 e6 e7 e8 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
let x6 := fresh "_paco_v_" in let EQ6 := fresh "_paco_EQ_" in
let x7 := fresh "_paco_v_" in let EQ7 := fresh "_paco_EQ_" in
let x8 := fresh "_paco_v_" in let EQ8 := fresh "_paco_EQ_" in
apply _paco_convert9;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
intros x5 EQ5;
intros x6 EQ6;
intros x7 EQ7;
intros x8 EQ8;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 EQ8)))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8;
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

Tactic Notation "paco_post9" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match9 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
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
(x0: @T0) (EQ0: _paco_id (@JMeq.JMeq (@T0) x0 (@T0) y0))
(x1: @T1 x0) (EQ1: _paco_id (@JMeq.JMeq (@T1 x0) x1 (@T1 y0) y1))
(x2: @T2 x0 x1) (EQ2: _paco_id (@JMeq.JMeq (@T2 x0 x1) x2 (@T2 y0 y1) y2))
(x3: @T3 x0 x1 x2) (EQ3: _paco_id (@JMeq.JMeq (@T3 x0 x1 x2) x3 (@T3 y0 y1 y2) y3))
(x4: @T4 x0 x1 x2 x3) (EQ4: _paco_id (@JMeq.JMeq (@T4 x0 x1 x2 x3) x4 (@T4 y0 y1 y2 y3) y4))
(x5: @T5 x0 x1 x2 x3 x4) (EQ5: _paco_id (@JMeq.JMeq (@T5 x0 x1 x2 x3 x4) x5 (@T5 y0 y1 y2 y3 y4) y5))
(x6: @T6 x0 x1 x2 x3 x4 x5) (EQ6: _paco_id (@JMeq.JMeq (@T6 x0 x1 x2 x3 x4 x5) x6 (@T6 y0 y1 y2 y3 y4 y5) y6))
(x7: @T7 x0 x1 x2 x3 x4 x5 x6) (EQ7: _paco_id (@JMeq.JMeq (@T7 x0 x1 x2 x3 x4 x5 x6) x7 (@T7 y0 y1 y2 y3 y4 y5 y6) y7))
(x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (EQ8: _paco_id (@JMeq.JMeq (@T8 x0 x1 x2 x3 x4 x5 x6 x7) x8 (@T8 y0 y1 y2 y3 y4 y5 y6 y7) y8))
(x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (EQ9: _paco_id (@JMeq.JMeq (@T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x9 (@T9 y0 y1 y2 y3 y4 y5 y6 y7 y8) y9))
, @paco10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9),
@paco10 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9.
Proof. intros. apply CONVERT; reflexivity. Qed.

Ltac paco_cont10 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
let x6 := fresh "_paco_v_" in let EQ6 := fresh "_paco_EQ_" in
let x7 := fresh "_paco_v_" in let EQ7 := fresh "_paco_EQ_" in
let x8 := fresh "_paco_v_" in let EQ8 := fresh "_paco_EQ_" in
let x9 := fresh "_paco_v_" in let EQ9 := fresh "_paco_EQ_" in
apply _paco_convert10;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
intros x5 EQ5;
intros x6 EQ6;
intros x7 EQ7;
intros x8 EQ8;
intros x9 EQ9;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 EQ9))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9;
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

Tactic Notation "paco_post10" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match10 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
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
(x0: @T0) (EQ0: _paco_id (@JMeq.JMeq (@T0) x0 (@T0) y0))
(x1: @T1 x0) (EQ1: _paco_id (@JMeq.JMeq (@T1 x0) x1 (@T1 y0) y1))
(x2: @T2 x0 x1) (EQ2: _paco_id (@JMeq.JMeq (@T2 x0 x1) x2 (@T2 y0 y1) y2))
(x3: @T3 x0 x1 x2) (EQ3: _paco_id (@JMeq.JMeq (@T3 x0 x1 x2) x3 (@T3 y0 y1 y2) y3))
(x4: @T4 x0 x1 x2 x3) (EQ4: _paco_id (@JMeq.JMeq (@T4 x0 x1 x2 x3) x4 (@T4 y0 y1 y2 y3) y4))
(x5: @T5 x0 x1 x2 x3 x4) (EQ5: _paco_id (@JMeq.JMeq (@T5 x0 x1 x2 x3 x4) x5 (@T5 y0 y1 y2 y3 y4) y5))
(x6: @T6 x0 x1 x2 x3 x4 x5) (EQ6: _paco_id (@JMeq.JMeq (@T6 x0 x1 x2 x3 x4 x5) x6 (@T6 y0 y1 y2 y3 y4 y5) y6))
(x7: @T7 x0 x1 x2 x3 x4 x5 x6) (EQ7: _paco_id (@JMeq.JMeq (@T7 x0 x1 x2 x3 x4 x5 x6) x7 (@T7 y0 y1 y2 y3 y4 y5 y6) y7))
(x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (EQ8: _paco_id (@JMeq.JMeq (@T8 x0 x1 x2 x3 x4 x5 x6 x7) x8 (@T8 y0 y1 y2 y3 y4 y5 y6 y7) y8))
(x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (EQ9: _paco_id (@JMeq.JMeq (@T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x9 (@T9 y0 y1 y2 y3 y4 y5 y6 y7 y8) y9))
(x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (EQ10: _paco_id (@JMeq.JMeq (@T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) x10 (@T10 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9) y10))
, @paco11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10),
@paco11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10.
Proof. intros. apply CONVERT; reflexivity. Qed.

Ltac paco_cont11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
let x6 := fresh "_paco_v_" in let EQ6 := fresh "_paco_EQ_" in
let x7 := fresh "_paco_v_" in let EQ7 := fresh "_paco_EQ_" in
let x8 := fresh "_paco_v_" in let EQ8 := fresh "_paco_EQ_" in
let x9 := fresh "_paco_v_" in let EQ9 := fresh "_paco_EQ_" in
let x10 := fresh "_paco_v_" in let EQ10 := fresh "_paco_EQ_" in
apply _paco_convert11;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
intros x5 EQ5;
intros x6 EQ6;
intros x7 EQ7;
intros x8 EQ8;
intros x9 EQ9;
intros x10 EQ10;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 EQ10)))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10;
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

Tactic Notation "paco_post11" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match11 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
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
(x0: @T0) (EQ0: _paco_id (@JMeq.JMeq (@T0) x0 (@T0) y0))
(x1: @T1 x0) (EQ1: _paco_id (@JMeq.JMeq (@T1 x0) x1 (@T1 y0) y1))
(x2: @T2 x0 x1) (EQ2: _paco_id (@JMeq.JMeq (@T2 x0 x1) x2 (@T2 y0 y1) y2))
(x3: @T3 x0 x1 x2) (EQ3: _paco_id (@JMeq.JMeq (@T3 x0 x1 x2) x3 (@T3 y0 y1 y2) y3))
(x4: @T4 x0 x1 x2 x3) (EQ4: _paco_id (@JMeq.JMeq (@T4 x0 x1 x2 x3) x4 (@T4 y0 y1 y2 y3) y4))
(x5: @T5 x0 x1 x2 x3 x4) (EQ5: _paco_id (@JMeq.JMeq (@T5 x0 x1 x2 x3 x4) x5 (@T5 y0 y1 y2 y3 y4) y5))
(x6: @T6 x0 x1 x2 x3 x4 x5) (EQ6: _paco_id (@JMeq.JMeq (@T6 x0 x1 x2 x3 x4 x5) x6 (@T6 y0 y1 y2 y3 y4 y5) y6))
(x7: @T7 x0 x1 x2 x3 x4 x5 x6) (EQ7: _paco_id (@JMeq.JMeq (@T7 x0 x1 x2 x3 x4 x5 x6) x7 (@T7 y0 y1 y2 y3 y4 y5 y6) y7))
(x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (EQ8: _paco_id (@JMeq.JMeq (@T8 x0 x1 x2 x3 x4 x5 x6 x7) x8 (@T8 y0 y1 y2 y3 y4 y5 y6 y7) y8))
(x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (EQ9: _paco_id (@JMeq.JMeq (@T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x9 (@T9 y0 y1 y2 y3 y4 y5 y6 y7 y8) y9))
(x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (EQ10: _paco_id (@JMeq.JMeq (@T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) x10 (@T10 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9) y10))
(x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (EQ11: _paco_id (@JMeq.JMeq (@T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) x11 (@T11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10) y11))
, @paco12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11),
@paco12 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11.
Proof. intros. apply CONVERT; reflexivity. Qed.

Ltac paco_cont12 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
let x6 := fresh "_paco_v_" in let EQ6 := fresh "_paco_EQ_" in
let x7 := fresh "_paco_v_" in let EQ7 := fresh "_paco_EQ_" in
let x8 := fresh "_paco_v_" in let EQ8 := fresh "_paco_EQ_" in
let x9 := fresh "_paco_v_" in let EQ9 := fresh "_paco_EQ_" in
let x10 := fresh "_paco_v_" in let EQ10 := fresh "_paco_EQ_" in
let x11 := fresh "_paco_v_" in let EQ11 := fresh "_paco_EQ_" in
apply _paco_convert12;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
intros x5 EQ5;
intros x6 EQ6;
intros x7 EQ7;
intros x8 EQ8;
intros x9 EQ9;
intros x10 EQ10;
intros x11 EQ11;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 EQ11))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11;
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

Tactic Notation "paco_post12" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match12 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
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
(x0: @T0) (EQ0: _paco_id (@JMeq.JMeq (@T0) x0 (@T0) y0))
(x1: @T1 x0) (EQ1: _paco_id (@JMeq.JMeq (@T1 x0) x1 (@T1 y0) y1))
(x2: @T2 x0 x1) (EQ2: _paco_id (@JMeq.JMeq (@T2 x0 x1) x2 (@T2 y0 y1) y2))
(x3: @T3 x0 x1 x2) (EQ3: _paco_id (@JMeq.JMeq (@T3 x0 x1 x2) x3 (@T3 y0 y1 y2) y3))
(x4: @T4 x0 x1 x2 x3) (EQ4: _paco_id (@JMeq.JMeq (@T4 x0 x1 x2 x3) x4 (@T4 y0 y1 y2 y3) y4))
(x5: @T5 x0 x1 x2 x3 x4) (EQ5: _paco_id (@JMeq.JMeq (@T5 x0 x1 x2 x3 x4) x5 (@T5 y0 y1 y2 y3 y4) y5))
(x6: @T6 x0 x1 x2 x3 x4 x5) (EQ6: _paco_id (@JMeq.JMeq (@T6 x0 x1 x2 x3 x4 x5) x6 (@T6 y0 y1 y2 y3 y4 y5) y6))
(x7: @T7 x0 x1 x2 x3 x4 x5 x6) (EQ7: _paco_id (@JMeq.JMeq (@T7 x0 x1 x2 x3 x4 x5 x6) x7 (@T7 y0 y1 y2 y3 y4 y5 y6) y7))
(x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (EQ8: _paco_id (@JMeq.JMeq (@T8 x0 x1 x2 x3 x4 x5 x6 x7) x8 (@T8 y0 y1 y2 y3 y4 y5 y6 y7) y8))
(x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (EQ9: _paco_id (@JMeq.JMeq (@T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x9 (@T9 y0 y1 y2 y3 y4 y5 y6 y7 y8) y9))
(x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (EQ10: _paco_id (@JMeq.JMeq (@T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) x10 (@T10 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9) y10))
(x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (EQ11: _paco_id (@JMeq.JMeq (@T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) x11 (@T11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10) y11))
(x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (EQ12: _paco_id (@JMeq.JMeq (@T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) x12 (@T12 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11) y12))
, @paco13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12),
@paco13 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12.
Proof. intros. apply CONVERT; reflexivity. Qed.

Ltac paco_cont13 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
let x6 := fresh "_paco_v_" in let EQ6 := fresh "_paco_EQ_" in
let x7 := fresh "_paco_v_" in let EQ7 := fresh "_paco_EQ_" in
let x8 := fresh "_paco_v_" in let EQ8 := fresh "_paco_EQ_" in
let x9 := fresh "_paco_v_" in let EQ9 := fresh "_paco_EQ_" in
let x10 := fresh "_paco_v_" in let EQ10 := fresh "_paco_EQ_" in
let x11 := fresh "_paco_v_" in let EQ11 := fresh "_paco_EQ_" in
let x12 := fresh "_paco_v_" in let EQ12 := fresh "_paco_EQ_" in
apply _paco_convert13;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
intros x5 EQ5;
intros x6 EQ6;
intros x7 EQ7;
intros x8 EQ8;
intros x9 EQ9;
intros x10 EQ10;
intros x11 EQ11;
intros x12 EQ12;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 EQ12)))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12;
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

Tactic Notation "paco_post13" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match13 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
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
(x0: @T0) (EQ0: _paco_id (@JMeq.JMeq (@T0) x0 (@T0) y0))
(x1: @T1 x0) (EQ1: _paco_id (@JMeq.JMeq (@T1 x0) x1 (@T1 y0) y1))
(x2: @T2 x0 x1) (EQ2: _paco_id (@JMeq.JMeq (@T2 x0 x1) x2 (@T2 y0 y1) y2))
(x3: @T3 x0 x1 x2) (EQ3: _paco_id (@JMeq.JMeq (@T3 x0 x1 x2) x3 (@T3 y0 y1 y2) y3))
(x4: @T4 x0 x1 x2 x3) (EQ4: _paco_id (@JMeq.JMeq (@T4 x0 x1 x2 x3) x4 (@T4 y0 y1 y2 y3) y4))
(x5: @T5 x0 x1 x2 x3 x4) (EQ5: _paco_id (@JMeq.JMeq (@T5 x0 x1 x2 x3 x4) x5 (@T5 y0 y1 y2 y3 y4) y5))
(x6: @T6 x0 x1 x2 x3 x4 x5) (EQ6: _paco_id (@JMeq.JMeq (@T6 x0 x1 x2 x3 x4 x5) x6 (@T6 y0 y1 y2 y3 y4 y5) y6))
(x7: @T7 x0 x1 x2 x3 x4 x5 x6) (EQ7: _paco_id (@JMeq.JMeq (@T7 x0 x1 x2 x3 x4 x5 x6) x7 (@T7 y0 y1 y2 y3 y4 y5 y6) y7))
(x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (EQ8: _paco_id (@JMeq.JMeq (@T8 x0 x1 x2 x3 x4 x5 x6 x7) x8 (@T8 y0 y1 y2 y3 y4 y5 y6 y7) y8))
(x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (EQ9: _paco_id (@JMeq.JMeq (@T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x9 (@T9 y0 y1 y2 y3 y4 y5 y6 y7 y8) y9))
(x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (EQ10: _paco_id (@JMeq.JMeq (@T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) x10 (@T10 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9) y10))
(x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (EQ11: _paco_id (@JMeq.JMeq (@T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) x11 (@T11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10) y11))
(x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (EQ12: _paco_id (@JMeq.JMeq (@T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) x12 (@T12 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11) y12))
(x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (EQ13: _paco_id (@JMeq.JMeq (@T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) x13 (@T13 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12) y13))
, @paco14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13),
@paco14 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13.
Proof. intros. apply CONVERT; reflexivity. Qed.

Ltac paco_cont14 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 :=
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
let x6 := fresh "_paco_v_" in let EQ6 := fresh "_paco_EQ_" in
let x7 := fresh "_paco_v_" in let EQ7 := fresh "_paco_EQ_" in
let x8 := fresh "_paco_v_" in let EQ8 := fresh "_paco_EQ_" in
let x9 := fresh "_paco_v_" in let EQ9 := fresh "_paco_EQ_" in
let x10 := fresh "_paco_v_" in let EQ10 := fresh "_paco_EQ_" in
let x11 := fresh "_paco_v_" in let EQ11 := fresh "_paco_EQ_" in
let x12 := fresh "_paco_v_" in let EQ12 := fresh "_paco_EQ_" in
let x13 := fresh "_paco_v_" in let EQ13 := fresh "_paco_EQ_" in
apply _paco_convert14;
intros x0 EQ0;
intros x1 EQ1;
intros x2 EQ2;
intros x3 EQ3;
intros x4 EQ4;
intros x5 EQ5;
intros x6 EQ6;
intros x7 EQ7;
intros x8 EQ8;
intros x9 EQ9;
intros x10 EQ10;
intros x11 EQ11;
intros x12 EQ12;
intros x13 EQ13;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 (conj EQ12 EQ13))))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12 EQ13;
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

Tactic Notation "paco_post14" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match14 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
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

