Require Import JMeq.
Require Import hpattern.
Require Export paconotation.

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

Ltac hrewrite_last e H := let x := fresh "_paco_x_" in
  first [try (set (x:=e) at 17; fail 1);
    first [try (set (x:=e) at 9; fail 1);
      first [try (set (x:=e) at 5; fail 1);
        first [try (set (x:=e) at 3; fail 1);
          first [try (set (x:=e) at 2; fail 1);
            try (hrewrite H at 1)
          | try (hrewrite H at 2) ]
        | first [try (set (x:=e) at 4; fail 1);
            try (hrewrite H at 3)
          | try (hrewrite H at 4) ] ]
      | first [try (set (x:=e) at 7; fail 1);
          first [try (set (x:=e) at 6; fail 1);
            try (hrewrite H at 5)
          | try (hrewrite H at 6)]
        | first [try (set (x:=e) at 8; fail 1);
            try (hrewrite H at 7)
          | try (hrewrite H at 8) ] ] ]
    | first [try (set (x:=e) at 13; fail 1);
        first [try (set (x:=e) at 11; fail 1);
          first [try (set (x:=e) at 10; fail 1);
            try (hrewrite H at 9)
          | try (hrewrite H at 10) ]
        | first [try (set (x:=e) at 12; fail 1);
            try (hrewrite H at 11)
          | try (hrewrite H at 12) ] ]
      | first [try (set (x:=e) at 15; fail 1);
          first [try (set (x:=e) at 14; fail 1);
            try (hrewrite H at 13)
          | try (hrewrite H at 14)]
        | first [try (set (x:=e) at 16; fail 1);
            try (hrewrite H at 15)
          | try (hrewrite H at 16) ] ] ] ]
  | first [try (set (x:=e) at 25; fail 1);
      first [try (set (x:=e) at 21; fail 1);
        first [try (set (x:=e) at 19; fail 1);
          first [try (set (x:=e) at 18; fail 1);
            try (hrewrite H at 17)
          | try (hrewrite H at 18) ]
        | first [try (set (x:=e) at 20; fail 1);
            try (hrewrite H at 19)
          | try (hrewrite H at 20) ] ]
      | first [try (set (x:=e) at 23; fail 1);
          first [try (set (x:=e) at 22; fail 1);
            try (hrewrite H at 21)
          | try (hrewrite H at 22)]
        | first [try (set (x:=e) at 24; fail 1);
            try (hrewrite H at 23)
          | try (hrewrite H at 24) ] ] ]
    | first [try (set (x:=e) at 29; fail 1);
        first [try (set (x:=e) at 27; fail 1);
          first [try (set (x:=e) at 26; fail 1);
            try (hrewrite H at 25)
          | try (hrewrite H at 26) ]
        | first [try (set (x:=e) at 28; fail 1);
            try (hrewrite H at 27)
          | try (hrewrite H at 28) ] ]
      | first [try (set (x:=e) at 31; fail 1);
          first [try (set (x:=e) at 30; fail 1);
            try (hrewrite H at 29)
          | try (hrewrite H at 30)]
        | first [try (set (x:=e) at 32; fail 1);
            try (hrewrite H at 31)
          | try (hrewrite H at 32) ] ] ] ] ]
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
  let CIH := fresh CIH in let TMP := fresh "_paco_TMP_" in
  intro CIH; paco_simp_hyp CIH;
  generalize _paco_mark_cons; intro TMP;
  repeat intro; paco_rename_last; paco_destruct_hyp _paco_mark;
  simplJM; paco_revert_hyp _paco_mark.

Ltac paco_ren_r nr cr :=
  first [rename cr into nr | let nr := fresh nr in rename cr into nr].

Ltac paco_ren_pr pr cr := rename cr into pr.

Ltac paco_revert :=
  match goal with [H: _ |- _] => revert H end.

Ltac paco_cofix_auto :=
  cofix; repeat intro;
  match goal with [H: _ |- _] => destruct H end; econstructor;
  try (match goal with [H: _|-_] => apply H end); intros;
  lazymatch goal with [PR: _ |- _] => match goal with [H: _ |- _] => apply H in PR end end;
  repeat match goal with [ H : _ \/ _ |- _] => destruct H end; first [eauto; fail|eauto 10].

(** *** Arity 0
*)

Ltac paco_cont0 :=
generalize _paco_foo_cons; paco_generalize_hyp _paco_mark.

Ltac paco_pre0 :=
generalize _paco_mark_cons; repeat intro; paco_cont0.

Ltac paco_post_match0 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| (pacoid _) -> _ => clear H; tac1 cr
| ?pr -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post0" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match0 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 1
*)

Ltac paco_cont1 e0 := 
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
paco_convert e0 x0 EQ0;
intros x0 EQ0;
generalize EQ0; clear EQ0;
move x0 at top; 
paco_generalize_hyp _paco_mark; revert x0.

Lemma _paco_pre1: forall T0 (gf: rel1 T0) x0
(X: let gf' := gf in gf' x0), gf x0.
Proof. intros; apply X. Defined.

Ltac paco_pre1 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre1; intro X;
match goal with
| |- _ ?e0 => unfold X; clear X; paco_cont1 e0
end.

Ltac paco_post_match1 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _, (pacoid _) _ -> _ => clear H; tac1 cr
| forall _, ?pr _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post1" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match1 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 2
*)

Ltac paco_cont2 e0 e1 := 
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
apply _paco_pre2; intro X;
match goal with
| |- _ ?e0 ?e1 => unfold X; clear X; paco_cont2 e0 e1
end.

Ltac paco_post_match2 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _, (pacoid _) _ _ -> _ => clear H; tac1 cr
| forall _ _, ?pr _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post2" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match2 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 3
*)

Ltac paco_cont3 e0 e1 e2 := 
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
apply _paco_pre3; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 => unfold X; clear X; paco_cont3 e0 e1 e2
end.

Ltac paco_post_match3 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _, (pacoid _) _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _, ?pr _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post3" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match3 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 4
*)

Ltac paco_cont4 e0 e1 e2 e3 := 
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
apply _paco_pre4; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 => unfold X; clear X; paco_cont4 e0 e1 e2 e3
end.

Ltac paco_post_match4 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _, (pacoid _) _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _, ?pr _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post4" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match4 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 5
*)

Ltac paco_cont5 e0 e1 e2 e3 e4 := 
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
apply _paco_pre5; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 => unfold X; clear X; paco_cont5 e0 e1 e2 e3 e4
end.

Ltac paco_post_match5 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _, (pacoid _) _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _, ?pr _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post5" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match5 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 6
*)

Ltac paco_cont6 e0 e1 e2 e3 e4 e5 := 
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
apply _paco_pre6; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 => unfold X; clear X; paco_cont6 e0 e1 e2 e3 e4 e5
end.

Ltac paco_post_match6 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _, ?pr _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post6" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match6 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 7
*)

Ltac paco_cont7 e0 e1 e2 e3 e4 e5 e6 := 
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
let x6 := fresh "_paco_v_" in let EQ6 := fresh "_paco_EQ_" in
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
apply _paco_pre7; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 => unfold X; clear X; paco_cont7 e0 e1 e2 e3 e4 e5 e6
end.

Ltac paco_post_match7 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post7" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match7 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 8
*)

Ltac paco_cont8 e0 e1 e2 e3 e4 e5 e6 e7 := 
let x0 := fresh "_paco_v_" in let EQ0 := fresh "_paco_EQ_" in
let x1 := fresh "_paco_v_" in let EQ1 := fresh "_paco_EQ_" in
let x2 := fresh "_paco_v_" in let EQ2 := fresh "_paco_EQ_" in
let x3 := fresh "_paco_v_" in let EQ3 := fresh "_paco_EQ_" in
let x4 := fresh "_paco_v_" in let EQ4 := fresh "_paco_EQ_" in
let x5 := fresh "_paco_v_" in let EQ5 := fresh "_paco_EQ_" in
let x6 := fresh "_paco_v_" in let EQ6 := fresh "_paco_EQ_" in
let x7 := fresh "_paco_v_" in let EQ7 := fresh "_paco_EQ_" in
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
apply _paco_pre8; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 => unfold X; clear X; paco_cont8 e0 e1 e2 e3 e4 e5 e6 e7
end.

Ltac paco_post_match8 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post8" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match8 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 9
*)

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
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
apply _paco_pre9; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 => unfold X; clear X; paco_cont9 e0 e1 e2 e3 e4 e5 e6 e7 e8
end.

Ltac paco_post_match9 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post9" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match9 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 10
*)

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
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
apply _paco_pre10; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 => unfold X; clear X; paco_cont10 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
end.

Ltac paco_post_match10 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post10" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match10 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 11
*)

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
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
apply _paco_pre11; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 => unfold X; clear X; paco_cont11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
end.

Ltac paco_post_match11 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post11" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match11 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 12
*)

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
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
apply _paco_pre12; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 => unfold X; clear X; paco_cont12 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
end.

Ltac paco_post_match12 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post12" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match12 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 13
*)

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
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
apply _paco_pre13; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 => unfold X; clear X; paco_cont13 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
end.

Ltac paco_post_match13 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post13" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match13 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 14
*)

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
paco_convert e13 x13 EQ13;
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
apply _paco_pre14; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 => unfold X; clear X; paco_cont14 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
end.

Ltac paco_post_match14 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post14" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match14 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 15
*)

Ltac paco_cont15 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 := 
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
let x14 := fresh "_paco_v_" in let EQ14 := fresh "_paco_EQ_" in
paco_convert e14 x14 EQ14;
paco_convert e13 x13 EQ13;
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
intros x14 EQ14;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 (conj EQ12 (conj EQ13 EQ14)))))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12 EQ13 EQ14;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top; move x13 at top; move x14 at top; 
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.

Lemma _paco_pre15: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.
Proof. intros; apply X. Defined.

Ltac paco_pre15 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre15; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 => unfold X; clear X; paco_cont15 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
end.

Ltac paco_post_match15 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post15" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match15 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 16
*)

Ltac paco_cont16 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 := 
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
let x14 := fresh "_paco_v_" in let EQ14 := fresh "_paco_EQ_" in
let x15 := fresh "_paco_v_" in let EQ15 := fresh "_paco_EQ_" in
paco_convert e15 x15 EQ15;
paco_convert e14 x14 EQ14;
paco_convert e13 x13 EQ13;
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
intros x14 EQ14;
intros x15 EQ15;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 (conj EQ12 (conj EQ13 (conj EQ14 EQ15))))))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12 EQ13 EQ14 EQ15;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top; move x13 at top; move x14 at top; move x15 at top; 
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.

Lemma _paco_pre16: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 (gf: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.
Proof. intros; apply X. Defined.

Ltac paco_pre16 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre16; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 ?e15 => unfold X; clear X; paco_cont16 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
end.

Ltac paco_post_match16 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post16" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match16 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 17
*)

Ltac paco_cont17 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 := 
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
let x14 := fresh "_paco_v_" in let EQ14 := fresh "_paco_EQ_" in
let x15 := fresh "_paco_v_" in let EQ15 := fresh "_paco_EQ_" in
let x16 := fresh "_paco_v_" in let EQ16 := fresh "_paco_EQ_" in
paco_convert e16 x16 EQ16;
paco_convert e15 x15 EQ15;
paco_convert e14 x14 EQ14;
paco_convert e13 x13 EQ13;
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
intros x14 EQ14;
intros x15 EQ15;
intros x16 EQ16;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 (conj EQ12 (conj EQ13 (conj EQ14 (conj EQ15 EQ16)))))))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12 EQ13 EQ14 EQ15 EQ16;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top; move x13 at top; move x14 at top; move x15 at top; move x16 at top; 
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16.

Lemma _paco_pre17: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 (gf: rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16.
Proof. intros; apply X. Defined.

Ltac paco_pre17 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre17; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 ?e15 ?e16 => unfold X; clear X; paco_cont17 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16
end.

Ltac paco_post_match17 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post17" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match17 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 18
*)

Ltac paco_cont18 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 := 
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
let x14 := fresh "_paco_v_" in let EQ14 := fresh "_paco_EQ_" in
let x15 := fresh "_paco_v_" in let EQ15 := fresh "_paco_EQ_" in
let x16 := fresh "_paco_v_" in let EQ16 := fresh "_paco_EQ_" in
let x17 := fresh "_paco_v_" in let EQ17 := fresh "_paco_EQ_" in
paco_convert e17 x17 EQ17;
paco_convert e16 x16 EQ16;
paco_convert e15 x15 EQ15;
paco_convert e14 x14 EQ14;
paco_convert e13 x13 EQ13;
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
intros x14 EQ14;
intros x15 EQ15;
intros x16 EQ16;
intros x17 EQ17;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 (conj EQ12 (conj EQ13 (conj EQ14 (conj EQ15 (conj EQ16 EQ17))))))))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12 EQ13 EQ14 EQ15 EQ16 EQ17;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top; move x13 at top; move x14 at top; move x15 at top; move x16 at top; move x17 at top; 
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17.

Lemma _paco_pre18: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 (gf: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17.
Proof. intros; apply X. Defined.

Ltac paco_pre18 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre18; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 ?e15 ?e16 ?e17 => unfold X; clear X; paco_cont18 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17
end.

Ltac paco_post_match18 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post18" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match18 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 19
*)

Ltac paco_cont19 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 := 
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
let x14 := fresh "_paco_v_" in let EQ14 := fresh "_paco_EQ_" in
let x15 := fresh "_paco_v_" in let EQ15 := fresh "_paco_EQ_" in
let x16 := fresh "_paco_v_" in let EQ16 := fresh "_paco_EQ_" in
let x17 := fresh "_paco_v_" in let EQ17 := fresh "_paco_EQ_" in
let x18 := fresh "_paco_v_" in let EQ18 := fresh "_paco_EQ_" in
paco_convert e18 x18 EQ18;
paco_convert e17 x17 EQ17;
paco_convert e16 x16 EQ16;
paco_convert e15 x15 EQ15;
paco_convert e14 x14 EQ14;
paco_convert e13 x13 EQ13;
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
intros x14 EQ14;
intros x15 EQ15;
intros x16 EQ16;
intros x17 EQ17;
intros x18 EQ18;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 (conj EQ12 (conj EQ13 (conj EQ14 (conj EQ15 (conj EQ16 (conj EQ17 EQ18)))))))))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12 EQ13 EQ14 EQ15 EQ16 EQ17 EQ18;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top; move x13 at top; move x14 at top; move x15 at top; move x16 at top; move x17 at top; move x18 at top; 
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18.

Lemma _paco_pre19: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 (gf: rel19 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18.
Proof. intros; apply X. Defined.

Ltac paco_pre19 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre19; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 ?e15 ?e16 ?e17 ?e18 => unfold X; clear X; paco_cont19 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
end.

Ltac paco_post_match19 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post19" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match19 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 20
*)

Ltac paco_cont20 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 := 
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
let x14 := fresh "_paco_v_" in let EQ14 := fresh "_paco_EQ_" in
let x15 := fresh "_paco_v_" in let EQ15 := fresh "_paco_EQ_" in
let x16 := fresh "_paco_v_" in let EQ16 := fresh "_paco_EQ_" in
let x17 := fresh "_paco_v_" in let EQ17 := fresh "_paco_EQ_" in
let x18 := fresh "_paco_v_" in let EQ18 := fresh "_paco_EQ_" in
let x19 := fresh "_paco_v_" in let EQ19 := fresh "_paco_EQ_" in
paco_convert e19 x19 EQ19;
paco_convert e18 x18 EQ18;
paco_convert e17 x17 EQ17;
paco_convert e16 x16 EQ16;
paco_convert e15 x15 EQ15;
paco_convert e14 x14 EQ14;
paco_convert e13 x13 EQ13;
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
intros x14 EQ14;
intros x15 EQ15;
intros x16 EQ16;
intros x17 EQ17;
intros x18 EQ18;
intros x19 EQ19;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 (conj EQ12 (conj EQ13 (conj EQ14 (conj EQ15 (conj EQ16 (conj EQ17 (conj EQ18 EQ19))))))))))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12 EQ13 EQ14 EQ15 EQ16 EQ17 EQ18 EQ19;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top; move x13 at top; move x14 at top; move x15 at top; move x16 at top; move x17 at top; move x18 at top; move x19 at top; 
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19.

Lemma _paco_pre20: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 (gf: rel20 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19.
Proof. intros; apply X. Defined.

Ltac paco_pre20 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre20; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 ?e15 ?e16 ?e17 ?e18 ?e19 => unfold X; clear X; paco_cont20 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19
end.

Ltac paco_post_match20 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post20" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match20 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 21
*)

Ltac paco_cont21 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 := 
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
let x14 := fresh "_paco_v_" in let EQ14 := fresh "_paco_EQ_" in
let x15 := fresh "_paco_v_" in let EQ15 := fresh "_paco_EQ_" in
let x16 := fresh "_paco_v_" in let EQ16 := fresh "_paco_EQ_" in
let x17 := fresh "_paco_v_" in let EQ17 := fresh "_paco_EQ_" in
let x18 := fresh "_paco_v_" in let EQ18 := fresh "_paco_EQ_" in
let x19 := fresh "_paco_v_" in let EQ19 := fresh "_paco_EQ_" in
let x20 := fresh "_paco_v_" in let EQ20 := fresh "_paco_EQ_" in
paco_convert e20 x20 EQ20;
paco_convert e19 x19 EQ19;
paco_convert e18 x18 EQ18;
paco_convert e17 x17 EQ17;
paco_convert e16 x16 EQ16;
paco_convert e15 x15 EQ15;
paco_convert e14 x14 EQ14;
paco_convert e13 x13 EQ13;
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
intros x14 EQ14;
intros x15 EQ15;
intros x16 EQ16;
intros x17 EQ17;
intros x18 EQ18;
intros x19 EQ19;
intros x20 EQ20;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 (conj EQ12 (conj EQ13 (conj EQ14 (conj EQ15 (conj EQ16 (conj EQ17 (conj EQ18 (conj EQ19 EQ20)))))))))))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12 EQ13 EQ14 EQ15 EQ16 EQ17 EQ18 EQ19 EQ20;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top; move x13 at top; move x14 at top; move x15 at top; move x16 at top; move x17 at top; move x18 at top; move x19 at top; move x20 at top; 
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20.

Lemma _paco_pre21: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 (gf: rel21 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20.
Proof. intros; apply X. Defined.

Ltac paco_pre21 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre21; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 ?e15 ?e16 ?e17 ?e18 ?e19 ?e20 => unfold X; clear X; paco_cont21 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20
end.

Ltac paco_post_match21 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post21" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match21 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 22
*)

Ltac paco_cont22 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 := 
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
let x14 := fresh "_paco_v_" in let EQ14 := fresh "_paco_EQ_" in
let x15 := fresh "_paco_v_" in let EQ15 := fresh "_paco_EQ_" in
let x16 := fresh "_paco_v_" in let EQ16 := fresh "_paco_EQ_" in
let x17 := fresh "_paco_v_" in let EQ17 := fresh "_paco_EQ_" in
let x18 := fresh "_paco_v_" in let EQ18 := fresh "_paco_EQ_" in
let x19 := fresh "_paco_v_" in let EQ19 := fresh "_paco_EQ_" in
let x20 := fresh "_paco_v_" in let EQ20 := fresh "_paco_EQ_" in
let x21 := fresh "_paco_v_" in let EQ21 := fresh "_paco_EQ_" in
paco_convert e21 x21 EQ21;
paco_convert e20 x20 EQ20;
paco_convert e19 x19 EQ19;
paco_convert e18 x18 EQ18;
paco_convert e17 x17 EQ17;
paco_convert e16 x16 EQ16;
paco_convert e15 x15 EQ15;
paco_convert e14 x14 EQ14;
paco_convert e13 x13 EQ13;
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
intros x14 EQ14;
intros x15 EQ15;
intros x16 EQ16;
intros x17 EQ17;
intros x18 EQ18;
intros x19 EQ19;
intros x20 EQ20;
intros x21 EQ21;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 (conj EQ12 (conj EQ13 (conj EQ14 (conj EQ15 (conj EQ16 (conj EQ17 (conj EQ18 (conj EQ19 (conj EQ20 EQ21))))))))))))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12 EQ13 EQ14 EQ15 EQ16 EQ17 EQ18 EQ19 EQ20 EQ21;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top; move x13 at top; move x14 at top; move x15 at top; move x16 at top; move x17 at top; move x18 at top; move x19 at top; move x20 at top; move x21 at top; 
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21.

Lemma _paco_pre22: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 (gf: rel22 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21.
Proof. intros; apply X. Defined.

Ltac paco_pre22 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre22; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 ?e15 ?e16 ?e17 ?e18 ?e19 ?e20 ?e21 => unfold X; clear X; paco_cont22 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21
end.

Ltac paco_post_match22 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post22" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match22 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 23
*)

Ltac paco_cont23 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 := 
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
let x14 := fresh "_paco_v_" in let EQ14 := fresh "_paco_EQ_" in
let x15 := fresh "_paco_v_" in let EQ15 := fresh "_paco_EQ_" in
let x16 := fresh "_paco_v_" in let EQ16 := fresh "_paco_EQ_" in
let x17 := fresh "_paco_v_" in let EQ17 := fresh "_paco_EQ_" in
let x18 := fresh "_paco_v_" in let EQ18 := fresh "_paco_EQ_" in
let x19 := fresh "_paco_v_" in let EQ19 := fresh "_paco_EQ_" in
let x20 := fresh "_paco_v_" in let EQ20 := fresh "_paco_EQ_" in
let x21 := fresh "_paco_v_" in let EQ21 := fresh "_paco_EQ_" in
let x22 := fresh "_paco_v_" in let EQ22 := fresh "_paco_EQ_" in
paco_convert e22 x22 EQ22;
paco_convert e21 x21 EQ21;
paco_convert e20 x20 EQ20;
paco_convert e19 x19 EQ19;
paco_convert e18 x18 EQ18;
paco_convert e17 x17 EQ17;
paco_convert e16 x16 EQ16;
paco_convert e15 x15 EQ15;
paco_convert e14 x14 EQ14;
paco_convert e13 x13 EQ13;
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
intros x14 EQ14;
intros x15 EQ15;
intros x16 EQ16;
intros x17 EQ17;
intros x18 EQ18;
intros x19 EQ19;
intros x20 EQ20;
intros x21 EQ21;
intros x22 EQ22;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 (conj EQ12 (conj EQ13 (conj EQ14 (conj EQ15 (conj EQ16 (conj EQ17 (conj EQ18 (conj EQ19 (conj EQ20 (conj EQ21 EQ22)))))))))))))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12 EQ13 EQ14 EQ15 EQ16 EQ17 EQ18 EQ19 EQ20 EQ21 EQ22;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top; move x13 at top; move x14 at top; move x15 at top; move x16 at top; move x17 at top; move x18 at top; move x19 at top; move x20 at top; move x21 at top; move x22 at top; 
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22.

Lemma _paco_pre23: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 (gf: rel23 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22.
Proof. intros; apply X. Defined.

Ltac paco_pre23 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre23; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 ?e15 ?e16 ?e17 ?e18 ?e19 ?e20 ?e21 ?e22 => unfold X; clear X; paco_cont23 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22
end.

Ltac paco_post_match23 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post23" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match23 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 24
*)

Ltac paco_cont24 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 := 
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
let x14 := fresh "_paco_v_" in let EQ14 := fresh "_paco_EQ_" in
let x15 := fresh "_paco_v_" in let EQ15 := fresh "_paco_EQ_" in
let x16 := fresh "_paco_v_" in let EQ16 := fresh "_paco_EQ_" in
let x17 := fresh "_paco_v_" in let EQ17 := fresh "_paco_EQ_" in
let x18 := fresh "_paco_v_" in let EQ18 := fresh "_paco_EQ_" in
let x19 := fresh "_paco_v_" in let EQ19 := fresh "_paco_EQ_" in
let x20 := fresh "_paco_v_" in let EQ20 := fresh "_paco_EQ_" in
let x21 := fresh "_paco_v_" in let EQ21 := fresh "_paco_EQ_" in
let x22 := fresh "_paco_v_" in let EQ22 := fresh "_paco_EQ_" in
let x23 := fresh "_paco_v_" in let EQ23 := fresh "_paco_EQ_" in
paco_convert e23 x23 EQ23;
paco_convert e22 x22 EQ22;
paco_convert e21 x21 EQ21;
paco_convert e20 x20 EQ20;
paco_convert e19 x19 EQ19;
paco_convert e18 x18 EQ18;
paco_convert e17 x17 EQ17;
paco_convert e16 x16 EQ16;
paco_convert e15 x15 EQ15;
paco_convert e14 x14 EQ14;
paco_convert e13 x13 EQ13;
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
intros x14 EQ14;
intros x15 EQ15;
intros x16 EQ16;
intros x17 EQ17;
intros x18 EQ18;
intros x19 EQ19;
intros x20 EQ20;
intros x21 EQ21;
intros x22 EQ22;
intros x23 EQ23;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 (conj EQ12 (conj EQ13 (conj EQ14 (conj EQ15 (conj EQ16 (conj EQ17 (conj EQ18 (conj EQ19 (conj EQ20 (conj EQ21 (conj EQ22 EQ23))))))))))))))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12 EQ13 EQ14 EQ15 EQ16 EQ17 EQ18 EQ19 EQ20 EQ21 EQ22 EQ23;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top; move x13 at top; move x14 at top; move x15 at top; move x16 at top; move x17 at top; move x18 at top; move x19 at top; move x20 at top; move x21 at top; move x22 at top; move x23 at top; 
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23.

Lemma _paco_pre24: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 (gf: rel24 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23.
Proof. intros; apply X. Defined.

Ltac paco_pre24 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre24; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 ?e15 ?e16 ?e17 ?e18 ?e19 ?e20 ?e21 ?e22 ?e23 => unfold X; clear X; paco_cont24 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23
end.

Ltac paco_post_match24 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post24" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match24 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 25
*)

Ltac paco_cont25 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 := 
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
let x14 := fresh "_paco_v_" in let EQ14 := fresh "_paco_EQ_" in
let x15 := fresh "_paco_v_" in let EQ15 := fresh "_paco_EQ_" in
let x16 := fresh "_paco_v_" in let EQ16 := fresh "_paco_EQ_" in
let x17 := fresh "_paco_v_" in let EQ17 := fresh "_paco_EQ_" in
let x18 := fresh "_paco_v_" in let EQ18 := fresh "_paco_EQ_" in
let x19 := fresh "_paco_v_" in let EQ19 := fresh "_paco_EQ_" in
let x20 := fresh "_paco_v_" in let EQ20 := fresh "_paco_EQ_" in
let x21 := fresh "_paco_v_" in let EQ21 := fresh "_paco_EQ_" in
let x22 := fresh "_paco_v_" in let EQ22 := fresh "_paco_EQ_" in
let x23 := fresh "_paco_v_" in let EQ23 := fresh "_paco_EQ_" in
let x24 := fresh "_paco_v_" in let EQ24 := fresh "_paco_EQ_" in
paco_convert e24 x24 EQ24;
paco_convert e23 x23 EQ23;
paco_convert e22 x22 EQ22;
paco_convert e21 x21 EQ21;
paco_convert e20 x20 EQ20;
paco_convert e19 x19 EQ19;
paco_convert e18 x18 EQ18;
paco_convert e17 x17 EQ17;
paco_convert e16 x16 EQ16;
paco_convert e15 x15 EQ15;
paco_convert e14 x14 EQ14;
paco_convert e13 x13 EQ13;
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
intros x14 EQ14;
intros x15 EQ15;
intros x16 EQ16;
intros x17 EQ17;
intros x18 EQ18;
intros x19 EQ19;
intros x20 EQ20;
intros x21 EQ21;
intros x22 EQ22;
intros x23 EQ23;
intros x24 EQ24;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 (conj EQ12 (conj EQ13 (conj EQ14 (conj EQ15 (conj EQ16 (conj EQ17 (conj EQ18 (conj EQ19 (conj EQ20 (conj EQ21 (conj EQ22 (conj EQ23 EQ24)))))))))))))))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12 EQ13 EQ14 EQ15 EQ16 EQ17 EQ18 EQ19 EQ20 EQ21 EQ22 EQ23 EQ24;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top; move x13 at top; move x14 at top; move x15 at top; move x16 at top; move x17 at top; move x18 at top; move x19 at top; move x20 at top; move x21 at top; move x22 at top; move x23 at top; move x24 at top; 
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24.

Lemma _paco_pre25: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 (gf: rel25 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24.
Proof. intros; apply X. Defined.

Ltac paco_pre25 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre25; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 ?e15 ?e16 ?e17 ?e18 ?e19 ?e20 ?e21 ?e22 ?e23 ?e24 => unfold X; clear X; paco_cont25 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24
end.

Ltac paco_post_match25 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post25" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match25 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 26
*)

Ltac paco_cont26 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 := 
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
let x14 := fresh "_paco_v_" in let EQ14 := fresh "_paco_EQ_" in
let x15 := fresh "_paco_v_" in let EQ15 := fresh "_paco_EQ_" in
let x16 := fresh "_paco_v_" in let EQ16 := fresh "_paco_EQ_" in
let x17 := fresh "_paco_v_" in let EQ17 := fresh "_paco_EQ_" in
let x18 := fresh "_paco_v_" in let EQ18 := fresh "_paco_EQ_" in
let x19 := fresh "_paco_v_" in let EQ19 := fresh "_paco_EQ_" in
let x20 := fresh "_paco_v_" in let EQ20 := fresh "_paco_EQ_" in
let x21 := fresh "_paco_v_" in let EQ21 := fresh "_paco_EQ_" in
let x22 := fresh "_paco_v_" in let EQ22 := fresh "_paco_EQ_" in
let x23 := fresh "_paco_v_" in let EQ23 := fresh "_paco_EQ_" in
let x24 := fresh "_paco_v_" in let EQ24 := fresh "_paco_EQ_" in
let x25 := fresh "_paco_v_" in let EQ25 := fresh "_paco_EQ_" in
paco_convert e25 x25 EQ25;
paco_convert e24 x24 EQ24;
paco_convert e23 x23 EQ23;
paco_convert e22 x22 EQ22;
paco_convert e21 x21 EQ21;
paco_convert e20 x20 EQ20;
paco_convert e19 x19 EQ19;
paco_convert e18 x18 EQ18;
paco_convert e17 x17 EQ17;
paco_convert e16 x16 EQ16;
paco_convert e15 x15 EQ15;
paco_convert e14 x14 EQ14;
paco_convert e13 x13 EQ13;
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
intros x14 EQ14;
intros x15 EQ15;
intros x16 EQ16;
intros x17 EQ17;
intros x18 EQ18;
intros x19 EQ19;
intros x20 EQ20;
intros x21 EQ21;
intros x22 EQ22;
intros x23 EQ23;
intros x24 EQ24;
intros x25 EQ25;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 (conj EQ12 (conj EQ13 (conj EQ14 (conj EQ15 (conj EQ16 (conj EQ17 (conj EQ18 (conj EQ19 (conj EQ20 (conj EQ21 (conj EQ22 (conj EQ23 (conj EQ24 EQ25))))))))))))))))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12 EQ13 EQ14 EQ15 EQ16 EQ17 EQ18 EQ19 EQ20 EQ21 EQ22 EQ23 EQ24 EQ25;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top; move x13 at top; move x14 at top; move x15 at top; move x16 at top; move x17 at top; move x18 at top; move x19 at top; move x20 at top; move x21 at top; move x22 at top; move x23 at top; move x24 at top; move x25 at top; 
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25.

Lemma _paco_pre26: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 (gf: rel26 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25.
Proof. intros; apply X. Defined.

Ltac paco_pre26 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre26; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 ?e15 ?e16 ?e17 ?e18 ?e19 ?e20 ?e21 ?e22 ?e23 ?e24 ?e25 => unfold X; clear X; paco_cont26 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25
end.

Ltac paco_post_match26 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post26" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match26 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 27
*)

Ltac paco_cont27 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 := 
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
let x14 := fresh "_paco_v_" in let EQ14 := fresh "_paco_EQ_" in
let x15 := fresh "_paco_v_" in let EQ15 := fresh "_paco_EQ_" in
let x16 := fresh "_paco_v_" in let EQ16 := fresh "_paco_EQ_" in
let x17 := fresh "_paco_v_" in let EQ17 := fresh "_paco_EQ_" in
let x18 := fresh "_paco_v_" in let EQ18 := fresh "_paco_EQ_" in
let x19 := fresh "_paco_v_" in let EQ19 := fresh "_paco_EQ_" in
let x20 := fresh "_paco_v_" in let EQ20 := fresh "_paco_EQ_" in
let x21 := fresh "_paco_v_" in let EQ21 := fresh "_paco_EQ_" in
let x22 := fresh "_paco_v_" in let EQ22 := fresh "_paco_EQ_" in
let x23 := fresh "_paco_v_" in let EQ23 := fresh "_paco_EQ_" in
let x24 := fresh "_paco_v_" in let EQ24 := fresh "_paco_EQ_" in
let x25 := fresh "_paco_v_" in let EQ25 := fresh "_paco_EQ_" in
let x26 := fresh "_paco_v_" in let EQ26 := fresh "_paco_EQ_" in
paco_convert e26 x26 EQ26;
paco_convert e25 x25 EQ25;
paco_convert e24 x24 EQ24;
paco_convert e23 x23 EQ23;
paco_convert e22 x22 EQ22;
paco_convert e21 x21 EQ21;
paco_convert e20 x20 EQ20;
paco_convert e19 x19 EQ19;
paco_convert e18 x18 EQ18;
paco_convert e17 x17 EQ17;
paco_convert e16 x16 EQ16;
paco_convert e15 x15 EQ15;
paco_convert e14 x14 EQ14;
paco_convert e13 x13 EQ13;
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
intros x14 EQ14;
intros x15 EQ15;
intros x16 EQ16;
intros x17 EQ17;
intros x18 EQ18;
intros x19 EQ19;
intros x20 EQ20;
intros x21 EQ21;
intros x22 EQ22;
intros x23 EQ23;
intros x24 EQ24;
intros x25 EQ25;
intros x26 EQ26;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 (conj EQ12 (conj EQ13 (conj EQ14 (conj EQ15 (conj EQ16 (conj EQ17 (conj EQ18 (conj EQ19 (conj EQ20 (conj EQ21 (conj EQ22 (conj EQ23 (conj EQ24 (conj EQ25 EQ26)))))))))))))))))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12 EQ13 EQ14 EQ15 EQ16 EQ17 EQ18 EQ19 EQ20 EQ21 EQ22 EQ23 EQ24 EQ25 EQ26;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top; move x13 at top; move x14 at top; move x15 at top; move x16 at top; move x17 at top; move x18 at top; move x19 at top; move x20 at top; move x21 at top; move x22 at top; move x23 at top; move x24 at top; move x25 at top; move x26 at top; 
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26.

Lemma _paco_pre27: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 (gf: rel27 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26.
Proof. intros; apply X. Defined.

Ltac paco_pre27 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre27; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 ?e15 ?e16 ?e17 ?e18 ?e19 ?e20 ?e21 ?e22 ?e23 ?e24 ?e25 ?e26 => unfold X; clear X; paco_cont27 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26
end.

Ltac paco_post_match27 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post27" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match27 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 28
*)

Ltac paco_cont28 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 := 
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
let x14 := fresh "_paco_v_" in let EQ14 := fresh "_paco_EQ_" in
let x15 := fresh "_paco_v_" in let EQ15 := fresh "_paco_EQ_" in
let x16 := fresh "_paco_v_" in let EQ16 := fresh "_paco_EQ_" in
let x17 := fresh "_paco_v_" in let EQ17 := fresh "_paco_EQ_" in
let x18 := fresh "_paco_v_" in let EQ18 := fresh "_paco_EQ_" in
let x19 := fresh "_paco_v_" in let EQ19 := fresh "_paco_EQ_" in
let x20 := fresh "_paco_v_" in let EQ20 := fresh "_paco_EQ_" in
let x21 := fresh "_paco_v_" in let EQ21 := fresh "_paco_EQ_" in
let x22 := fresh "_paco_v_" in let EQ22 := fresh "_paco_EQ_" in
let x23 := fresh "_paco_v_" in let EQ23 := fresh "_paco_EQ_" in
let x24 := fresh "_paco_v_" in let EQ24 := fresh "_paco_EQ_" in
let x25 := fresh "_paco_v_" in let EQ25 := fresh "_paco_EQ_" in
let x26 := fresh "_paco_v_" in let EQ26 := fresh "_paco_EQ_" in
let x27 := fresh "_paco_v_" in let EQ27 := fresh "_paco_EQ_" in
paco_convert e27 x27 EQ27;
paco_convert e26 x26 EQ26;
paco_convert e25 x25 EQ25;
paco_convert e24 x24 EQ24;
paco_convert e23 x23 EQ23;
paco_convert e22 x22 EQ22;
paco_convert e21 x21 EQ21;
paco_convert e20 x20 EQ20;
paco_convert e19 x19 EQ19;
paco_convert e18 x18 EQ18;
paco_convert e17 x17 EQ17;
paco_convert e16 x16 EQ16;
paco_convert e15 x15 EQ15;
paco_convert e14 x14 EQ14;
paco_convert e13 x13 EQ13;
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
intros x14 EQ14;
intros x15 EQ15;
intros x16 EQ16;
intros x17 EQ17;
intros x18 EQ18;
intros x19 EQ19;
intros x20 EQ20;
intros x21 EQ21;
intros x22 EQ22;
intros x23 EQ23;
intros x24 EQ24;
intros x25 EQ25;
intros x26 EQ26;
intros x27 EQ27;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 (conj EQ12 (conj EQ13 (conj EQ14 (conj EQ15 (conj EQ16 (conj EQ17 (conj EQ18 (conj EQ19 (conj EQ20 (conj EQ21 (conj EQ22 (conj EQ23 (conj EQ24 (conj EQ25 (conj EQ26 EQ27))))))))))))))))))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12 EQ13 EQ14 EQ15 EQ16 EQ17 EQ18 EQ19 EQ20 EQ21 EQ22 EQ23 EQ24 EQ25 EQ26 EQ27;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top; move x13 at top; move x14 at top; move x15 at top; move x16 at top; move x17 at top; move x18 at top; move x19 at top; move x20 at top; move x21 at top; move x22 at top; move x23 at top; move x24 at top; move x25 at top; move x26 at top; move x27 at top; 
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27.

Lemma _paco_pre28: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 (gf: rel28 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27.
Proof. intros; apply X. Defined.

Ltac paco_pre28 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre28; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 ?e15 ?e16 ?e17 ?e18 ?e19 ?e20 ?e21 ?e22 ?e23 ?e24 ?e25 ?e26 ?e27 => unfold X; clear X; paco_cont28 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27
end.

Ltac paco_post_match28 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post28" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match28 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 29
*)

Ltac paco_cont29 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 := 
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
let x14 := fresh "_paco_v_" in let EQ14 := fresh "_paco_EQ_" in
let x15 := fresh "_paco_v_" in let EQ15 := fresh "_paco_EQ_" in
let x16 := fresh "_paco_v_" in let EQ16 := fresh "_paco_EQ_" in
let x17 := fresh "_paco_v_" in let EQ17 := fresh "_paco_EQ_" in
let x18 := fresh "_paco_v_" in let EQ18 := fresh "_paco_EQ_" in
let x19 := fresh "_paco_v_" in let EQ19 := fresh "_paco_EQ_" in
let x20 := fresh "_paco_v_" in let EQ20 := fresh "_paco_EQ_" in
let x21 := fresh "_paco_v_" in let EQ21 := fresh "_paco_EQ_" in
let x22 := fresh "_paco_v_" in let EQ22 := fresh "_paco_EQ_" in
let x23 := fresh "_paco_v_" in let EQ23 := fresh "_paco_EQ_" in
let x24 := fresh "_paco_v_" in let EQ24 := fresh "_paco_EQ_" in
let x25 := fresh "_paco_v_" in let EQ25 := fresh "_paco_EQ_" in
let x26 := fresh "_paco_v_" in let EQ26 := fresh "_paco_EQ_" in
let x27 := fresh "_paco_v_" in let EQ27 := fresh "_paco_EQ_" in
let x28 := fresh "_paco_v_" in let EQ28 := fresh "_paco_EQ_" in
paco_convert e28 x28 EQ28;
paco_convert e27 x27 EQ27;
paco_convert e26 x26 EQ26;
paco_convert e25 x25 EQ25;
paco_convert e24 x24 EQ24;
paco_convert e23 x23 EQ23;
paco_convert e22 x22 EQ22;
paco_convert e21 x21 EQ21;
paco_convert e20 x20 EQ20;
paco_convert e19 x19 EQ19;
paco_convert e18 x18 EQ18;
paco_convert e17 x17 EQ17;
paco_convert e16 x16 EQ16;
paco_convert e15 x15 EQ15;
paco_convert e14 x14 EQ14;
paco_convert e13 x13 EQ13;
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
intros x14 EQ14;
intros x15 EQ15;
intros x16 EQ16;
intros x17 EQ17;
intros x18 EQ18;
intros x19 EQ19;
intros x20 EQ20;
intros x21 EQ21;
intros x22 EQ22;
intros x23 EQ23;
intros x24 EQ24;
intros x25 EQ25;
intros x26 EQ26;
intros x27 EQ27;
intros x28 EQ28;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 (conj EQ12 (conj EQ13 (conj EQ14 (conj EQ15 (conj EQ16 (conj EQ17 (conj EQ18 (conj EQ19 (conj EQ20 (conj EQ21 (conj EQ22 (conj EQ23 (conj EQ24 (conj EQ25 (conj EQ26 (conj EQ27 EQ28)))))))))))))))))))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12 EQ13 EQ14 EQ15 EQ16 EQ17 EQ18 EQ19 EQ20 EQ21 EQ22 EQ23 EQ24 EQ25 EQ26 EQ27 EQ28;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top; move x13 at top; move x14 at top; move x15 at top; move x16 at top; move x17 at top; move x18 at top; move x19 at top; move x20 at top; move x21 at top; move x22 at top; move x23 at top; move x24 at top; move x25 at top; move x26 at top; move x27 at top; move x28 at top; 
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28.

Lemma _paco_pre29: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 (gf: rel29 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28.
Proof. intros; apply X. Defined.

Ltac paco_pre29 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre29; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 ?e15 ?e16 ?e17 ?e18 ?e19 ?e20 ?e21 ?e22 ?e23 ?e24 ?e25 ?e26 ?e27 ?e28 => unfold X; clear X; paco_cont29 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28
end.

Ltac paco_post_match29 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post29" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match29 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** *** Arity 30
*)

Ltac paco_cont30 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 := 
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
let x14 := fresh "_paco_v_" in let EQ14 := fresh "_paco_EQ_" in
let x15 := fresh "_paco_v_" in let EQ15 := fresh "_paco_EQ_" in
let x16 := fresh "_paco_v_" in let EQ16 := fresh "_paco_EQ_" in
let x17 := fresh "_paco_v_" in let EQ17 := fresh "_paco_EQ_" in
let x18 := fresh "_paco_v_" in let EQ18 := fresh "_paco_EQ_" in
let x19 := fresh "_paco_v_" in let EQ19 := fresh "_paco_EQ_" in
let x20 := fresh "_paco_v_" in let EQ20 := fresh "_paco_EQ_" in
let x21 := fresh "_paco_v_" in let EQ21 := fresh "_paco_EQ_" in
let x22 := fresh "_paco_v_" in let EQ22 := fresh "_paco_EQ_" in
let x23 := fresh "_paco_v_" in let EQ23 := fresh "_paco_EQ_" in
let x24 := fresh "_paco_v_" in let EQ24 := fresh "_paco_EQ_" in
let x25 := fresh "_paco_v_" in let EQ25 := fresh "_paco_EQ_" in
let x26 := fresh "_paco_v_" in let EQ26 := fresh "_paco_EQ_" in
let x27 := fresh "_paco_v_" in let EQ27 := fresh "_paco_EQ_" in
let x28 := fresh "_paco_v_" in let EQ28 := fresh "_paco_EQ_" in
let x29 := fresh "_paco_v_" in let EQ29 := fresh "_paco_EQ_" in
paco_convert e29 x29 EQ29;
paco_convert e28 x28 EQ28;
paco_convert e27 x27 EQ27;
paco_convert e26 x26 EQ26;
paco_convert e25 x25 EQ25;
paco_convert e24 x24 EQ24;
paco_convert e23 x23 EQ23;
paco_convert e22 x22 EQ22;
paco_convert e21 x21 EQ21;
paco_convert e20 x20 EQ20;
paco_convert e19 x19 EQ19;
paco_convert e18 x18 EQ18;
paco_convert e17 x17 EQ17;
paco_convert e16 x16 EQ16;
paco_convert e15 x15 EQ15;
paco_convert e14 x14 EQ14;
paco_convert e13 x13 EQ13;
paco_convert e12 x12 EQ12;
paco_convert e11 x11 EQ11;
paco_convert e10 x10 EQ10;
paco_convert e9 x9 EQ9;
paco_convert e8 x8 EQ8;
paco_convert e7 x7 EQ7;
paco_convert e6 x6 EQ6;
paco_convert e5 x5 EQ5;
paco_convert e4 x4 EQ4;
paco_convert e3 x3 EQ3;
paco_convert e2 x2 EQ2;
paco_convert e1 x1 EQ1;
paco_convert e0 x0 EQ0;
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
intros x14 EQ14;
intros x15 EQ15;
intros x16 EQ16;
intros x17 EQ17;
intros x18 EQ18;
intros x19 EQ19;
intros x20 EQ20;
intros x21 EQ21;
intros x22 EQ22;
intros x23 EQ23;
intros x24 EQ24;
intros x25 EQ25;
intros x26 EQ26;
intros x27 EQ27;
intros x28 EQ28;
intros x29 EQ29;
generalize (conj EQ0 (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 (conj EQ8 (conj EQ9 (conj EQ10 (conj EQ11 (conj EQ12 (conj EQ13 (conj EQ14 (conj EQ15 (conj EQ16 (conj EQ17 (conj EQ18 (conj EQ19 (conj EQ20 (conj EQ21 (conj EQ22 (conj EQ23 (conj EQ24 (conj EQ25 (conj EQ26 (conj EQ27 (conj EQ28 EQ29))))))))))))))))))))))))))))); clear EQ0 EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8 EQ9 EQ10 EQ11 EQ12 EQ13 EQ14 EQ15 EQ16 EQ17 EQ18 EQ19 EQ20 EQ21 EQ22 EQ23 EQ24 EQ25 EQ26 EQ27 EQ28 EQ29;
move x0 at top; move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top; move x9 at top; move x10 at top; move x11 at top; move x12 at top; move x13 at top; move x14 at top; move x15 at top; move x16 at top; move x17 at top; move x18 at top; move x19 at top; move x20 at top; move x21 at top; move x22 at top; move x23 at top; move x24 at top; move x25 at top; move x26 at top; move x27 at top; move x28 at top; move x29 at top; 
paco_generalize_hyp _paco_mark; revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29.

Lemma _paco_pre30: forall T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 (gf: rel30 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
(X: let gf' := gf in gf' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29), gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29.
Proof. intros; apply X. Defined.

Ltac paco_pre30 := let X := fresh "_paco_X_" in
generalize _paco_mark_cons; repeat intro;
apply _paco_pre30; intro X;
match goal with
| |- _ ?e0 ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 ?e9 ?e10 ?e11 ?e12 ?e13 ?e14 ?e15 ?e16 ?e17 ?e18 ?e19 ?e20 ?e21 ?e22 ?e23 ?e24 ?e25 ?e26 ?e27 ?e28 ?e29 => unfold X; clear X; paco_cont30 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29
end.

Ltac paco_post_match30 INC tac1 tac2 :=
let cr := fresh "_paco_cr_" in intros cr INC; repeat (red in INC);
match goal with [H: ?x |- _] => match x with
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, (pacoid _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
| forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => paco_post_var INC pr cr; tac2 pr cr
| _ => tac1 cr
end end.

Tactic Notation "paco_post30" ident(CIH) "with" ident(nr) :=
let INC := fresh "_paco_inc_" in
paco_post_match30 INC ltac:(paco_ren_r nr) paco_ren_pr; paco_post_simp CIH;
let CIH' := fresh CIH in try rename INC into CIH'.

(** ** External interface *)

(** We provide our main tactics:

    - [pcofix{n} ident using lemma with ident']


    where [ident] is the identifier used to name the generated coinduction hypothesis,
    [lemma] is an expression denoting which accumulation lemma is to be used, and
    [ident'] is the identifier used to name the accumulation variable.
*)

Tactic Notation "pcofix0" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre0; eapply lem; paco_post0 CIH with r.

Tactic Notation "pcofix1" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre1; eapply lem; paco_post1 CIH with r.

Tactic Notation "pcofix2" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre2; eapply lem; paco_post2 CIH with r.

Tactic Notation "pcofix3" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre3; eapply lem; paco_post3 CIH with r.

Tactic Notation "pcofix4" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre4; eapply lem; paco_post4 CIH with r.

Tactic Notation "pcofix5" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre5; eapply lem; paco_post5 CIH with r.

Tactic Notation "pcofix6" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre6; eapply lem; paco_post6 CIH with r.

Tactic Notation "pcofix7" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre7; eapply lem; paco_post7 CIH with r.

Tactic Notation "pcofix8" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre8; eapply lem; paco_post8 CIH with r.

Tactic Notation "pcofix9" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre9; eapply lem; paco_post9 CIH with r.

Tactic Notation "pcofix10" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre10; eapply lem; paco_post10 CIH with r.

Tactic Notation "pcofix11" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre11; eapply lem; paco_post11 CIH with r.

Tactic Notation "pcofix12" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre12; eapply lem; paco_post12 CIH with r.

Tactic Notation "pcofix13" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre13; eapply lem; paco_post13 CIH with r.

Tactic Notation "pcofix14" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre14; eapply lem; paco_post14 CIH with r.

Tactic Notation "pcofix15" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre15; eapply lem; paco_post15 CIH with r.

Tactic Notation "pcofix16" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre16; eapply lem; paco_post16 CIH with r.

Tactic Notation "pcofix17" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre17; eapply lem; paco_post17 CIH with r.

Tactic Notation "pcofix18" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre18; eapply lem; paco_post18 CIH with r.

Tactic Notation "pcofix19" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre19; eapply lem; paco_post19 CIH with r.

Tactic Notation "pcofix20" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre20; eapply lem; paco_post20 CIH with r.

Tactic Notation "pcofix21" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre21; eapply lem; paco_post21 CIH with r.

Tactic Notation "pcofix22" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre22; eapply lem; paco_post22 CIH with r.

Tactic Notation "pcofix23" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre23; eapply lem; paco_post23 CIH with r.

Tactic Notation "pcofix24" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre24; eapply lem; paco_post24 CIH with r.

Tactic Notation "pcofix25" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre25; eapply lem; paco_post25 CIH with r.

Tactic Notation "pcofix26" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre26; eapply lem; paco_post26 CIH with r.

Tactic Notation "pcofix27" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre27; eapply lem; paco_post27 CIH with r.

Tactic Notation "pcofix28" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre28; eapply lem; paco_post28 CIH with r.

Tactic Notation "pcofix29" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre29; eapply lem; paco_post29 CIH with r.

Tactic Notation "pcofix30" ident(CIH) "using" constr(lem) "with" ident(r) :=
paco_pre30; eapply lem; paco_post30 CIH with r.

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
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 30)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 29)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 28)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 27)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 26)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 25)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 24)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 23)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 22)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 21)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 20)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 19)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 18)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 17)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 16)
     | [|- _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 15)
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
  | [|- let _ := 15 in _] => intros _; pcofix15 CIH using lem with nr
  | [|- let _ := 16 in _] => intros _; pcofix16 CIH using lem with nr
  | [|- let _ := 17 in _] => intros _; pcofix17 CIH using lem with nr
  | [|- let _ := 18 in _] => intros _; pcofix18 CIH using lem with nr
  | [|- let _ := 19 in _] => intros _; pcofix19 CIH using lem with nr
  | [|- let _ := 20 in _] => intros _; pcofix20 CIH using lem with nr
  | [|- let _ := 21 in _] => intros _; pcofix21 CIH using lem with nr
  | [|- let _ := 22 in _] => intros _; pcofix22 CIH using lem with nr
  | [|- let _ := 23 in _] => intros _; pcofix23 CIH using lem with nr
  | [|- let _ := 24 in _] => intros _; pcofix24 CIH using lem with nr
  | [|- let _ := 25 in _] => intros _; pcofix25 CIH using lem with nr
  | [|- let _ := 26 in _] => intros _; pcofix26 CIH using lem with nr
  | [|- let _ := 27 in _] => intros _; pcofix27 CIH using lem with nr
  | [|- let _ := 28 in _] => intros _; pcofix28 CIH using lem with nr
  | [|- let _ := 29 in _] => intros _; pcofix29 CIH using lem with nr
  | [|- let _ := 30 in _] => intros _; pcofix30 CIH using lem with nr
  end.

Tactic Notation "pcofix" ident(CIH) "using" constr(lem) :=
  pcofix CIH using lem with r.

