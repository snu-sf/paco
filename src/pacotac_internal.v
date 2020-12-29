From Paco Require Export paconotation.


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

(** ** Internal Helper Tactics
*)

Inductive _paco_mark := _paco_mark_cons.

Ltac paco_revert :=
  match goal with [H: _ |- _] => revert H end.

Ltac paco_revert_hyp mark :=
  match goal with [x: ?A |- _] =>
  match A with
    | mark => clear x
    | _ => revert x; paco_revert_hyp mark
  end end.

(** * Cofixpoint Tactic

    Mostly written by Li-yao Xia

[pcofix self]: Apply coinduction to a goal with [paco] at the head of the conclusion
(possibly after unfolding definitions).
The parameter [self] is the name of the coinduction hypothesis.

Internal definition of [pcofix_]:

Example initial goal:
<<
===========
forall (x : X) (y : Y), hyp x y -> paco2 gf bot2 (f0 x y) (f1 x y)
>>

   1. [pcofix_] first recursively introduces all hypotheses [H], being careful to
      preserve existing names, and at the same time builds up continuations
      to process the goal once we reach the conclusion. This technique has the
      benefit that the name of each hypothesis is available, so it does
      not need to be guessed repeatedly.

Goal after step 1:
<<
x : X
y : Y
H : hyp x y
===========
paco2 gf bot2 (f0 x y) (f1 x y)
>>

   2. Having reached the conclusion, we use the [pack_goal0] continuation to
      regeneralize the hypotheses we introduced into a single sigma type
      (a chain of [{_ & _}]/[sigT]),

Goal after step 2:
<<
===========
forall (u : {x : X & {y : Y & {_ : hyp x y & unit}}}),
  paco2 gf bot2 (f0 (projT1 u) (projT2 u)) (f1 (projT1 u) (projT2 u))
>>

   3. We can now apply [paco2_accF] (depending on the arity of paco)

Goal after step 3:
<<
r : rel2 T0 T1
_pacotmp_SELF: forall (u : _), r (f0 (projT1 u) (projT2 u)) (f1 (projT1 u) (projT2 u))
==========
forall (u : {x : X & {y : Y & {_ : hyp x y & unit}}}),
  paco2 gf r (f0 (projT1 u) (projT2 u)) (f1 (projT1 u) (projT2 u))
>>

   4. We decompose the tuple in the goal using the [unpack_goal0] continuation
      (basically the reverse of [pack_goal0]) and [revert_tmp0].

Goal after step 4:
<<
r : rel2 T0 T1
_pacotmp_SELF: forall (u : _), r (f0 (projT1 u) (projT2 u)) (f1 (projT1 u) (projT2 u))
==========
forall x y, hyp x y -> paco2 gf r (f0 x y) (f1 x y)
>>

   5. We decompose the tuple in the coinduction hypothesis

Goal after step 5:
<<
r : rel2 T0 T1
SELF: forall x y, hyp x y -> r (f0 x y) (f1 x y)
==========
forall x y, hyp x y -> paco2 gf r (f0 x y) (f1 x y)
>>

tODO: Currently this step does not preserve variable names,
so the actual hypothesis looks more like this:

<<
SELF: forall x0 x1, hyp x0 x1 -> r (f0 x0 x1) (f1 x0 x1)
>>
*)

Lemma paco_curry_sig {A : Type} {P : A -> Type} {Q : forall (a : A) (b : P a), Prop}
  : (forall x : sigT P, Q (projT1 x) (projT2 x)) -> forall (a : A) (p : P a), Q a p.
Proof.
  exact (fun H a p => H (existT _ a p)).
Qed.

Ltac paco_get_r INC r :=
  let tmp_type := type of INC in
  lazymatch tmp_type with

  | bot0 -> r => clear INC
  | ?pr -> r => pr
  | forall _, bot1 _ -> r _ => clear INC
  | forall _, ?pr _ -> r _ => pr
  | forall _ _, bot2 _ _ -> r _ _ => clear INC
  | forall _ _, ?pr _ _ -> r _ _ => pr
  | forall _ _ _, bot3 _ _ _ -> r _ _ _ => clear INC
  | forall _ _ _, ?pr _ _ _ -> r _ _ _ => pr
  | forall _ _ _ _, bot4 _ _ _ _ -> r _ _ _ _ => clear INC
  | forall _ _ _ _, ?pr _ _ _ _ -> r _ _ _ _ => pr

  | _ => idtac
  end.

Ltac paco_inc self INC r0 r :=
  let TMP := fresh "_pacotmp_" in
  repeat (
    match reverse goal with [H: context f [r0] |-_] =>
      let cih := context f [r] in rename H into TMP;
      assert(H : cih) by (repeat intro; eapply INC, TMP; eassumption); clear TMP
    end);
  first [clear INC r0; try rename r into r0|
         try (let self := fresh self in rename INC into self)].

Ltac pcofix_ self rv lem pack_goal unpack_goal revert_tmp prove_self :=
  hnf;
  lazymatch goal with
  | [ |- forall x : ?X, ?P ] =>
    (* 1. build_tactics *)
    let x := fresh x in intros x;
    let pack_goal' := (revert x; apply paco_curry_sig; pack_goal) in
    let unpack_goal' H := (unpack_goal H; destruct H as [x H]; cbn [projT1 projT2]) in
    let revert_tmp' := (revert x; revert_tmp) in
    let prove_self' tmp_self tm := (prove_self tmp_self (existT (fun x => _) x tm)) in
    pcofix_ self rv lem pack_goal' unpack_goal' revert_tmp' prove_self'
  | _ =>
    let tmp_self := fresh "_pacotmp_self_" in
    let tmp_hyp := fresh "_pacotmp_hyp_" in
    let tmp_type := fresh "_pacotmp_type_" in
    (* 2. pack_goal *)
    pose proof (tmp_hyp := tt); revert tmp_hyp; pack_goal;
    (* 3. paco_acc *)
    eapply lem; [..|
    let r := fresh rv in let INC := fresh "_pacotmp_inc_" in intros r INC tmp_self;
    let r0 := paco_get_r INC r in paco_inc self INC r0 r; 
    (* 4. unpack_goal *)
    intros tmp_hyp; unpack_goal tmp_hyp; clear tmp_hyp; revert_tmp;
    (* 5. unpack_hyp *)
    let self := fresh self in
    evar (tmp_type : Prop);
    let type_of_tmp_self := type of tmp_self in
    assert(tmp_hyp: tmp_type -> type_of_tmp_self);
    [ intros self tmp_hyp; unpack_goal tmp_hyp; revert_tmp; exact self |
      clear tmp_hyp; assert (self: tmp_type); subst tmp_type;
      [ intros; prove_self tmp_self tt | clear tmp_self]]]
  end.

Tactic Notation "pcofix" ident(self) "using" constr(lem) "with" ident(rv) :=
  let pack_goal := idtac in
  let unpack_goal _ := idtac in
  let revert_tmp := idtac in
  let prove_self tmp_self tm := exact (tmp_self tm) in
  pcofix_ self rv lem pack_goal unpack_goal revert_tmp prove_self.

Tactic Notation "pcofix" ident(CIH) "using" constr(lem) :=
  pcofix CIH using lem with r.

