Require Import Omega.

Ltac name A B :=
  let Heq := fresh "H" in
  remember A as B eqn:Heq; clear Heq.
Ltac copy H :=
  let x := fresh "H" in
  name H x.
Ltac apply_new Hlem H :=
  let HNEW := fresh "H" in
  name H HNEW; apply Hlem in HNEW.
Ltac eapply_new Hlem H :=
  let HNEW := fresh "H" in
  name H HNEW; eapply Hlem in HNEW.
Ltac inv H := inversion H; clear H; subst.

Ltac clear_dup :=
  match goal with
    |[H1 : ?A, H2: ?A |- _] => clear H2
  end.

(* break/destruct helpers *)
Ltac break_if_hyp :=
  match goal with
    | [ H : context [ if ?X then _ else _ ] |- _] => destruct X eqn:?
  end.
Ltac break_if_goal :=
  match goal with
    | [ |- context [ if ?X then _ else _ ] ] => destruct X eqn:?
  end.
Ltac break_if := break_if_hyp || break_if_goal.
Ltac break_match_hyp :=
  match goal with
    | [ H : context [ match ?X with _ => _ end ] |- _] => destruct X eqn:?
  end.
Ltac break_match_goal :=
  match goal with
    | [ |- context [ match ?X with _ => _ end ] ] => destruct X eqn:?
  end.
Ltac break_match := break_match_goal || break_match_hyp.
Ltac break_exists :=
  match goal with
    | [H : exists _, _ |- _ ] => destruct H
  end.
Ltac break_and :=
  match goal with
   | [H : _ /\ _ |- _ ] => destruct H
  end.
Ltac break_let_hyp :=
  match goal with
    | [ H : context [ (let (_,_) := ?X in _) ] |- _ ] => destruct X eqn:?
  end.
Ltac break_let_goal :=
  match goal with
    | [ |- context [ (let (_,_) := ?X in _) ] ] => destruct X eqn:?
  end.
Ltac break_let := break_let_hyp || break_let_goal.
Ltac break_or :=
  match goal with
    | [ H : _ \/ _ |- _ ] => inv H
  end.

(**)
Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof. auto. Qed.
Ltac exploit x :=
    refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _) _)
 || refine (modusponens _ _ (x _ _) _)
 || refine (modusponens _ _ (x _) _).


(* ---------------------------------------- *)
(* START DEMO *)
(* ---------------------------------------- *)

Inductive my_rel a b c : Prop :=
| mk_my_rel:
    S (S a) = S b ->
    c = true ->
    my_rel a b c.

Lemma my_lem1:
  forall a b c,
    my_rel a b c ->
    c = true.
Proof.
  intros.
  inversion H.
  assumption.
Qed.

Lemma my_lem2:
  forall a b c,
    my_rel a b c ->
    a < b.
Proof.
  intros.  
  inversion H.
  omega.
Qed.


Lemma foobar:
  forall a b c d,
    my_rel a b c ->
    a < (if c then b else d) /\ c <> false.
Proof.
  intros.
  split.
  inversion H. break_if; try discriminate. omega.
  inversion H.  
  rewrite H1.  
  omega.
  exploit my_lem1; eauto; intro.
  congruence.
Qed.


(* ---------------------------------------- *)
(* END DEMO *)
(* ---------------------------------------- *)
































(*EOF*)


