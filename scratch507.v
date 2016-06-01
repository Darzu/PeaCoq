Require Import Omega.

Ltac name A B :=
  let Heq := fresh "H" in
  remember A as B eqn:Heq; clear Heq.

Ltac copy H :=
  let x := fresh "H" in
  name H x.

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
  copy H.  
  apply my_lem1 in H0.
  subst.
  apply my_lem2 in H.
  assumption.
  inversion H.
  congruence.
Qed.

(*END DEMO*)





Lemma foobar2:
  forall a b c d,
    my_rel a b c ->
    a < (if c then b else d).
Proof.
  intros.
  rename_all my_rel MyRel.  
  P copy my_rel.  
  NP1 _applyin my_lem1 my_rel.
  subst.
  NP _applyin my_lem2 my_rel.
  assumption.
Qed.

Lemma foobar3:
  forall a b c d,
    my_rel a b c ->
    a < (if c then b else d).
Proof.
  intros.
  P copy my_rel.
  copy my_lem1.
  (* PN1 _applyin my_rel H. *)
  apply* [[true]] in H.
  (* apply* my_lem1 in H. *)
  apply* my_lem1 in [[my_rel]].
  NP1 _applyin my_lem1 my_rel.
  subst.
  NP _applyin my_lem2 my_rel.
  assumption.
Qed.








Lemma foo:
  forall x y z,
    x = 9000 ->
    y = 2000 ->
    z = x + y ->
    z = 9000 + 2000.
Proof.
  intros.
  omega.
Qed.  

Fixpoint fact (n : nat) : nat :=
  match n with
    | 0 => 1
    | S n' => fact n' * S n'
  end.

Eval cbv in (fact 10).

Inductive fact_state : Set :=
| AnswerIs : nat -> fact_state
| WithAccumulator : nat -> nat -> fact_state
.

Inductive fact_init (original_input : nat) : fact_state -> Prop

Inductive natural : Set :=
| Zero : natural
| Succ : natural -> natural.

Fixpoint add (n m : natural) : natural :=
  match n with
    | Zero => m
    | Succ n' => Succ (add n' m)
  end.

(* Induction: forall n : nat. P(n); need
derive inductive def n
 *)

Theorem add_assoc : forall n m o, add (add n m) o = add n (add m o).
Proof.
  induction n.

  intros.
  simpl.
  reflexivity.

  intros.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma triv : forall x y,
               x + y -> y + x.
Admitted.

Lemma triv2 : forall x y, (x + y), y+x.

Lemma add_Zero : forall n,
                   add n Zero = n.
Proof.
  induction n; simpl.

  reflexivity.

  rewrite IHn.
  reflexivity.
Qed.

Lemma add_Succ : forall n m,
                   add n (Succ m) = Succ (add n m).
Proof.
  induction n; simpl; intros.

  reflexivity.

  rewrite IHn.
  reflexivity.
Qed.

Theorem add_comm : forall n m, add n m = add m n.
Proof.
  induction n; intros; simpl.

  rewrite add_Zero.
  reflexivity.

  rewrite IHn.
  rewrite add_Succ.
  reflexivity.
Qed.

Inductive exp : Set :=
| Constant : nat -> exp
| Plus : exp -> exp -> exp
| Times : exp -> exp -> exp.

Fixpoint eval (e : exp) : nat :=
  match e with
    | Constant n => n
    | Plus e1 e2 => eval e1 + eval e2
    | Times e1 e2 => eval e1 * eval e2
  end.

Fixpoint commuter (e : exp) : exp :=
  match e with
    | Constant _ => e
    | Plus e1 e2 => Plus (commuter e2) (commuter e1)
    | Times e1 e2 => Times (commuter e2) (commuter e1)
  end.

Theorem eval_commuter : forall e, eval (commuter e) = eval e.
Proof.
  induction e; simpl;
  repeat match goal with
           | [ H : _ = _ |- _ ] => rewrite H
         end; ring.
Qed.

(*   reflexivity. *)

(*   rewrite IHe1. *)
(*   rewrite IHe2. *)
(*   ring. *)

(*   rewrite IHe1. *)
(*   rewrite IHe2. *)
(*   ring. *)
(* Qed. *)

Inductive term : Set :=
| Var : string -> term
| Abs : string -> term -> term
| App : term -> term -> term.

Fixpoint subst (rep : term) (x : string) (e : term) : term :=
  match e with
    | Var y => if string_dec y x then rep else Var y
    | Abs y e1 => (if string_dec y x then e1 else subst rep x e1)
    | App e1 e2 => App (subst rep x e1) (subst rep x e2)
  end.

Fixpoint notFreeIn (x : string) (e : term) : Prop :=
  match e with
    | Var y => y <> x
                      

                      

(*TODO: 
  http://coq-blog.clarus.me/tutorial-a-hello-world-in-coq.html
  https://github.com/clarus/coq-hello-world
*)

Lemma dist:
  forall A B C,
    (A \/ B) /\ (A \/ C) ->
     A \/ (B /\ C).
Proof.
  intros.
  inversion H.
  inversion H0.
  {
    left. assumption.
  }
  {
    inversion H1.
    {
      left. assumption.
    }
    {
      right. auto.
    }
  }
Qed.  
