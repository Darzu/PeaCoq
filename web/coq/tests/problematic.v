(* Episode 02: Hello PeaCoq *)

(* bind a name to an expression *)
Definition x := 0.

(* show the expression a name is bound to *)
Print x.

(* show the type of the expression x is bound to *)
Check x.

(* show the result of evaluating an expression *)
Eval cbv in (1 + 1).

(* what the heck is "binding" anyway? [slides] *)

(* FUNCTIONS *)

Definition id x := x.

(* TYPES *)

(* Coq doesn't have any built in types! *)
(* however, the standard prelude provides familiar types *)

Print bool.

(* we can define bool ourselves *)
Inductive boolean : Type :=
| true
| false.

Inductive positive_numbers_under_ten : Type :=
| one
| two
| three
| four
| five
| six
| seven
| eight
| nine.

Definition pnut : Type :=
  positive_numbers_under_ten.

(* Functions *)

Definition boolean_negation : boolean -> boolean :=
  fun (b: boolean) =>
    match b with
      | true => false
      | false => true
    end.

Definition boolean_negation' (b: boolean) : boolean :=
  match b with
    | true => false
    | false => true
  end.

Definition pnut_scramble (n : pnut) : pnut :=
  match n with
    | one => three
    | two => one
    | three => two
    | four => five
    | five => four
    | six => nine
    | seven => seven
    | eight => eight
    | nine => six
  end.

(* What about successor? It's a partial function... *)

Definition identity (T: Type) (v: T) : T :=
  v.

(* Parameterized Types *)

Inductive option (T: Type) : Type :=
| Some : T -> option T
| None : option T.

(* More Functions *)

Definition pnut_successor (n : pnut) : option pnut :=
  match n with
    | one => Some pnut two
    | two => Some pnut three
    | three => Some pnut four
    | four => Some pnut five
    | five => Some pnut six
    | six => Some pnut seven
    | seven => Some pnut eight
    | eight => Some pnut nine
    | nine => None pnut
  end.

Fixpoint factorial n :=
  match n with
  | O => 1
  | S m => n * factorial m
  end.

Definition monotonic f :=
  forall a b,
  a <= b ->
  f a <= f b.





