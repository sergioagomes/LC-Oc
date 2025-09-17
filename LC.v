Require Import Nat.

(*Lambda Calculus*)
Inductive term : Type :=
  | Var : nat -> term
  | Abs : term -> term
  | App : term -> term -> term.

Definition id_term : term :=  Abs(Var 0).

Lemma id_term_is_term : exists t : term, True.
Proof.
  exists id_term.
  (* Proves the goal by reflexivity *)
  reflexivity. 
Qed.