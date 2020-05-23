(** * Performance Criterion: fast alpha-equivalence check (Õ(term size)) *)
Require Import Coq.ZArith.ZArith.

Fixpoint biga (n : nat) (P : Prop)
:= match n with
   | 0 => P
   | S n => forall a : Prop, biga n (a -> P)
   end.
Fixpoint bigb (n : nat) (P : Prop)
:= match n with
   | 0 => P
   | S n => forall b : Prop, biga n (b -> P)
   end.

Definition goal n := biga n True = bigb n True.

Ltac check n :=
  let ty := (eval cbv in (goal (Z.to_nat n))) in
  let lhs := lazymatch ty with ?x = _ => x end in
  time let v := constr:(@eq_refl Prop lhs : ty) in idtac.

(* overhead to build the term is pretty big, though... *)
Goal True.
  check 7000%Z. (* Tactic call ran for 0.006 secs (0.006u,0.s) (success) *)
  check 8000%Z. (* Tactic call ran for 0.007 secs (0.007u,0.s) (success) *)
  check 9000%Z. (* Tactic call ran for 0.008 secs (0.008u,0.s) (success) *)
Abort.
