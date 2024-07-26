(** * Performance Criterion: fast alpha-equivalence check (Õ(term size)) *)
From Coq Require Import ZArith.

Fixpoint biga (n : nat) (f : Prop -> Prop)
:= match n with
   | 0 => f True
   | S n => biga n (fun x => forall a : Prop, f (a -> x))
   end.
Fixpoint bigb (n : nat) (f : Prop -> Prop)
:= match n with
   | 0 => f True
   | S n => bigb n (fun x => forall b : Prop, f (b -> x))
   end.

Definition goal n := biga n (fun x => x) = bigb n (fun x => x).

Ltac check n :=
  let ty := (eval cbv in (goal (Z.to_nat n))) in
  let lhs := lazymatch ty with ?x = _ => x end in
  time let v := constr:(@eq_refl Prop lhs : ty) in idtac.

(* overhead to build the term is pretty big, though... *)
Goal True.
  check 7000%Z. (* Tactic call ran for 0.006 secs (0.006u,0.s) (success) *)
  Optimize Heap.
  check 8000%Z. (* Tactic call ran for 0.007 secs (0.007u,0.s) (success) *)
  Optimize Heap.
  check 9000%Z. (* Tactic call ran for 0.008 secs (0.008u,0.s) (success) *)
Abort.
