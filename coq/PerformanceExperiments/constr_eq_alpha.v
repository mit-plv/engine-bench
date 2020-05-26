Require Import PerformanceExperiments.Harness.

Fixpoint biga (n : nat) (P : Prop)
:= match n with
   | 0 => P
   | S n => forall a : Prop, biga n (a -> P)
   end.
Fixpoint bigb (n : nat) (P : Prop)
:= match n with
   | 0 => P
   | S n => forall b : Prop, bigb n (b -> P)
   end.

Definition goal n := biga n True = bigb n True.

Ltac check n :=
  let ty := (eval cbv in (goal (Z.to_nat n))) in
  let lhs := lazymatch ty with ?x = _ => x end in
  optimize_heap;
  time "constr-eq_refl" let v := constr:(@eq_refl Prop lhs : ty) in idtac.

Ltac mkgoal n := constr:(True).
Ltac redgoal _ := idtac.
Ltac time_solve_goal0 n := check n.

Global Open Scope Z_scope.

Definition args_of_size (s : size) : list Z
  := match s with
     | Sanity => List.map Z.of_nat (seq 0 3)
     | SuperFast => List.map (fun x => Z.of_nat x * 1000) (seq 1 10)
     | Fast => []
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.
(*
Goal True. run0 SuperFast.
*)
