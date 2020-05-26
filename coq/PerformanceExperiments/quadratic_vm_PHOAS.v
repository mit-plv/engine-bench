Require Import PerformanceExperiments.Harness.
Require PerformanceExperiments.quadratic_cbv_lazy_PHOAS.
(** https://github.com/coq/coq/issues/11151 *)

Local Infix "/" := Nat.div : nat_scope.

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 0 3
     | SuperFast => List.map (fun x => x * 5) (seq 0 (120 / 5))
     | Fast => List.map (fun x => x * 5) (seq 0 (150 / 5))
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac mkgoal n := quadratic_cbv_lazy_PHOAS.mkgoal n.
Ltac describe_goal n := quadratic_cbv_lazy_PHOAS.describe_goal n.
Ltac redgoal _ := vm_compute.
Ltac time_solve_goal0 n :=
  let term := quadratic_cbv_lazy_PHOAS.get_term () in
  try (once (time "vm_compute" (idtac; let res := (eval vm_compute in term) in idtac)); fail).
Ltac run0 sz := Harness.runtests args_of_size describe_goal mkgoal redgoal time_solve_goal0 sz.
(*
Goal True. run0 SuperFast.
*)
