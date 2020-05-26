Require Import PerformanceExperiments.Harness.
Require Export PerformanceExperiments.rewrite_under_binders_common.

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 0 3
     | SuperFast => List.map (fun x => x * 50) (seq 1 4)
     | Fast => List.map (fun x => x * 10) (seq 1 20)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac time_solve_goal0 n :=
  time "repeat-setoid_rewrite" repeat setoid_rewrite <- plus_n_O.

Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.

(*
Goal True.
  run0 SuperFast.
 *)
