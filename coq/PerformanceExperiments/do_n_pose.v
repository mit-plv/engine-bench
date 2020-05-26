Require Import PerformanceExperiments.Harness.
Global Open Scope Z_scope.
Definition args_of_size (s : size) : list Z
  := match s with
     | Sanity => List.map Z.of_nat (seq 0 3)
     | SuperFast => List.map (fun v => 1000 + 100 * Z.of_nat v) (seq 0 10)
     | Fast => List.map (fun v => 1000 + 100 * Z.of_nat v) (seq 0 100)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac step_goal _ := pose I.
Ltac redgoal _ := idtac.
Ltac time_solve_goal0 n := let H := fresh in time "do-100-pose-I" do 100 (pose I as H; clear H).
Ltac run0 sz := Harness.runtests_step args_of_size default_describe_goal step_goal redgoal time_solve_goal0 sz.

(*
Goal True. run0 Fast.
*)
