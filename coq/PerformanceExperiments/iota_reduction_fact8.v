Require Import PerformanceExperiments.Harness.
Require Export PerformanceExperiments.iota_reduction_common.

Global Open Scope Z_scope.

Local Notation factn := 8.
Local Notation with_abstract := false.

Definition args_of_size (s : size) : list Z
  := match s with
     | Sanity => List.map Z.of_nat (seq 0 3)
     | SuperFast => List.map (fun x => Z.of_nat x * 100) (seq 1 10)
     | Fast => List.map (fun x => Z.of_nat x * 100) (seq 1 100)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac describe_goal0 n := describe_goal_gen constr:(factn) slow n.
Ltac time_solve_goal0 n v := time_solve_goal_gen_slow constr:(with_abstract) n v.
Ltac run0 sz := idtac; Harness.runtests_step_constr args_of_size describe_goal0 step_goal_constr redgoal_constr time_solve_goal0 sz ltac:(mkgoal_init slow constr:(factn)).

Ltac describe_goal1 n := describe_goal_gen constr:(factn) fast n.
Ltac time_solve_goal1 n v := time_solve_goal_gen_fast constr:(with_abstract) n v.
Ltac run1 sz := Harness.runtests_step_constr args_of_size describe_goal1 step_goal_constr redgoal_constr time_solve_goal1 sz ltac:(mkgoal_init fast constr:(factn)).

(*
Goal True. run0 Fast.
*)
