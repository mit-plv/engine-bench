Require Import PerformanceExperiments.Harness.
Require Export PerformanceExperiments.one_step_reduction_common.

Ltac time_solve_goal0 n := test_delta true n.
Ltac time_solve_goal1 n := test_beta true n.
Ltac time_solve_goal2 n := test_zeta true n.

Ltac run0 sz := Harness.runtests args_of_size_with_abstract default_describe_goal mkgoal redgoal time_solve_goal0 sz.
Ltac run1 sz := Harness.runtests args_of_size_with_abstract default_describe_goal mkgoal redgoal time_solve_goal1 sz.
Ltac run2 sz := Harness.runtests args_of_size_with_abstract default_describe_goal mkgoal redgoal time_solve_goal2 sz.

(*
Goal True. run1 SuperFast.
*)
