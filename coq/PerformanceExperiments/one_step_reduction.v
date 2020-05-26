Require Import PerformanceExperiments.Harness.
Require Export PerformanceExperiments.one_step_reduction_common.

Ltac time_solve_goal0 n := test_delta false n.
Ltac time_solve_goal1 n := test_beta false n.
Ltac time_solve_goal2 n := test_zeta false n.

Ltac run0 sz := Harness.runtests args_of_size_without_abstract default_describe_goal mkgoal redgoal time_solve_goal0 sz.
Ltac run1 sz := Harness.runtests args_of_size_without_abstract default_describe_goal mkgoal redgoal time_solve_goal1 sz.
Ltac run2 sz := Harness.runtests args_of_size_without_abstract default_describe_goal mkgoal redgoal time_solve_goal2 sz.

(*
Goal True. run1 SuperFast.
*)
