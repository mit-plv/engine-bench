Require Import PerformanceExperiments.Harness.
Require Import PerformanceExperiments.lift_identity_evar_subst_common.

Ltac describe_goal0 := describe_goal_x.
Ltac time_solve_goal0 := time_solve_goal_x.
Definition args_of_size0 := args_of_size_x.

Ltac run0 sz := Harness.runtests args_of_size0 describe_goal0 mkgoal redgoal time_solve_goal0 sz.
