Require Import PerformanceExperiments.Harness.

Ltac make_uconstr n :=
  lazymatch n with
  | O => uconstr:(I)
  | S ?n => let rest := make_uconstr n in
            uconstr:(let _ := I in rest)
  end.

Ltac make_uconstr_and_check n :=
  restart_timer;
  let res := make_uconstr n in
  finish_timing ("Tactic call make_uconstr");
  restart_timer;
  let res := constr:(res) in
  finish_timing ("Tactic call constr");
  idtac.

Global Open Scope Z_scope.

Definition args_of_size (s : size) : list Z
  := match s with
     | Sanity => List.map Z.of_nat (seq 0 3)
     | SuperFast => List.map (fun x => Z.of_nat x * 100) (seq 0 70)
     | Fast => List.map (fun x => Z.of_nat x * 500) (seq 0 30) (* Stack overflow after about 30 *)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac mkgoal _ := constr:(True).
Ltac redgoal _ := idtac.
Ltac time_solve_goal0 n :=
  let n := (eval vm_compute in (Z.to_nat n)) in
  make_uconstr_and_check n.

Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.

(*
Goal True. run0 Fast.
 *)
