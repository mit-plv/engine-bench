Require Import PerformanceExperiments.Harness.

Ltac make_uconstr n :=
  lazymatch n with
  | O => uconstr:(_)
  | S ?n => let ret := make_uconstr n in
            uconstr:(fun x => ret)
  end.

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 0 3
     | SuperFast => seq 0 500
     | Fast => (List.map (fun x => x * 10) (seq 0 100))
                 ++ (List.map (fun x => x * 100) (seq 0 31))
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac mkgoal n := True.
Ltac redgoal _ := idtac.
Ltac time_solve_goal0 n :=
  time "build-and-open" (
         restart_timer;
         let preterm := make_uconstr n in
         finish_timing ( "Tactic call uconstr" );
         restart_timer;
         let term := open_constr:(preterm) in
         finish_timing ( "Tactic call open_constr" );
         idtac).
Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.
(*
Goal True. run0 Fast.
*)
