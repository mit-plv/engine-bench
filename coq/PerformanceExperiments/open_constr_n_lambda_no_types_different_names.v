Require Import PerformanceExperiments.Harness.

Ltac make_uconstr n x :=
  lazymatch n with
  | O => uconstr:(_)
  | S ?n => let __ := match goal with _ => pose I as x end in
            let x' := fresh x in
            let ret := make_uconstr n x' in
            let __ := match goal with _ => clear x end in
            uconstr:(fun x' => ret)
  end.

Definition args_of_size (s : size) : list nat
  := match s with
     | SuperFast => seq 0 500
     | Fast => (List.map (fun x => x * 10) (seq 0 100))
                 ++ (List.map (fun x => x * 100) (seq 0 22))
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac mkgoal n := True.
Ltac redgoal _ := idtac.
Ltac time_solve_goal0 n :=
  time "build-and-open" (
         restart_timer;
         let x := fresh "x" in
         let preterm := make_uconstr n x in
         finish_timing ( "Tactic call uconstr" );
         restart_timer;
         let term := open_constr:(preterm) in
         finish_timing ( "Tactic call open_constr" );
         idtac).
Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.
(*
Goal True. run0 Fast.
*)
