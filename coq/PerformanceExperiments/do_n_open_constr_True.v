Require Import PerformanceExperiments.Harness.

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 0 3
     | SuperFast => seq 0 300
     | Fast => (List.map (fun x => x * 2) (seq 0 200))
                 ++ (List.map (fun x => 400 + 10 * x) (seq 0 30))
                 ++ (List.map (fun x => 700 + 100 * x) (seq 0 24))
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac step_goal _ := pose proof I.
Ltac redgoal _ := idtac.
Ltac time_solve_goal0 n :=
  time "open-constr-True-1000" (do 1000 let v := open_constr:(_ : True) in idtac).
Ltac run0 sz := Harness.runtests_step args_of_size default_describe_goal step_goal redgoal time_solve_goal0 sz.
(*
Goal True. run0 Fast.
*)
