Require Import PerformanceExperiments.Harness.

Fixpoint letn n (x : nat) (k : nat -> Prop) :=
  match n with
  | O => k x
  | S n =>
    let x := S x in
    letn n x k
  end.

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 0 3
     | SuperFast => seq 0 100
     | Fast => List.map (fun x => 50 * x) (seq 0 40)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac mkgoal n := constr:(letn n O (fun _ => True)).
Ltac redgoal _ := idtac.
Ltac time_solve_goal0 n :=
  cut True;
  [ intros _;
    time "abstract-intros"
         abstract (
           cbv beta iota delta [letn];
           time "intros" intros;
           restart_timer;
           exact I
         )
  | finish_timing ("Tactic call close-abstract") ].
Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.
(*
Goal True. run0 Fast.
 *)
