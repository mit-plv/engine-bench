Require Import PerformanceExperiments.Harness.

Fixpoint n_units (n : nat)
  := match n with
     | 0 => unit
     | S n => unit -> n_units n
     end.

Definition goal (n : nat) := n_units n -> unit.

Ltac build_app n f :=
  lazymatch n with
  | 0 => f
  | S ?n => build_app n uconstr:(f tt)
  end.

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 0 3
     | SuperFast => List.map (fun x => x * 100) (seq 0 70)
     | Fast => List.map (fun x => x * 100) (seq 0 128) (* stack overflow at 12800 *)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac mkgoal n := constr:(goal n).
Ltac redgoal _ := vm_compute.
Ltac time_solve_goal0 n :=
  let f := fresh "f" in
  intro f;
  time "build-and-refine"
       (restart_timer;
        let term := build_app n f in
        finish_timing ( "Tactic call build" );
        restart_timer;
        let term := constr:(term) in
        finish_timing ( "Tactic call to_constr" );
        restart_timer;
        let __ := type of term in
        finish_timing ( "Tactic call type_of" );
        time "refine" refine term).
Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.

(*
Goal True.
  run0 SuperFast.
 *)
