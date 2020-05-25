Require Import Ltac2.Ltac2.
Require Import Ltac2.Constr.
Require Import Ltac2.Control.
Require Ltac2.Notations.
Require Ltac2.Array.
Require Ltac2.Int.
Require Import PerformanceExperiments.Harness.

Fixpoint n_units (n : nat)
  := match n with
     | 0 => unit
     | S n => unit -> n_units n
     end.

Definition goal (n : nat) := n_units n -> unit.

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 0 3
     | SuperFast => List.map (fun x => x * 100) (seq 0 70)
     | Fast => List.map (fun x => x * 100) (seq 0 201)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.


Module Import WithLtac2.
  Import Ltac2.Notations.

  Ltac2 build_app (n : int) (f : constr) :=
    match Int.lt 0 n with
    | false => f
    | true => Unsafe.make (Unsafe.App f (Array.make n 'tt))
    end.

  Ltac2 rec int_of_nat n :=
    (lazy_match! n with
    | 0 => 0
    | S ?n => Int.add 1 (int_of_nat n)
     end).
  Ltac2 time_solve_goal0 n :=
    let n := int_of_nat n in
    (intro f;
    let f := '&f in
    let v := Control.time
               (Some "build-and-typecheck")
               (fun _ =>
                  let v := Control.time (Some "build") (fun _ => build_app n f) in
                  let __ := Control.time (Some "typecheck") (fun _ => Unsafe.check v) in
                  v) in
    Control.time (Some "refine") (fun _ => refine v)).
End WithLtac2.

Ltac mkgoal n := constr:(goal n).
Ltac redgoal _ := vm_compute.
Ltac time_solve_goal0 :=
  ltac2:(n |- time_solve_goal0 (match (Ltac1.to_constr n) with Some v => v | None => 'I end)).
Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.

Global Set Default Proof Mode "Classic".
(*
Goal True. run0 SuperFast.
*)
