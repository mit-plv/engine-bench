Require Import Ltac2.Ltac2.
Require Import Ltac2.Constr.
Require Import PerformanceExperiments.Ltac2Compat.Constr.
Require Import Ltac2.Control.
Require Ltac2.Notations.
Require Ltac2.Array.
Require PerformanceExperiments.Ltac2Compat.Array.
Require Ltac2.Int.
Require Import PerformanceExperiments.Harness.

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

Module Import WithLtac2.
  Import Ltac2.Notations.

  Ltac2 rec build_fun (n : int) (tt : constr) (uni : constr) :=
    match Int.lt 0 n with
    | false => tt
    | true
      => let rest := build_fun (Int.sub n 1) tt uni in
         Unsafe.make (Unsafe.mkLambda (Binder.make None uni) rest)
    end.

  Ltac2 rec int_of_nat n :=
    (lazy_match! n with
    | O => 0
    | S ?n => Int.add 1 (int_of_nat n)
     end).
  Ltac2 time_solve_goal0 n :=
    let n := int_of_nat n in
    let tt := 'tt in
    let uni := 'unit in
    let v := Control.time
               (Some "build-and-typecheck")
               (fun _ =>
                  let v := Control.time (Some "build") (fun _ => build_fun n tt uni) in
                  let __ := Control.time (Some "typecheck") (fun _ => Unsafe.check v) in
                  v) in
    ().
End WithLtac2.

Ltac mkgoal _ := constr:(True).
Ltac redgoal _ := idtac.
Ltac time_solve_goal0 n :=
  let n := (eval vm_compute in (Z.to_nat n)) in
  let f := ltac2:(n |- time_solve_goal0 (match (Ltac1.to_constr n) with Some v => v | None => 'I end)) in
  f n.
Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.

Global Set Default Proof Mode "Classic".
(*
Goal True. run0 SuperFast.
*)
