(** * Performance Criterion: Adding a new let binder underneath n lets should be Õ(1) *)

(** We can establish this criterion in three ways: using the proof
    engine to add a new let binder either (a) via [pose] or (b) via
    [intro], or (c) looking at the marginal increase of adding another
    let binder to a term and re-type-checking it. *)

(** Note that in Coq, this is severely complicated by the overhead of
    fresh name generation. *)

(** See also COQBUG(https://github.com/coq/coq/issues/8244) *)

Goal True.
  Time (do 1000 pose I).
  (* Finished transaction in 0.293 secs (0.289u,0.003s) (successful) *)
  Time (do 1000 pose I).
  (* Finished transaction in 0.746 secs (0.734u,0.011s) (successful) *)
  Time (do 1000 pose I).
  (* Finished transaction in 1.29 secs (1.27u,0.019s) (successful) *)
Abort.

Ltac make n :=
  lazymatch n with
  | O => uconstr:(I)
  | S ?n => let rest := make n in
            uconstr:(let _ := I in rest)
  end.

Ltac make_and_check n :=
  restart_timer;
  let res := make n in
  finish_timing ("Tactic call make");
  restart_timer;
  let res := constr:(res) in
  finish_timing ("Tactic call constr");
  idtac.

Goal True.
  make_and_check 1000.
  (* Tactic call make ran for 0.037 secs (0.022u,0.015s)
Tactic call constr ran for 0.011 secs (0.011u,0.s)
   *)
  make_and_check 2000.
  (* Tactic call make ran for 0.051 secs (0.045u,0.005s)
Tactic call constr ran for 0.047 secs (0.047u,0.s)
*)
  make_and_check 4000.
  (* Tactic call make ran for 0.094 secs (0.094u,0.s)
Tactic call constr ran for 0.205 secs (0.205u,0.s)
   *)
Abort.


Fixpoint letn n (x : nat) (k : nat -> Prop) :=
  match n with
  | O => k x
  | S n =>
    let x := S x in
    letn n x k
  end.

Goal letn 250 O (fun _ => True). cbv beta iota delta [letn]. Time intros. Time Optimize Proof. exact I. Qed.
(*Finished transaction in 0.029 secs (0.022u,0.006s) (successful)
Evars: 253 -> 1
Finished transaction in 0.012 secs (0.012u,0.s) (successful) *)
Goal letn 500 O (fun _ => True). cbv beta iota delta [letn]. Time intros. Time Optimize Proof. exact I. Qed.
(* Finished transaction in 0.055 secs (0.054u,0.s) (successful)
Evars: 503 -> 1
Finished transaction in 0.123 secs (0.122u,0.s) (successful) *)
Goal letn 1000 O (fun _ => True). cbv beta iota delta [letn]. Time intros. Time Optimize Proof. exact I. Qed.
(* Finished transaction in 0.264 secs (0.257u,0.006s) (successful)
Evars: 1003 -> 1
Finished transaction in 0.73 secs (0.726u,0.003s) (successful) *)
Goal letn 2000 O (fun _ => True). cbv beta iota delta [letn]. Time intros. Time Optimize Proof. exact I. Qed.
(* Finished transaction in 1.09 secs (1.077u,0.009s) (successful)
Evars: 2003 -> 1
Finished transaction in 6.754 secs (6.741u,0.006s) (successful) *)
(*
Goal letn 4000 O (fun _ => True). cbv beta iota delta [letn]. Time intros. Time Optimize Proof. exact I. Qed.
(* Finished transaction in 4.324 secs (4.235u,0.079s) (successful)
Evars: 4003 -> 1
Finished transaction in 68.641 secs (68.531u,0.073s) (successful) *)
 *)
