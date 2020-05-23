(** * Performance Criterion: Adding a new let binder underneath n lets should be Õ(1) *)

(** We can establish this criterion in two ways: using the proof
    engine to add a new let binder, or looking at the marginal
    increase of adding another let binder to a term and
    re-type-checking it. *)

(** Note that in Coq, this is severely complicated by the overhead of
    fresh name generation. *)

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
