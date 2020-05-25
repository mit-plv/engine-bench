(** * Performance Criterion: Adding a new binder underneath n binders should be Õ(1) *)

(** We can establish this criterion in two ways: using the proof
    engine to add a new binder via [intro], or looking at the marginal
    increase of adding another binder to a term and re-type-checking
    it. *)

(** Note that in Coq, this is severely complicated by the overhead of
    fresh name generation. *)

(** See also COQBUG(https://github.com/coq/coq/issues/8244) *)

Fixpoint foralln n (x : nat) (k : nat -> Prop) :=
  match n with
  | O => k x
  | S n =>
    forall x : nat, foralln n x k
  end.

Goal foralln 250 O (fun _=> True). cbv beta iota delta [foralln]. Time intros. Time Optimize Proof. exact I. Qed.
(* Finished transaction in 0.034 secs (0.034u,0.s) (successful)
Evars: 253 -> 1
Finished transaction in 0.012 secs (0.011u,0.s) (successful) *)
Goal foralln 500 O (fun _=> True). cbv beta iota delta [foralln]. Time intros. Time Optimize Proof. exact I. Qed.
(* Finished transaction in 0.052 secs (0.051u,0.s) (successful)
Evars: 503 -> 1
Finished transaction in 0.113 secs (0.113u,0.s) (successful) *)
Goal foralln 1000 O (fun _=>True). cbv beta iota delta [foralln]. Time intros. Time Optimize Proof. exact I. Qed.
(* Finished transaction in 0.217 secs (0.213u,0.003s) (successful)
Evars: 1003 -> 1
Finished transaction in 0.796 secs (0.795u,0.s) (successful) *)
Goal foralln 2000 O (fun _=>True). cbv beta iota delta [foralln]. Time intros. Time Optimize Proof. exact I. Qed.
(* Finished transaction in 0.944 secs (0.924u,0.016s) (successful)
Evars: 2003 -> 1
Finished transaction in 6.819 secs (6.801u,0.009s) (successful) *)
(*
Goal foralln 4000 O (fun _=>True). cbv beta iota delta [foralln]. Time intros. Time Optimize Proof. exact I. Qed.
(* Finished transaction in 4.415 secs (4.384u,0.016s) (successful)
Evars: 4003 -> 1
Finished transaction in 72.025 secs (71.63u,0.122s) (successful) *)
 *)

Ltac make n :=
  lazymatch n with
  | O => uconstr:(tt)
  | S ?n => let rest := make n in
            uconstr:(fun _ : unit => rest)
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
  (* Tactic call make ran for 0.02 secs (0.02u,0.s)
Tactic call constr ran for 0.024 secs (0.024u,0.s)
   *)
  make_and_check 2000.
  (* Tactic call make ran for 0.048 secs (0.048u,0.s)
Tactic call constr ran for 0.046 secs (0.046u,0.s)
*)
  make_and_check 4000.
  (* Tactic call make ran for 0.082 secs (0.078u,0.003s)
Tactic call constr ran for 0.234 secs (0.23u,0.004s)
   *)
Abort.
