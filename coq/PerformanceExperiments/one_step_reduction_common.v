Require Import PerformanceExperiments.Harness.

Notation "'subst!' v 'for' x 'in' f" := (match v with x => f end) (only parsing, at level 200).

Ltac uconstr_beta1 term :=
  lazymatch term with
  | ((fun x => ?f) ?v) => uconstr:(subst! v for x in f)
  end.

Ltac uconstr_zeta1 term :=
  lazymatch term with
  | (let x := ?v in ?f) => uconstr:(subst! v for x in f)
  end.

Ltac beta1 term :=
  lazymatch term with
  | ((fun x => ?f) ?v) => constr:(subst! v for x in f)
  end.

Ltac zeta1 term :=
  lazymatch term with
  | (let x := ?v in ?f) => constr:(subst! v for x in f)
  end.

Fixpoint fact (n : nat) := match n with 0 => 1 | S n' => n * fact n' end.
Fixpoint walk (n : nat) : unit := match n with 0 => tt | S n => walk n end.
Definition skip (n : nat) : unit := tt.
Inductive value := the (A : Type) (_ : A).
Arguments the : clear implicits.
Time Definition slow := the (walk (fact 9) = tt) (eq_refl tt).
(* Finished transaction in 1.069 secs (1.052u,0.016s) (successful) *)
Definition fast := the (skip (fact 9) = tt) (eq_refl tt).
Axiom Ax_fst : forall {A B}, A * B -> A.
Axiom Ax_snd : forall {A B}, A * B -> B.
Fixpoint big_tree {A} (v : A) (n : nat) : A
  := match n with
     | 0 => Ax_fst (v, v)
     | S n => big_tree (Ax_fst (v, v)) n
     end.
Definition big_slow (n : nat) := Eval cbv [big_tree] in big_tree slow n.
Definition big_fast (n : nat) := Eval cbv [big_tree] in big_tree fast n.
(** Tell conversion to unfold [slow] and [fast] early, so that we
    don't run the risk of trying to unfold [fact] during conversion
    when we don't want to. *)
Strategy -10 [slow fast].

Ltac test_delta1_slow with_abstract n :=
  optimize_heap;
  let v := (eval cbv [big_slow] in (big_slow n)) in
  restart_timer;
  let v2 := (eval cbv delta [slow] in v) in
  finish_timing ("Tactic call delta-1-slow");
  time "unify-delta-1-slow" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-delta-1-slow" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.

Ltac test_delta1_fast with_abstract n :=
  optimize_heap;
  let v := (eval cbv [big_fast] in (big_fast n)) in
  restart_timer;
  let v2 := (eval cbv delta [fast] in v) in
  finish_timing ("Tactic call delta-1-fast");
  time "unify-delta-1-fast" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-delta-1-fast" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.

Ltac test_delta with_abstract n := test_delta1_fast with_abstract n; test_delta1_slow with_abstract n.

Fixpoint big_tree2 (n : nat) {A} (v1 v2 : A) : A
  := match n with
     | 0 => Ax_fst (v1, v2)
     | S n => big_tree2 n (Ax_fst (v1, v2)) (Ax_snd (v1, v2))
     end.
Definition big_slow_beta1 (n : nat) := Eval cbv [big_tree2 slow] in id (fun v => big_tree2 n v v) slow.
Definition big_fast_beta1 (n : nat) := Eval cbv [big_tree2 fast] in id (fun v => big_tree2 n v v) fast.
Definition big_slow_beta2 (n : nat) := Eval cbv [big_tree2 slow] in id (big_tree2 n) slow slow.
Definition big_fast_beta2 (n : nat) := Eval cbv [big_tree2 fast] in id (big_tree2 n) fast fast.

Ltac beta_id v :=
  lazymatch v with
  | id ?f ?x => constr:(f x)
  | id ?f ?x ?y => constr:(f x y)
  end.

Ltac test_beta1_slow with_abstract n :=
  optimize_heap;
  let v := (eval cbv [big_slow_beta1] in (big_slow_beta1 n)) in
  let v := beta_id v in
  restart_timer;
  let v2 := (eval cbv beta in v) in
  finish_timing ("Tactic call beta-1-slow");
  time "unify-beta-1-slow" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-beta-1-slow" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.

Ltac test_beta2_slow with_abstract n :=
  optimize_heap;
  let v := (eval cbv [big_slow_beta2] in (big_slow_beta2 n)) in
  let v := beta_id v in
  restart_timer;
  let v2 := (eval cbv beta in v) in
  finish_timing ("Tactic call beta-2-slow");
  time "unify-beta-2-slow" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-beta-2-slow" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.

Ltac test_beta1_fast with_abstract n :=
  optimize_heap;
  let v := (eval cbv [big_fast_beta1] in (big_fast_beta1 n)) in
  let v := beta_id v in
  restart_timer;
  let v2 := (eval cbv beta in v) in
  finish_timing ("Tactic call beta-1-fast");
  time "unify-beta-1-fast" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-beta-1-fast" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.

Ltac test_beta2_fast with_abstract n :=
  optimize_heap;
  let v := (eval cbv [big_fast_beta2] in (big_fast_beta2 n)) in
  let v := beta_id v in
  restart_timer;
  let v2 := (eval cbv beta in v) in
  finish_timing ("Tactic call beta-2-fast");
  time "unify-beta-2-fast" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-beta-2-fast" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.

Ltac test_beta with_abstract n := test_beta1_fast with_abstract n; test_beta2_fast with_abstract n; test_beta1_slow with_abstract n; test_beta2_slow with_abstract n.

Definition big_slow_zeta1 (n : nat) := Eval cbv beta iota delta [big_tree2 slow] in let v := slow in big_tree2 n v v.
Definition big_fast_zeta1 (n : nat) := Eval cbv beta iota delta [big_tree2 fast] in let v := fast in big_tree2 n v v.
Definition big_slow_zeta2 (n : nat) := Eval cbv beta iota delta [big_tree2 slow] in let v1 := slow in let v2 := slow in big_tree2 n v1 v2.
Definition big_fast_zeta2 (n : nat) := Eval cbv beta iota delta [big_tree2 fast] in let v1 := fast in let v2 := fast in big_tree2 n v1 v2.

Ltac test_zeta1_slow with_abstract n :=
  optimize_heap;
  let v := (eval cbv beta iota delta [big_slow_zeta1] in (big_slow_zeta1 n)) in
  restart_timer;
  let v2 := (eval cbv zeta in v) in
  finish_timing ("Tactic call zeta-1-slow");
  time "unify-zeta-1-slow" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-zeta-1-slow" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.

Ltac test_zeta2_slow with_abstract n :=
  optimize_heap;
  let v := (eval cbv beta iota delta [big_slow_zeta2] in (big_slow_zeta2 n)) in
  restart_timer;
  let v2 := (eval cbv zeta in v) in
  finish_timing ("Tactic call zeta-2-slow");
  time "unify-zeta-2-slow" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-zeta-2-slow" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.

Ltac test_zeta1_fast with_abstract n :=
  optimize_heap;
  let v := (eval cbv beta iota delta [big_fast_zeta1] in (big_fast_zeta1 n)) in
  restart_timer;
  let v2 := (eval cbv zeta in v) in
  finish_timing ("Tactic call zeta-1-fast");
  time "unify-zeta-1-fast" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-zeta-1-fast" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.

Ltac test_zeta2_fast with_abstract n :=
  optimize_heap;
  let v := (eval cbv beta iota delta [big_fast_zeta2] in (big_fast_zeta2 n)) in
  restart_timer;
  let v2 := (eval cbv zeta in v) in
  finish_timing ("Tactic call zeta-2-fast");
  time "unify-zeta-2-fast" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-zeta-2-fast" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.

Ltac test_zeta with_abstract n := test_zeta1_fast with_abstract n; test_zeta2_fast with_abstract n; test_zeta1_slow with_abstract n; test_zeta2_slow with_abstract n.

Definition args_of_size_with_abstract (s : size) : list nat
  := match s with
     | Sanity => seq 1 1
     | SuperFast => seq 1 3
     | Fast => []
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Definition args_of_size_without_abstract (s : size) : list nat
  := match s with
     | Sanity => seq 1 3
     | SuperFast => seq 1 13
     | Fast => seq 1 15
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac mkgoal n := constr:(True).
Ltac redgoal _ := idtac.

(*
Goal True. run1 SuperFast.
*)
