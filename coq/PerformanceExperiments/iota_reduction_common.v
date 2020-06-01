Require Import PerformanceExperiments.Harness.

Fixpoint fact (n : nat) := match n with 0 => 1 | S n' => n * fact n' end.
Fixpoint walk (n : nat) : unit := match n with 0 => tt | S n => walk n end.
Definition skip (n : nat) : unit := tt.
Inductive value := the (A : Type) (_ : A).
Arguments the : clear implicits.
Notation slown n := (the (walk (fact n) = tt) (eq_refl tt)) (only parsing).
Notation fastn n := (the (skip (fact n) = tt) (eq_refl tt)) (only parsing).

Notation iota_the v := match v return value with
                       | the A a => the A a
                       end.

Inductive speed := slow | fast.
Ltac describe_goal_gen factn speed n := idtac "Params: a-n=" n ", fact-n=" factn (* ", speed=" speed*).
Ltac step_goal_constr _ v := uconstr:(iota_the v).
Ltac redgoal_constr _ v := constr:(v).
Ltac time_solve_goal_gen_slow with_abstract n v :=
  optimize_heap;
  restart_timer;
  let v2 := (eval cbv beta iota in v) in
  finish_timing ("Tactic call beta-iota-slow");
  time "unify-beta-iota-slow" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-beta-iota-slow" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.
Ltac time_solve_goal_gen_fast with_abstract n v :=
  optimize_heap;
  restart_timer;
  let v2 := (eval cbv beta iota in v) in
  finish_timing ("Tactic call beta-iota-fast");
  time "unify-beta-iota-fast" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-beta-iota-fast" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.
Ltac mkgoal_init speed factn :=
  let factn := (eval cbv in (Z.to_nat factn)) in
  lazymatch speed with
  | slow => constr:(slown factn)
  | fast => constr:(fastn factn)
  end.
