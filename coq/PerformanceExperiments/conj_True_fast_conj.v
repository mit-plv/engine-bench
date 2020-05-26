Require Import PerformanceExperiments.Harness.

Fixpoint and_True (n : nat)
  := match n with
     | 0 => True
     | S n => True /\ and_True n
     end.

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 1 3
     | SuperFast => seq 1 100
     | Fast => seq 100 200
                   ++ List.map (fun x => 200 + x * 2) (seq 0 50)
                   ++ List.map (fun x => 300 + x * 5) (seq 0 20)
                   ++ List.map (fun x => 400 + x * 10) (seq 0 10)
                   ++ List.map (fun x => 500 + x * 50) (seq 0 10)
                   ++ List.map (fun x => 1000 + x * 100) (seq 0 10)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac preshare_pf G cont :=
  lazymatch G with
  | True => cont True I
  | ?L /\ ?R
    => preshare_pf
         L ltac:(
         fun L l
         => preshare_pf
              R ltac:(
              fun R r
              => let H := fresh in
                 pose (and L R) as H;
                 cont H uconstr:(@conj L R l r)))
  | _ => fail 0 "invalid:" G
  end.

Ltac fast_conj :=
  time "pose build and refine"
       (let G := match goal with |- ?G => G end in
        refine (_ : G);
        preshare_pf
          G ltac:(fun G pf => time "refine" refine pf)).

Ltac mkgoal n := constr:(and_True (pred n)).
Ltac redgoal _ := vm_compute.
Ltac time_solve_goal0 n :=
  cut True;
  [ intros _;
    time "abstract-fast_conj"
         abstract
         (cut True;
          [ intros _;
            time "fast_conj" fast_conj
          | restart_timer; exact I ])
  | finish_timing ("Tactic call close-abstract") ].

Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.
(*
Goal True. run0 SuperFast.
*)
