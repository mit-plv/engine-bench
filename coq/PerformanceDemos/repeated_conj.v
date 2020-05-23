(** * performance of proving large conjunctions without structural types *)
Fixpoint nconj (n : nat) := match n with 0 => True | S n => and True (nconj n) end.

Goal nconj 100. Time repeat constructor. Qed.
(* Finished transaction in 0.034 secs (0.034u,0.s) (successful) *)
Goal nconj 1000. Time repeat constructor. Qed.
(* Finished transaction in 1.216 secs (1.18u,0.035s) (successful) *)
Goal nconj 2000. Time repeat constructor. Qed.
(* Finished transaction in 4.793 secs (4.717u,0.075s) (successful) *)

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
  cbv [nconj];
  time "pose build and refine"
       (let G := match goal with |- ?G => G end in
        refine (_ : G);
        preshare_pf
          G ltac:(fun G pf => time "refine" refine pf)).

Goal nconj 1000. Time fast_conj. Time Optimize Proof. Time Qed.
(* Tactic call refine ran for 0.009 secs (0.009u,0.s) (success)
Tactic call pose build and refine ran for 0.434 secs (0.422u,0.011s) (success)

Finished transaction in 0.435 secs (0.423u,0.011s) (successful)
Evars: 1006 -> 0

Finished transaction in 0.955 secs (0.951u,0.003s) (successful)
Finished transaction in 0.091 secs (0.087u,0.003s) (successful)
*)
Goal nconj 2000. Time fast_conj. Time Optimize Proof. Time Qed.
(* Tactic call refine ran for 0.02 secs (0.02u,0.s) (success)
Tactic call pose build and refine ran for 1.454 secs (1.438u,0.015s) (success)

Finished transaction in 1.456 secs (1.44u,0.016s) (successful)
Evars: 2006 -> 0

Finished transaction in 11.191 secs (11.167u,0.023s) (successful)
Finished transaction in 0.279 secs (0.279u,0.s) (successful)
 *)
