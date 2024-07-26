(** * performance of turning f (f (... (f x))) = g (g (... (g x))) given f x = g x (or x = y -> f x = g y) w/ rewrite_strat *)
From Coq Require Import Setoid Morphisms.
Axiom f : nat -> nat.
Axiom g : nat -> nat.
Axiom fg : forall x, f x = g x.
Lemma fg_ext : forall x y, x = y -> f x = g y.
Proof. intros; subst; apply fg. Qed.

#[global]
Hint Rewrite fg : rew_fg.

Fixpoint comp_pow {A} (f : A -> A) (n : nat) (x : A) {struct n} : A
  := match n with
     | O => x
     | S n => f (comp_pow f n x)
     end.

Local Infix "^" := comp_pow : core_scope.

Goal forall x, (f^100) x = (g^100) x. cbv [comp_pow]; intro. Time autorewrite with rew_fg. reflexivity. Abort.
(* Finished transaction in 0.129 secs (0.129u,0.s) (successful) *)
Goal forall x, (f^200) x = (g^200) x. cbv [comp_pow]; intro. Time autorewrite with rew_fg. reflexivity. Abort.
(* Finished transaction in 0.452 secs (0.452u,0.s) (successful) *)
Goal forall x, (f^400) x = (g^400) x. cbv [comp_pow]; intro. Time autorewrite with rew_fg. reflexivity. Abort.
(* Finished transaction in 2.151 secs (2.14u,0.01s) (successful) *)

Goal forall x, (f^100) x = (g^100) x. cbv [comp_pow]; intro. Time rewrite !fg. reflexivity. Abort.
(* Finished transaction in 0.129 secs (0.129u,0.s) (successful) *)
Goal forall x, (f^200) x = (g^200) x. cbv [comp_pow]; intro. Time rewrite !fg. reflexivity. Abort.
(* Finished transaction in 0.48 secs (0.468u,0.011s) (successful) *)
Goal forall x, (f^400) x = (g^400) x. cbv [comp_pow]; intro. Time rewrite !fg. reflexivity. Abort.
(* Finished transaction in 2.187 secs (2.179u,0.007s) (successful) *)

Goal forall x, (f^100) x = (g^100) x. cbv [comp_pow]; intro. Time rewrite_strat topdown hints rew_fg. reflexivity. Abort.
(* Finished transaction in 0.356 secs (0.356u,0.s) (successful) *)
Goal forall x, (f^200) x = (g^200) x. cbv [comp_pow]; intro. Time rewrite_strat topdown hints rew_fg. reflexivity. Abort.
(* Finished transaction in 0.887 secs (0.883u,0.003s) (successful) *)
Goal forall x, (f^400) x = (g^400) x. cbv [comp_pow]; intro. Time rewrite_strat topdown hints rew_fg. reflexivity. Abort.
(* Finished transaction in 2.925 secs (2.901u,0.023s) (successful) *)

Goal forall x, (f^100) x = (g^100) x. cbv [comp_pow]; intro. Time rewrite_strat bottomup hints rew_fg. reflexivity. Abort.
(* Finished transaction in 0.431 secs (0.431u,0.s) (successful) *)
Goal forall x, (f^200) x = (g^200) x. cbv [comp_pow]; intro. Time rewrite_strat bottomup hints rew_fg. reflexivity. Abort.
(* Finished transaction in 1.282 secs (1.277u,0.003s) (successful) *)
Goal forall x, (f^400) x = (g^400) x. cbv [comp_pow]; intro. Time rewrite_strat bottomup hints rew_fg. reflexivity. Abort.
(* Finished transaction in 4.382 secs (4.338u,0.039s) (successful) *)

Ltac preshare_pf f g fx gy Hfg_ext cont :=
  lazymatch fx with
  | f ?x
    => lazymatch gy with
       | g ?y
         => preshare_pf
              f g x y Hfg_ext
              ltac:(fun x' y' pf
                    => let fH := fresh f in
                       let gH := fresh g in
                       let __ := match goal with _ => pose (f x') as fH; pose (g y') as gH end in
                       cont fH gH uconstr:(Hfg_ext x' y' pf))
       | _ => fail 0 "Invalid mismatch" fx gy
       end
  | ?x
    => lazymatch gy with
       | x
         => let A := type of x in
            cont x x uconstr:(@eq_refl A x)
       | _ => fail 0 "Invalid mismatch" fx gy
       end
  end.

Ltac fast_rewrite :=
  cbv [comp_pow];
  intro;
  time "pose build and refine"
    lazymatch goal with
    | [ |- f ?x = g ?y :> ?A ]
      => refine (_ : f x = g y :> A);
         preshare_pf
           f g (f x) (g y) fg_ext
           ltac:(fun x' y' pf
                 => time "refine" refine pf)
    end.

Goal forall x, (f^100) x = (g^100) x. Time fast_rewrite. Time Optimize Proof. Time Qed.
(* Tactic call refine ran for 0.001 secs (0.001u,0.s) (success)
Tactic call pose build and refine ran for 0.019 secs (0.019u,0.s) (success)

Finished transaction in 0.019 secs (0.019u,0.s) (successful)
Evars: 212 -> 0

Finished transaction in 0.008 secs (0.008u,0.s) (successful)
Finished transaction in 0.004 secs (0.004u,0.s) (successful) *)
Goal forall x, (f^200) x = (g^200) x. Time fast_rewrite. Time Optimize Proof. Time Qed.
(* Tactic call refine ran for 0.001 secs (0.001u,0.s) (success)
Tactic call pose build and refine ran for 0.069 secs (0.061u,0.008s) (success)

Finished transaction in 0.069 secs (0.061u,0.008s) (successful)
Evars: 412 -> 0

Finished transaction in 0.058 secs (0.058u,0.s) (successful)
Finished transaction in 0.011 secs (0.011u,0.s) (successful) *)
Goal forall x, (f^1000) x = (g^1000) x. Time fast_rewrite. Time Optimize Proof. Time Qed.
(* Tactic call refine ran for 0.01 secs (0.01u,0.s) (success)
Tactic call pose build and refine ran for 0.864 secs (0.845u,0.019s) (success)

Finished transaction in 0.867 secs (0.847u,0.019s) (successful)
Evars: 2012 -> 0

Finished transaction in 8.697 secs (8.693u,0.004s) (successful)
Finished transaction in 0.185 secs (0.185u,0.s) (successful) *)

From Coq Require Import ssreflect.
Goal forall x, (f^100) x = (g^100) x. cbv [comp_pow]; intro. Time rewrite !fg. reflexivity. Abort.
(* Finished transaction in 0.114 secs (0.114u,0.s) (successful) *)
Goal forall x, (f^200) x = (g^200) x. cbv [comp_pow]; intro. Time rewrite !fg. reflexivity. Abort.
(* Finished transaction in 0.361 secs (0.357u,0.003s) (successful) *)
Goal forall x, (f^400) x = (g^400) x. cbv [comp_pow]; intro. Time rewrite !fg. reflexivity. Abort.
(* Finished transaction in 1.493 secs (1.481u,0.011s) (successful) *)
