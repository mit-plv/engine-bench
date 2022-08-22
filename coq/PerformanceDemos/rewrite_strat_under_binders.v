(** * performance of rewrite/rewrite_strat under binders *)
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x := let y := x in f y.
Strategy 100 [Let_In].
Global Hint Opaque Let_In : rewrite.
Reserved Notation "'dlet_nd' x .. y := v 'in' f"
         (at level 200, x binder, y binder, f at level 200, format "'dlet_nd'  x .. y  :=  v  'in' '//' f").
Reserved Notation "'dlet' x .. y := v 'in' f"
         (at level 200, x binder, y binder, f at level 200, format "'dlet'  x .. y  :=  v  'in' '//' f").
Notation "'dlet_nd' x .. y := v 'in' f" := (Let_In (P:=fun _ => _) v (fun x => .. (fun y => f) .. )) (only parsing).
Notation "'dlet' x .. y := v 'in' f" := (Let_In v (fun x => .. (fun y => f) .. )).
Global Instance Let_In_nd_Proper {A P}
  : Proper (eq ==> pointwise_relation _ eq ==> eq) (@Let_In A (fun _ => P)).
Proof. cbv; intros; subst; auto. Qed.
Global Hint Extern 0 (Proper _ (@Let_In _ _)) => simple apply @Let_In_nd_Proper : typeclass_instances.
Global Instance eq_eq_eq {A}
  : Proper (eq ==> eq ==> eq) (@eq A).
Proof. repeat intro; subst; reflexivity. Qed.
Global Instance all_Proper {A} (* Why do we need this??? *)
  : Proper (pointwise_relation _ eq ==> Basics.flip Basics.impl) (@all A).
Proof. intros f g H Hg x; specialize (H x); specialize (Hg x); congruence. Qed.

Fixpoint make_lets_def (n : nat) (v : nat) (acc : nat) {struct n} :=
  match n with
  | 0 => acc + acc + v
  | S n => dlet acc := acc + acc + v in make_lets_def n v acc
  end.

Notation goal n := (forall acc, make_lets_def n 0 acc = acc) (only parsing).

Goal goal 50. cbv [make_lets_def]. Time repeat setoid_rewrite <- plus_n_O. Abort.
(* Finished transaction in 0.249 secs (0.249u,0.s) (successful) *)
Goal goal 100. cbv [make_lets_def]. Time repeat setoid_rewrite <- plus_n_O. Abort.
(* Finished transaction in 1.455 secs (1.455u,0.s) (successful) *)
Goal goal 200. cbv [make_lets_def]. Time repeat setoid_rewrite <- plus_n_O. Abort.
(* Finished transaction in 9.922 secs (9.922u,0.s) (successful) *)

Goal goal 10. cbv [make_lets_def]. Time repeat rewrite_strat topdown <- plus_n_O. Abort.
(* Finished transaction in 0.083 secs (0.083u,0.s) (successful) *)
Goal goal 20. cbv [make_lets_def]. Time repeat rewrite_strat topdown <- plus_n_O. Abort.
(* Finished transaction in 0.392 secs (0.392u,0.s) (successful) *)
Goal goal 40. cbv [make_lets_def]. Time repeat rewrite_strat topdown <- plus_n_O. Abort.
(* Finished transaction in 3.241 secs (3.241u,0.s) (successful) *)

Goal goal 10. cbv [make_lets_def]. Time repeat rewrite_strat bottomup <- plus_n_O. Abort.
(* Finished transaction in 0.085 secs (0.082u,0.002s) (successful) *)
Goal goal 20. cbv [make_lets_def]. Time repeat rewrite_strat bottomup <- plus_n_O. Abort.
(* Finished transaction in 0.395 secs (0.391u,0.003s) (successful) *)
Goal goal 40. cbv [make_lets_def]. Time repeat rewrite_strat bottomup <- plus_n_O. Abort.
(* Finished transaction in 3.261 secs (3.261u,0.s) (successful) *)
