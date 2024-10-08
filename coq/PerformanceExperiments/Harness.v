From Coq Require Import Orders.
From Coq Require Import Lia.
From Coq Require Import Bool.
From Coq Require Import Mergesort.
From Coq Require Export List.
From Coq Require Export ZArith.
Export ListNotations.

Global Set Printing Width 1000.
Global Open Scope Z_scope.
Global Open Scope nat_scope.
Global Open Scope list_scope.

(** divisions should be roughly:
- The [Sanity] tests should be just enough to ensure that the code compiles and runs.
- All [SuperFast] tests in a file should finish in under 10 seconds total
- The [Fast] test files should take about a minute each
- The [Medium] tests should go up to about a minute each
- The [Slow] tests should go up to about 10 minutes each
- The [VerySlow] tests may take longer than 10 minutes each *)

Inductive size := Sanity | SuperFast | Fast | Medium | Slow | VerySlow.

Definition nat_of_size (sz : size) : nat
  := match sz with
     | Sanity => 0
     | SuperFast => 1
     | Fast => 2
     | Medium => 3
     | Slow => 4
     | VerySlow => 5
     end%nat.

Definition smaller_sizes (sz : size) : list size
  := match sz with
     | Sanity => []
     | SuperFast => [Sanity]
     | Fast => [Sanity; SuperFast]
     | Medium => [Sanity; SuperFast; Fast]
     | Slow => [Sanity; SuperFast; Fast; Medium]
     | VerySlow => [Sanity; SuperFast; Fast; Medium; Slow]
     end.

Definition size_pred (sz : size) : option size
  := match sz with
     | Sanity => None
     | SuperFast => Some Sanity
     | Fast => Some SuperFast
     | Medium => Some Fast
     | Slow => Some Medium
     | VerySlow => Some Slow
     end.

Fixpoint uniquify {T} (T_beq : T -> T -> bool) (ls : list T) : list T
  := match ls with
     | nil => nil
     | cons x xs
       => x :: filter (fun y => negb (T_beq x y)) (uniquify T_beq xs)
     end.

Definition remove_smaller_args_of_size {T} (T_beq : T -> T -> bool) (sz : size)
           (args_of_size : size -> list T)
  : list T
  := let args := uniquify T_beq (args_of_size sz) in
     let smaller_args := flat_map args_of_size (smaller_sizes sz) in
     filter (fun v => negb (existsb (T_beq v) smaller_args)) args.

Module NatProdOrder <: TotalLeBool.
  Definition t := (nat * nat)%type.
  Definition t_to_Z (v : t) : Z := (Z.of_nat (fst v) * Z.of_nat (snd v))%Z.
  Definition ltb (x y : t) : bool
    := (t_to_Z x <? t_to_Z y)%Z
       || (((t_to_Z x =? t_to_Z y)%Z)
             && ((fst x <? fst y)
                 || ((fst x =? fst y) && (snd x <? snd y)))).
  Definition leb (x y : t) : bool
    := ltb x y || ((fst x =? fst y) && (snd x =? snd y)).
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    cbv [leb ltb]; intros a1 a2.
    repeat first [ rewrite !Bool.andb_true_iff
                 | rewrite !Bool.orb_true_iff
                 | rewrite !Nat.eqb_eq
                 | rewrite !Z.eqb_eq
                 | rewrite !Z.ltb_lt
                 | rewrite !Nat.ltb_lt ].
    destruct (Z.lt_total (t_to_Z a1) (t_to_Z a2)) as [?|[?|?]];
      try solve [ auto ]; [].
    destruct (Nat.lt_total (fst a1) (fst a2)) as [?|[?|?]];
      try solve [ auto 6 ]; [].
    destruct (Nat.lt_total (snd a1) (snd a2)) as [?|[?|?]];
      solve [ auto 7 ].
  Qed.
End NatProdOrder.

Module NatProdSort := Sort NatProdOrder.
Notation sort_by_prod := NatProdSort.sort.

Module NatFstOrder <: TotalLeBool.
  Definition t := (nat * nat)%type.
  Definition ltb (x y : t) : bool
    := (fst x <? fst y)
       || ((fst x =? fst y)
             && (snd x <? snd y)).
  Definition leb (x y : t) : bool
    := ltb x y || ((fst x =? fst y) && (snd x =? snd y)).
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    cbv [leb ltb]; intros a1 a2.
    repeat first [ rewrite !Bool.andb_true_iff
                 | rewrite !Bool.orb_true_iff
                 | rewrite !Nat.eqb_eq
                 | rewrite !Nat.ltb_lt ].
    destruct (Nat.lt_total (fst a1) (fst a2)) as [?|[?|?]];
      try solve [ auto 6 ]; [].
    destruct (Nat.lt_total (snd a1) (snd a2)) as [?|[?|?]];
      solve [ auto 7 ].
  Qed.
End NatFstOrder.

Module NatFstSort := Sort NatFstOrder.
Notation sort_by_fst := NatFstSort.sort.

Module ZProdOrder <: TotalLeBool.
  Local Open Scope Z_scope.
  Definition t := (Z * Z)%type.
  Definition t_to_Z (v : t) : Z := (fst v * snd v)%Z.
  Definition ltb (x y : t) : bool
    := (t_to_Z x <? t_to_Z y)%Z
       || (((t_to_Z x =? t_to_Z y)%Z)
             && ((fst x <? fst y)
                 || ((fst x =? fst y) && (snd x <? snd y)))).
  Definition leb (x y : t) : bool
    := ltb x y || ((fst x =? fst y) && (snd x =? snd y)).
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    cbv [leb ltb]; intros a1 a2.
    repeat first [ rewrite !Bool.andb_true_iff
                 | rewrite !Bool.orb_true_iff
                 | rewrite !Z.eqb_eq
                 | rewrite !Z.ltb_lt
                 | rewrite !Z.ltb_lt ].
    destruct (Z.lt_total (t_to_Z a1) (t_to_Z a2)) as [?|[?|?]];
      try solve [ auto ]; [].
    destruct (Z.lt_total (fst a1) (fst a2)) as [?|[?|?]];
      try solve [ auto 6 ]; [].
    destruct (Z.lt_total (snd a1) (snd a2)) as [?|[?|?]];
      solve [ auto 7 ].
  Qed.
End ZProdOrder.

Module ZProdSort := Sort ZProdOrder.
Notation Zsort_by_prod := ZProdSort.sort.

Module ZFstOrder <: TotalLeBool.
  Local Open Scope Z_scope.
  Definition t := (Z * Z)%type.
  Definition ltb (x y : t) : bool
    := (fst x <? fst y)
       || ((fst x =? fst y)
             && (snd x <? snd y)).
  Definition leb (x y : t) : bool
    := ltb x y || ((fst x =? fst y) && (snd x =? snd y)).
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    cbv [leb ltb]; intros a1 a2.
    repeat first [ rewrite !Bool.andb_true_iff
                 | rewrite !Bool.orb_true_iff
                 | rewrite !Z.eqb_eq
                 | rewrite !Z.ltb_lt ].
    destruct (Z.lt_total (fst a1) (fst a2)) as [?|[?|?]];
      try solve [ auto 6 ]; [].
    destruct (Z.lt_total (snd a1) (snd a2)) as [?|[?|?]];
      solve [ auto 7 ].
  Qed.
End ZFstOrder.

Module ZFstSort := Sort ZFstOrder.
Notation Zsort_by_fst := ZFstSort.sort.


Module ZOrder <: TotalLeBool.
  Local Open Scope Z_scope.
  Definition t := Z.
  Definition ltb := Z.ltb.
  Definition leb := Z.leb.
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    cbv [leb ltb]; intros a1 a2.
    repeat first [ rewrite !Bool.andb_true_iff
                 | rewrite !Bool.orb_true_iff
                 | rewrite !Z.eqb_eq
                 | rewrite !Z.ltb_lt
                 | rewrite !Z.leb_le ].
    lia.
  Qed.
End ZOrder.

Module ZSort := Sort ZOrder.

Existing Class reflect.
Notation reflect_rel R1 R2 := (forall x y, reflect (R1 x y) (R2 x y)).

Lemma reflect_of_beq {beq : bool} {R : Prop}
      (bp : beq = true -> R)
      (pb : R -> beq = true)
  : reflect R beq.
Proof.
  destruct beq; constructor; intuition (discriminate || auto).
Qed.

Definition reflect_rel_of_beq {T} {beq : T -> T -> bool} {R : T -> T -> Prop}
      (bp : forall x y, beq x y = true -> R x y)
      (pb : forall x y, R x y -> beq x y = true)
  : reflect_rel R beq
  := fun x y => reflect_of_beq (bp x y) (pb x y).

Definition reflect_rel_of_beq_iff {T} {beq : T -> T -> bool} {R : T -> T -> Prop}
      (bp : forall x y, beq x y = true <-> R x y)
  : reflect_rel R beq
  := reflect_rel_of_beq (fun x y => proj1 (bp x y)) (fun x y => proj2 (bp x y)).

Global Instance reflect_eq_nat : reflect_rel (@eq nat) Nat.eqb
  := reflect_rel_of_beq_iff Nat.eqb_eq.

Global Instance reflect_eq_Z : reflect_rel (@eq Z) Z.eqb
  := reflect_rel_of_beq_iff Z.eqb_eq.

Class has_sub T := sub : T -> T -> T.
Global Instance: has_sub nat := Nat.sub.
Global Instance: has_sub Z := Z.sub.

Class has_succ T := succ : T -> T.
Global Instance: has_succ nat := S.
Global Instance: has_succ Z := Z.succ.

Class has_zero T := zero : T.
Global Instance: has_zero nat := O.
Global Instance: has_zero Z := Z0.

Class has_sort T := sort : list T -> list T.
Global Instance: has_sort nat := NatSort.sort.
Global Instance: has_sort Z := ZSort.sort.

Definition remove_smaller_args_of_size_by_reflect
           {T} {T_beq : T -> T -> bool}
           {T_reflect : reflect_rel (@eq T) T_beq}
           (sz : size)
           (args_of_size : size -> list T)
  : list T
  := let args := uniquify T_beq (args_of_size sz) in
     let smaller_args := flat_map args_of_size (smaller_sizes sz) in
     filter (fun v => negb (existsb (T_beq v) smaller_args)) args.

Ltac default_describe_goal x :=
  idtac "Params: n=" x.

Ltac runtests args_of_size describe_goal mkgoal redgoal time_solve_goal sz :=
  let args := (eval vm_compute in (remove_smaller_args_of_size_by_reflect sz args_of_size)) in
  let rec iter ls :=
      lazymatch ls with
      | [] => idtac
      | ?x :: ?xs
        => describe_goal x;
           let T := mkgoal x in
           try (solve [ assert T by (redgoal x; once (time_solve_goal x + fail 2 "time_solve_goal failed!")) ]; []);
           iter xs
      end in
  iter args.

Ltac step_goal_from_to_constr step_goal cur_n target_n G :=
  let test := match constr:(Set) with
              | _ => let __ := match constr:(Set) with _ => constr_eq cur_n target_n end in
                     true
              | _ => false
              end in
  lazymatch test with
  | true => G
  | false
    => let next_n := (eval cbv in (succ cur_n)) in
       let G := step_goal next_n G in
       step_goal_from_to_constr step_goal next_n target_n G
  end.

Ltac runtests_step_arg_constr args_of_size describe_goal step_goal redgoal_constr redgoal time_solve_goal sz G extra_args :=
  let args := (eval vm_compute in (remove_smaller_args_of_size_by_reflect sz args_of_size)) in
  let T := lazymatch type of args with list ?T => T end in
  let rec iter cur ls G :=
      lazymatch ls with
      | [] => idtac
      | ?x :: ?xs
        => let G := step_goal_from_to_constr step_goal cur x G in
           let G := redgoal_constr x G in
           describe_goal x;
           try (solve [ redgoal x; once (time_solve_goal x G extra_args + fail 2 "time_solve_goal failed!") ]; []);
           iter x xs G
      end in
  let zero := (eval cbv in (@zero T _)) in
  iter zero args G.

Ltac runtests_step_constr args_of_size describe_goal step_goal redgoal_constr time_solve_goal sz G :=
  runtests_step_arg_constr args_of_size describe_goal step_goal redgoal_constr ltac:(fun _ => idtac) ltac:(fun n G args => time_solve_goal n G) sz G ().

Ltac constr_run_tac f x :=
  lazymatch goal with
  | _ => f x
  end.

Ltac runtests_step args_of_size describe_goal step_goal redgoal time_solve_goal sz :=
  runtests_step_arg_constr args_of_size describe_goal ltac:(fun n G => constr_run_tac step_goal n) ltac:(fun _ G => G) redgoal ltac:(fun n G args => time_solve_goal n) sz () ().
