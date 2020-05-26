Require Import Coq.Lists.List.
Require Import PerformanceExperiments.Harness.
(** https://github.com/coq/coq/issues/11151 *)

Inductive type := NAT | LIST (t : type) | ARROW (A B : type).
Fixpoint interpt (t : type) : Set
  := match t with
     | NAT => nat
     | LIST t => list (interpt t)
     | ARROW A B => interpt A -> interpt B
     end.
Inductive expr {var : type -> Type} {ident : type -> Type} : type -> Type :=
| LetIn {A B} : expr A -> (var A -> expr B) -> expr B
| App {A B} : expr (ARROW A B) -> expr A -> expr B
| Ident {A} : ident A -> expr A
| Var {A} : var A -> expr A.
Inductive ident : type -> Type :=
| ident_literal : nat -> ident NAT
| ident_cons : ident (ARROW NAT (ARROW (LIST NAT) (LIST NAT)))
| ident_nil : ident (LIST NAT)
| ident_f : ident (ARROW NAT (ARROW NAT NAT)).
Axiom Let_In : forall {A B : Set}, A -> (A -> B) -> B.
Axiom f : nat -> nat -> nat.
Fixpoint interp (ident_interp : forall t, ident t -> interpt t) {T} (v : expr T) : interpt T
  := match v with
     | LetIn v f => Let_In (interp ident_interp v) (fun v => interp ident_interp (f v))
     | App f x => interp ident_interp f (interp ident_interp x)
     | Var v => v
     | Ident idc => ident_interp _ idc
     end.
Definition ident_interp {t} (idc : ident t) : interpt t
  := match idc with
     | ident_literal x => x
     | ident_cons => fun x xs => cons x xs
     | ident_nil => nil
     | ident_f => fun x y => f x y
     end.

Definition map_double_cps {T} {var} (ls : list (expr (ident:=ident) (var:=var) NAT)) (k : list (expr (ident:=ident) (var:=var) NAT) -> expr (ident:=ident) (var:=var) T) :=
  list_rect
    (fun _ => (list (expr (var:=var) NAT) -> expr T) -> _)
    (fun k => k nil)
    (fun x xs rec k
     => LetIn (App (App (Ident ident_f) x) x)
              (fun y =>
                 rec (fun ys => k (cons (Var y) ys))))
    ls
    k.

Definition make_cps {var} {T} (n : nat) (m : nat) (v : expr (var:=var)(ident:=ident) NAT) (k : list (expr (var:=var) NAT) -> expr T)
  := nat_rect
       _
       (fun k => k (List.repeat v n))
       (fun _ rec k => rec (fun ls => map_double_cps ls k))
       m
       k.
Fixpoint reify_list {var} (ls : list (expr (var:=var) NAT)) : expr (var:=var) (LIST NAT)
  := match ls with
     | nil => Ident ident_nil
     | cons x xs => App (App (Ident ident_cons) x) (reify_list xs)
     end.

Local Infix "/" := Nat.div : nat_scope.

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 0 3
     | SuperFast => List.map (fun x => x * 5) (seq 0 (70 / 5))
     | Fast => List.map (fun x => x * 5) (seq 0 (120 / 5))
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Axiom P : forall {T}, T -> Prop.

Ltac mkgoal n := constr:(P (fun x var => make_cps (T:=LIST NAT) (var:=var) n n (Ident (ident_literal x)) (@reify_list var))).
Ltac describe_goal n :=
  let n2 := (eval cbv in (n * n)) in
  idtac "Params: a-num-binders=" n2 ", n=" n.
Ltac redgoal _ := vm_compute.
Ltac get_term _ :=
  let preterm := lazymatch goal with |- P ?preterm => preterm end in
  let term := constr:(fun x => interp (@ident_interp) (preterm x _)) in
  term.
Ltac time_solve_goal0 n :=
  let term := get_term () in
  try (once (time "cbv" (idtac; let res := (eval cbv in term) in idtac)); fail);
  try (once (time "lazy" (idtac; let res := (eval cbv in term) in idtac)); fail).
Ltac run0 sz := Harness.runtests args_of_size describe_goal mkgoal redgoal time_solve_goal0 sz.
(*
Goal True. run0 SuperFast.
*)
