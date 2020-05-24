(* -*- coq-prog-args: ("-debug") -*- *)
(** * Full reduction on a function of complexity O(f) should be Õ(f + input term size + output term size) *)
Require Import Coq.Lists.List.
(** Copied from COQBUG(https://github.com/coq/coq/issues/11964) *)
Module Red.
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

Ltac do_up_to tac n :=
  lazymatch n with
  | O => idtac n; tac 0 0
  | S (S (S (S (S ?n')))) => do_up_to tac n'; idtac n; tac n n
  | S ?n' => do_up_to tac n'; idtac n; tac n n
  end.
Ltac mk n m :=
  let preterm := (eval vm_compute in (fun x var => make_cps (T:=LIST NAT) (var:=var) n m (Ident (ident_literal x)) (@reify_list var))) in
  let term := constr:(fun x => interp (@ident_interp) (preterm x _)) in
  term.
Ltac do_time_cbv n m:=
  let term := mk n m in
  try (once (time "cbv" (idtac; let res := (eval cbv in term) in idtac)); fail).
Ltac do_time_lazy n m:=
  let term := mk n m in
  try (once (time "lazy" (idtac; let res := (eval lazy in term) in idtac)); fail).
Ltac do_time_vm_compute n m:=
  let term := mk n m in
  try (once (time "vm_compute" (idtac; let res := (eval vm_compute in term) in idtac)); fail).
Ltac do_time_native_compute n m:=
  let term := mk n m in
  try (once (time "native_compute" (idtac; let res := (eval native_compute in term) in idtac)); fail).
Goal True.
  do_up_to do_time_vm_compute 120.
  do_up_to do_time_cbv 75.
  do_up_to do_time_lazy 75.
Abort.
End Red.


(** Copied from COQBUG(https://github.com/coq/coq/issues/11964) *)
Module Native.
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

Ltac do_up_to tac n :=
  lazymatch n with
  | O => idtac n; tac 0 0
  | S (S (S (S (S ?n')))) => do_up_to tac n'; idtac n; tac n n
  | S ?n' => do_up_to tac n'; idtac n; tac n n
  end.
Ltac mk n m :=
  let preterm := (eval vm_compute in (fun x var => make_cps (T:=LIST NAT) (var:=var) n m (Ident (ident_literal x)) (@reify_list var))) in
  let term := constr:(fun x => interp (@ident_interp) (preterm x _)) in
  term.
Ltac do_time_native_compute n m:=
  let term := mk n m in
  try (once (time "native_compute" (idtac; let res := (eval native_compute in term) in idtac)); fail).
Set NativeCompute Timing.
Goal True.
  (* stack overflows occur starting at 65 *)
  do_up_to do_time_native_compute 40.
Abort.
End Native.
