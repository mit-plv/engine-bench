Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms.
Axiom f : nat -> nat.
Axiom g : nat -> nat.
Axiom fg : forall x, f x = g x.
Lemma fg_ext : forall x y, x = y -> f x = g y.
Proof. intros; subst; apply fg. Qed.

Hint Rewrite fg : rew_fg.

Fixpoint comp_pow {A} (f : A -> A) (n : nat) (x : A) {struct n} : A
  := match n with
     | O => x
     | S n => f (comp_pow f n x)
     end.

Local Infix "^" := comp_pow : core_scope.

Global Instance eq_Proper {A}
  : Proper (eq ==> eq ==> Basics.flip Basics.impl) (@eq A).
Proof. repeat intro; subst; reflexivity. Qed.
Global Instance f_Proper : Proper (eq ==> eq) f.
Proof. repeat intro; subst; reflexivity. Qed.
Global Instance g_Proper : Proper (eq ==> eq) g.
Proof. repeat intro; subst; reflexivity. Qed.

Notation goal n := (forall x, (f^n) x = (g^n) x).
Ltac mkgoal n := constr:(goal n).
Ltac redgoal _ := cbv [comp_pow]; intro.

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
  time "pose build and refine"
    lazymatch goal with
    | [ |- f ?x = g ?y :> ?A ]
      => refine (_ : f x = g y :> A);
         preshare_pf
           f g (f x) (g y) fg_ext
           ltac:(fun x' y' pf
                 => time "refine" refine pf)
    end.
