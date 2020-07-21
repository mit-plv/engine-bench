import tactic.norm_num
import algebra.group_power
open prod
universes u v w ℓ

def let_in {A : Type u} {B : Type v} (x : A) (f : A → B) := f x

local notation `dlet` binders ` ≔ ` b ` in ` c:(scoped P, P) := let_in b c

set_option pp.max_depth 1000000000

axiom f : ℕ → ℕ
axiom g : ℕ → ℕ
axiom fg : ∀ (x : ℕ), f x = g x
lemma fg_ext : ∀ x y, x = y → f x = g y :=
begin
  intros x y h, cases h, apply fg
end

@[simp]
def comp_pow {A : Type u} (f : A → A) : ℕ → A → A
| 0 x := x
| (nat.succ n) x := f (comp_pow n x)

@[simp] def goal10 : Σ' P, P = (∀ x, comp_pow f 10 x = comp_pow g 10 x) :=
by { eapply psigma.mk, simp only [comp_pow] }

lemma ex_simp_10 : goal10.1 := by { intro x, simp [fg] }

lemma ex_repeat_rw_10 : goal10.1 := by { intro x, repeat { rw fg } }

lemma ex_norm_num_10 : goal10.1 := by { intro x, norm_num [fg] }
