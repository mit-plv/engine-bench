import tactic.norm_num
import algebra.group_power
open prod
universes u v w ℓ

def let_in {A : Type u} {B : Type v} (x : A) (f : A → B) := f x

local notation `dlet` binders ` ≔ ` b ` in ` c:(scoped P, P) := let_in b c

set_option pp.max_depth 1000000000

axiom zero_ax : ℕ

@[simp]
def make_lets_def : ℕ → ℕ → ℕ → ℕ
| 0            v acc := acc + acc + v
| (nat.succ n) v acc := dlet acc ≔ acc + acc + v in make_lets_def n v acc

axiom rev_plus_n_O : ∀ (n : ℕ), n + zero_ax = n

axiom fin_ax : ∀ x y : ℕ, x = y

local notation `goal` n := ∀ acc, make_lets_def n zero_ax acc = acc

@[simp] def goal10 : Σ' P, P = goal 10 :=
by { eapply psigma.mk, simp only [make_lets_def] }

lemma ex_simp_10 : goal10.1 := by { intro acc, simp [rev_plus_n_O], apply fin_ax }

lemma ex_simp_only_10 : goal10.1 := by { intro acc, simp only [rev_plus_n_O], apply fin_ax }

lemma ex_norm_num_10 : goal10.1 := by { intro x, norm_num [rev_plus_n_O], apply fin_ax }
