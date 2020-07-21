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

@[simp] def goal100 : Σ' P, P = goal 100 :=
by { eapply psigma.mk, simp only [make_lets_def] }

@[simp] def goal200 : Σ' P, P = goal 200 :=
by { eapply psigma.mk, simp only [make_lets_def] }

@[simp] def goal300 : Σ' P, P = goal 300 :=
by { eapply psigma.mk, simp only [make_lets_def] }

@[simp] def goal400 : Σ' P, P = goal 400 :=
by { eapply psigma.mk, simp only [make_lets_def] }

@[simp] def goal500 : Σ' P, P = goal 500 :=
by { eapply psigma.mk, simp only [make_lets_def] }

@[simp] def goal600 : Σ' P, P = goal 600 :=
by { eapply psigma.mk, simp only [make_lets_def] }

@[simp] def goal700 : Σ' P, P = goal 700 :=
by { eapply psigma.mk, simp only [make_lets_def] }

@[simp] def goal800 : Σ' P, P = goal 800 :=
by { eapply psigma.mk, simp only [make_lets_def] }

@[simp] def goal900 : Σ' P, P = goal 900 :=
by { eapply psigma.mk, simp only [make_lets_def] }

@[simp] def goal1000 : Σ' P, P = goal 1000 :=
by { eapply psigma.mk, simp only [make_lets_def] }

lemma ex_simp_only_100 : goal100.1 := by { intro x, simp only [rev_plus_n_O], apply fin_ax }
lemma ex_simp_only_200 : goal200.1 := by { intro x, simp only [rev_plus_n_O], apply fin_ax }
lemma ex_simp_only_300 : goal300.1 := by { intro x, simp only [rev_plus_n_O], apply fin_ax }
lemma ex_simp_only_400 : goal400.1 := by { intro x, simp only [rev_plus_n_O], apply fin_ax }
lemma ex_simp_only_500 : goal500.1 := by { intro x, simp only [rev_plus_n_O], apply fin_ax }
lemma ex_simp_only_600 : goal600.1 := by { intro x, simp only [rev_plus_n_O], apply fin_ax }
lemma ex_simp_only_700 : goal700.1 := by { intro x, simp only [rev_plus_n_O], apply fin_ax }
lemma ex_simp_only_800 : goal800.1 := by { intro x, simp only [rev_plus_n_O], apply fin_ax }
lemma ex_simp_only_900 : goal900.1 := by { intro x, simp only [rev_plus_n_O], apply fin_ax }
lemma ex_simp_only_1000 : goal1000.1 := by { intro x, simp only [rev_plus_n_O], apply fin_ax }

lemma ex_simp_100 : goal100.1 := by { intro x, simp [rev_plus_n_O], apply fin_ax }
lemma ex_simp_200 : goal200.1 := by { intro x, simp [rev_plus_n_O], apply fin_ax }
lemma ex_simp_300 : goal300.1 := by { intro x, simp [rev_plus_n_O], apply fin_ax }
lemma ex_simp_400 : goal400.1 := by { intro x, simp [rev_plus_n_O], apply fin_ax }
lemma ex_simp_500 : goal500.1 := by { intro x, simp [rev_plus_n_O], apply fin_ax }
lemma ex_simp_600 : goal600.1 := by { intro x, simp [rev_plus_n_O], apply fin_ax }
lemma ex_simp_700 : goal700.1 := by { intro x, simp [rev_plus_n_O], apply fin_ax }
lemma ex_simp_800 : goal800.1 := by { intro x, simp [rev_plus_n_O], apply fin_ax }
lemma ex_simp_900 : goal900.1 := by { intro x, simp [rev_plus_n_O], apply fin_ax }
lemma ex_simp_1000 : goal1000.1 := by { intro x, simp [rev_plus_n_O], apply fin_ax }

lemma ex_norm_num_100 : goal100.1 := by { intro x, norm_num [rev_plus_n_O], apply fin_ax }
lemma ex_norm_num_200 : goal200.1 := by { intro x, norm_num [rev_plus_n_O], apply fin_ax }
lemma ex_norm_num_300 : goal300.1 := by { intro x, norm_num [rev_plus_n_O], apply fin_ax }
lemma ex_norm_num_400 : goal400.1 := by { intro x, norm_num [rev_plus_n_O], apply fin_ax }
lemma ex_norm_num_500 : goal500.1 := by { intro x, norm_num [rev_plus_n_O], apply fin_ax }
lemma ex_norm_num_600 : goal600.1 := by { intro x, norm_num [rev_plus_n_O], apply fin_ax }
lemma ex_norm_num_700 : goal700.1 := by { intro x, norm_num [rev_plus_n_O], apply fin_ax }
lemma ex_norm_num_800 : goal800.1 := by { intro x, norm_num [rev_plus_n_O], apply fin_ax }
lemma ex_norm_num_900 : goal900.1 := by { intro x, norm_num [rev_plus_n_O], apply fin_ax }
lemma ex_norm_num_1000 : goal1000.1 := by { intro x, norm_num [rev_plus_n_O], apply fin_ax }
