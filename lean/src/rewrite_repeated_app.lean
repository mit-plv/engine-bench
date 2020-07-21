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

@[simp] def goal100 : Σ' P, P = (∀ x, comp_pow f 100 x = comp_pow g 100 x) :=
by { eapply psigma.mk, simp only [comp_pow] }

@[simp] def goal200 : Σ' P, P = (∀ x, comp_pow f 200 x = comp_pow g 200 x) :=
by { eapply psigma.mk, simp only [comp_pow] }

@[simp] def goal300 : Σ' P, P = (∀ x, comp_pow f 300 x = comp_pow g 300 x) :=
by { eapply psigma.mk, simp only [comp_pow] }

@[simp] def goal400 : Σ' P, P = (∀ x, comp_pow f 400 x = comp_pow g 400 x) :=
by { eapply psigma.mk, simp only [comp_pow] }

@[simp] def goal500 : Σ' P, P = (∀ x, comp_pow f 500 x = comp_pow g 500 x) :=
by { eapply psigma.mk, simp only [comp_pow] }

@[simp] def goal600 : Σ' P, P = (∀ x, comp_pow f 600 x = comp_pow g 600 x) :=
by { eapply psigma.mk, simp only [comp_pow] }

@[simp] def goal700 : Σ' P, P = (∀ x, comp_pow f 700 x = comp_pow g 700 x) :=
by { eapply psigma.mk, simp only [comp_pow] }

@[simp] def goal800 : Σ' P, P = (∀ x, comp_pow f 800 x = comp_pow g 800 x) :=
by { eapply psigma.mk, simp only [comp_pow] }

@[simp] def goal900 : Σ' P, P = (∀ x, comp_pow f 900 x = comp_pow g 900 x) :=
by { eapply psigma.mk, simp only [comp_pow] }

@[simp] def goal1000 : Σ' P, P = (∀ x, comp_pow f 1000 x = comp_pow g 1000 x) :=
by { eapply psigma.mk, simp only [comp_pow] }

lemma ex_simp_only_100 : goal100.1 := by { intro x, simp only [fg] }
lemma ex_simp_only_200 : goal200.1 := by { intro x, simp only [fg] }
lemma ex_simp_only_300 : goal300.1 := by { intro x, simp only [fg] }
lemma ex_simp_only_400 : goal400.1 := by { intro x, simp only [fg] }
lemma ex_simp_only_500 : goal500.1 := by { intro x, simp only [fg] }
lemma ex_simp_only_600 : goal600.1 := by { intro x, simp only [fg] }
lemma ex_simp_only_700 : goal700.1 := by { intro x, simp only [fg] }
lemma ex_simp_only_800 : goal800.1 := by { intro x, simp only [fg] }
lemma ex_simp_only_900 : goal900.1 := by { intro x, simp only [fg] }
lemma ex_simp_only_1000 : goal1000.1 := by { intro x, simp only [fg] }

lemma ex_simp_100 : goal100.1 := by { intro x, simp [fg] }
lemma ex_simp_200 : goal200.1 := by { intro x, simp [fg] }
lemma ex_simp_300 : goal300.1 := by { intro x, simp [fg] }
lemma ex_simp_400 : goal400.1 := by { intro x, simp [fg] }
lemma ex_simp_500 : goal500.1 := by { intro x, simp [fg] }
lemma ex_simp_600 : goal600.1 := by { intro x, simp [fg] }
lemma ex_simp_700 : goal700.1 := by { intro x, simp [fg] }
lemma ex_simp_800 : goal800.1 := by { intro x, simp [fg] }
lemma ex_simp_900 : goal900.1 := by { intro x, simp [fg] }
lemma ex_simp_1000 : goal1000.1 := by { intro x, simp [fg] }

lemma ex_norm_num_100 : goal100.1 := by { intro x, norm_num [fg] }
lemma ex_norm_num_200 : goal200.1 := by { intro x, norm_num [fg] }
lemma ex_norm_num_300 : goal300.1 := by { intro x, norm_num [fg] }
lemma ex_norm_num_400 : goal400.1 := by { intro x, norm_num [fg] }
lemma ex_norm_num_500 : goal500.1 := by { intro x, norm_num [fg] }
lemma ex_norm_num_600 : goal600.1 := by { intro x, norm_num [fg] }
lemma ex_norm_num_700 : goal700.1 := by { intro x, norm_num [fg] }
lemma ex_norm_num_800 : goal800.1 := by { intro x, norm_num [fg] }
lemma ex_norm_num_900 : goal900.1 := by { intro x, norm_num [fg] }
lemma ex_norm_num_1000 : goal1000.1 := by { intro x, norm_num [fg] }

lemma ex_repeat_rw_100 : goal100.1 := by { intro x, repeat { rw [fg] } }
lemma ex_repeat_rw_200 : goal200.1 := by { intro x, repeat { rw [fg] } }
--lemma ex_repeat_rw_300 : goal300.1 := by { intro x, repeat { rw [fg] } }
--lemma ex_repeat_rw_400 : goal400.1 := by { intro x, repeat { rw [fg] } }
--lemma ex_repeat_rw_500 : goal500.1 := by { intro x, repeat { rw [fg] } }
--lemma ex_repeat_rw_600 : goal600.1 := by { intro x, repeat { rw [fg] } }
