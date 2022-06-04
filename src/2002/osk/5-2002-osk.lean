import algebra.big_operators.basic
import algebra.big_operators.nat_antidiagonal
import algebra.big_operators.ring
import data.finset.nat_antidiagonal
import data.real.basic
import tactic

namespace OSK2002_5

open_locale big_operators

-- Lemma by Eric Wieser from the Xena Project Discord
lemma pow_sub_pow {R} [ring R] {a b : R} (h : commute a b) {n : ℕ} :
  a^n.succ - b^n.succ = (a - b) * ∑ x in finset.nat.antidiagonal n, a^x.1 * b^x.2 :=
begin
  rw [sub_mul, sub_eq_sub_iff_add_eq_add, finset.mul_sum, finset.mul_sum],
  simp_rw [(h.symm.pow_right _).left_comm, ←mul_assoc a, ←pow_succ],
  transitivity ∑ x in finset.nat.antidiagonal n.succ, a^x.1 * b^x.2,
  { rw [finset.nat.sum_antidiagonal_succ', pow_zero, mul_one], },
  { rw [finset.nat.sum_antidiagonal_succ, pow_zero, one_mul, add_comm] },
end

lemma cube_sub_cube {a b : ℝ} : a^3 - b^3 = (a - b) * (a^2 + a * b + b^2) := by ring

-- Added hypothesis that a ≠ 0 that's missing from the original statement 
theorem osk2002_5 {a : ℝ} (h : a ≠ 0) : a^3 - a^(-3 : ℤ) = (a - (1 / a)) * (a^2 + 1 + (1 / a^2)) :=
begin
  rw zpow_neg,
  rw ← inv_zpow,
  rw inv_eq_one_div,
  norm_cast,
  rw ← one_div_pow,
  have h1 : 1 = a * (1 / a),
  { rw mul_one_div,
    rw div_self,
    exact h,},
  nth_rewrite_rhs 1 h1,
  rw cube_sub_cube,
end

end OSK2002_5