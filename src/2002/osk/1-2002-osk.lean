import data.nat.basic
import algebra.group_power.basic
import tactic

-- ℚ LHS suggestion by Eric Wieser on the Xena Project Discord
theorem osk2002_1 : (((2^4)^8) / ((4^8)^2) : ℚ) = 1 :=
begin
  norm_num, -- suggestion by Marco Dos Santos on the Xena Project Discord
end

lemma four_eq_two_pow_two : (4: ℕ) = (2^2 : ℕ) := rfl

-- l1, l2, l3 helper lemmas
-- credit: Kevin Buzzard on the Xena Project Discord
lemma l1 : ((2^4)^8) = ((4^8)^2) :=
begin
  nth_rewrite 2 four_eq_two_pow_two, -- now always raising powers of 2 to powers
  simp only [← pow_mul],
  -- goal is now 2^X = 2^Y
  apply congr_arg, -- goal is now X=Y
  norm_num, -- would have worked earlier but arguably not in spirit of problem
end

lemma l2 (a b : ℕ) (h : (a / b : ℚ) = 1) : a = b :=
begin
  rw div_eq_one_iff_eq at h,
  { assumption_mod_cast, },
  { intro hb,
    rw hb at h,
    simpa using h,
  },
end

lemma l3 {a b : ℕ} (h : a = b) (hb : b ≠ 0) : (a / b : ℚ) = 1 :=
begin
  rw h,
  rw div_eq_one_iff_eq,
  assumption_mod_cast,
end

theorem osk2002_1_alt : (((2^4)^8) / ((4^8)^2) : ℚ) = 1 :=
begin
  have h : (4^8)^2 ≠ 0,
  { norm_num, },
  -- recursion error
  -- exact l3 l1 h,
  sorry,
end

