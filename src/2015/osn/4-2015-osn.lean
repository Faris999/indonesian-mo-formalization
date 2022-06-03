import data.real.basic tactic

namespace OSN2015_P4



-- We represent a function ℝ+ → ℝ+ as a function ℝ → ℝ that takes positive values at positive inputs
def fn_pos (f : ℝ → ℝ) := ∀ x : ℝ, 0 < x -> 0 < f x
def fn_eq (f g : ℝ → ℝ) (c : ℝ) (_ : 0 < c) := ∀ x y : ℝ, 0 < x → 0 < y → f(g x * y + f x) = (y + c) * f x



---- Part a: We generalize, replacing 2015 by an arbitrary positive real number c
lemma lem1_1 : ∀ (f g : ℝ → ℝ) (c : ℝ) (X : 0 < c) (_ : fn_pos f) (_ : fn_pos g),
  fn_eq f g c X → ∀ x y : ℝ, 0 < x → f x < y → f y = f x * (g x)⁻¹ * y + (c - f x * (g x)⁻¹) * f x :=
begin
  intros f g c X h h0 h1 x y h2 h3,
  have h4 := (h0 x h2),
  calc f y = f(g x * ((y - f x) * (g x)⁻¹) + f x) : _
  ... = ((y - f x) * (g x)⁻¹ + c) * f x : _
  ... = f x * (g x)⁻¹ * y + (c - f x * (g x)⁻¹) * f x : by ring,
  { apply congr_arg,
    rw [mul_comm, mul_assoc, (mul_comm _ (g x)), mul_inv_cancel, mul_one, sub_add_cancel],
    apply (ne_of_gt h4), },
  { rwa h1,
    apply real.mul_pos,
    { rwa sub_pos, },
    { rwa inv_pos, }, },
end

lemma lem1_2 : ∀ a b c d : ℝ, (∃ M : ℝ, ∀ y : ℝ, M < y → a * y + b = c * y + d) → a = c ∧ b = d :=
begin
  intros a b c d h,
  cases h with M h,
  have h1 : M < M + 1 := by norm_num,
  have h2 : M < M + 2 := by norm_num,
  have h3 := (h (M + 1) h1),
  have h4 : a = c,
  { calc a = (a * (M + 2) + b) - (a * (M + 1) + b) : by ring
    ... = (c * (M + 2) + d) - (c * (M + 1) + d) : by rw [h3, (h (M + 2) h2)]
    ... = c : by ring, },
  rw [h4, add_right_inj] at h3,
  split; assumption,
end

lemma lem1_3 : ∀ (f g : ℝ → ℝ) (c : ℝ) (X : 0 < c), fn_pos f → fn_pos g → fn_eq f g c X →
  ∃ m1 m2 : ℝ, ∀ a : ℝ, 0 < a → f a * (g a)⁻¹ = m1 ∧ (c - m1) * f a = m2 :=
begin
  intros f g c X h h0 h1,
  suffices : (∃ m1 m2 : ℝ, ∀ a : ℝ, 0 < a → f a * (g a)⁻¹ = m1 ∧ (c - f a * (g a)⁻¹) * f a = m2),
  { cases this with m1 this,
    cases this with m2 this,
    use [m1, m2],
    intros a h2,
    split,
    exact and.left (this a h2),
    rwa ← and.left (this a h2),
    exact and.right (this a h2), },
  use [f 1 * (g 1)⁻¹, (c - f 1 * (g 1)⁻¹) * f 1],
  intros a h2,
  apply lem1_2; use [max (f 1) (f a)],
  intros y h3,
  rw [←lem1_1 f g c X h h0 h1 1 y zero_lt_one, ←lem1_1 f g c X h h0 h1 a y h2],
  all_goals {apply lt_of_le_of_lt _ h3},
  exact le_max_right (f 1) (f a),
  exact le_max_left (f 1) (f a),
end

theorem osn2015_4a : ∀ (f g : ℝ → ℝ) (c : ℝ) (X : 0 < c), fn_pos f → fn_pos g → fn_eq f g c X →
  ∀ x : ℝ, 0 < x → f x = c * g x :=
begin
  intros f g c X h h0 h1,
  cases (lem1_3 f g c X h h0 h1) with m1 h2; cases h2 with m2 h2,

  suffices : (m1 = c),
  { intros x h3,
    rw [← this, ← and.left (h2 x h3), mul_assoc, inv_mul_cancel, mul_one],
    apply ne_of_gt,
    exact (h0 x h3), },

  suffices : (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ f a ≠ f b),
  { cases this with a this; cases this with b this,
    have h3 := and.right (h2 a (and.left this)),
    rw [← and.right (h2 b (and.left (and.right this))), ← sub_eq_zero, ← mul_sub] at h3,
    rw [mul_eq_zero, sub_eq_zero, sub_eq_zero] at h3,
    cases h3,
    { rw h3, },
    { have h4 := and.right (and.right this),
      contradiction, }, },

  use [g 1 * 1 + f 1, g 1 * 2 + f 1],
  repeat {split},
  -- For the two inequalities
  any_goals {
    apply add_pos,
    apply mul_pos,
    apply h0,
    any_goals { apply h, },
    all_goals { norm_num, },
  },

  rw [h1, h1],
  norm_num,
  apply ne_of_gt,
  apply h,
  all_goals { norm_num, },
end



---- Part b: to implement the solution, we need to provide a proof that 0 < 2015
---- Also note that in this solution, f and g are defined on ℝ, not just on ℝ+
lemma zero_lt_2015 : 0 < (2015 : ℝ) :=
begin
  by norm_num,
end

theorem osn2015_4b : fn_eq (λ x, 2015 * max x 1) (λ x, max x 1) 2015 zero_lt_2015 :=
begin
  intros x y h h0,
  simp,
  rw [mul_comm (y + 2015), mul_assoc, mul_comm 2015 (max x 1), ← mul_add],
  apply congr_arg,
  apply max_eq_left,
  have h1 : 1 ≤ max x 1 * 1 := by rw mul_one; apply le_max_right,
  apply le_trans h1,
  rw mul_le_mul_left,
  { apply le_of_lt,
    apply lt_trans _ (lt_add_of_pos_left 2015 h0),
    norm_num, },
  { rw mul_one at h1,
    exact lt_of_lt_of_le zero_lt_one h1, },
end



end OSN2015_P4 
