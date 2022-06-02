import data.real.basic

theorem osk2002_4 {x : ℝ} : x < 0 → x < x^2 :=
begin
  intros h,
  transitivity,
  exact h,
  apply sq_pos_of_ne_zero,
  apply ne_of_lt h,
end