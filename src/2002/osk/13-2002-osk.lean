import data.nat.basic
import data.nat.digits

@[simp]
def digits_sum (n : ℕ) : ℕ := (nat.digits 10 n).sum

lemma digits_sum_ten_pow_mul {a n : ℕ} :
  digits_sum (10^a * n) = digits_sum n := sorry

theorem osk2002_13 : digits_sum (2^(2002) * 5^(2003)) = 5 :=
begin
  have h : 2^(2002) * 5^(2003) = 10^(2002) * 5,
  { calc 2^(2002) * 5^(2003) = 2^(2002) * 5^(2002 + 1) : _ 
    ... = 2^(2002) * (5^(2002) * 5^1) : _
    ... = 2^(2002) * 5^(2002) * 5 : _
    ... = 10^(2002) * 5 : _,
    { simp,
      apply congr_arg,
      norm_num, },
    { rw pow_add, },
    { rw mul_assoc,
      simp,},
    { rw ← mul_pow,
      simp,
      norm_num, }},
  calc digits_sum (2^(2002) * 5^(2003)) = digits_sum(10^(2002) * 5) : by rw h
  ... = digits_sum(5) : by rw digits_sum_ten_pow_mul
  ... = 5 : by simp,
end