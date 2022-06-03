import data.nat.basic
import data.nat.digits

def digits_sum (n : ℕ) : ℕ := (nat.digits 10 n).sum

-- First we prove digits_sum (10n) = digits_sum n
lemma digits_sum_ten_mul {n : ℕ} :
  digits_sum (10 * n) = digits_sum n :=
begin
  have h : 0 = n ∨ 0 < n,
  { apply nat.eq_or_lt_of_le,
    exact nat.zero_le n, },
  destruct h,
  -- Case 1: n = 0
  { intros h0,
    rw ← h0,
    rw nat.mul_zero, },
  -- Case 2: 0 < n
  { intros h0,
    have h : nat.digits 10 (10 * n) = 0 :: nat.digits 10 n,
    { calc nat.digits 10 (10 * n) = nat.digits 10 (0 + 10 * n) : by rw (nat.zero_add (10 * n))
      ... = 0 :: nat.digits 10 n : _,
      { rw nat.digits_add,
        norm_num,
        norm_num,
        right, exact h0, } },
    calc (nat.digits 10 (10 * n)).sum = (0 :: nat.digits 10 n).sum : by rw h
    ... = 0 + (nat.digits 10 n).sum : by rw list.sum_cons
    ... = (nat.digits 10 n).sum : by rw nat.zero_add, }
end

-- And then use the previous lemma and induct on a
-- Lemma name suggestion by Yaël Dillies on the Xena Project Discord
lemma digits_sum_ten_pow_mul {a n : ℕ} :
  digits_sum (10^a * n) = digits_sum n :=
begin
  induction a,
  simp,
  rwa [pow_succ, mul_assoc, digits_sum_ten_mul],
end

theorem osk2002_13 : digits_sum (2^(2002) * 5^(2003)) = 5 :=
begin
  have h : 2^(2002) * 5^(2003) = 10^(2002) * 5,
  { calc 2^(2002) * 5^(2003) = 2^(2002) * 5^(2002 + 1) : _ 
    ... = 2^(2002) * (5^(2002) * 5^1) : by rw pow_add
    ... = 2^(2002) * 5^(2002) * 5 : by simp [mul_assoc]
    ... = 10^(2002) * 5 : _,
    { simp,
      apply congr_arg,
      norm_num, },
    { rw ← mul_pow,
      simp,
      norm_num, } },
  calc digits_sum (2^(2002) * 5^(2003)) = digits_sum(10^(2002) * 5) : by rw h
  ... = digits_sum(5) : by rw digits_sum_ten_pow_mul
  ... = 5 : by simp [digits_sum],
end