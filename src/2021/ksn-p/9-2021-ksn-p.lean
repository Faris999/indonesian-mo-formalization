import data.rat.basic
import data.rat.floor
import data.rat.order
import tactic

namespace KSNP2021_9

def pos_rat_set : set ℚ := { x | 0 < x }

def nat_set : set ℚ := { x | 0 < x ∧ coe (rat.floor x) = x }

def interval : ℚ → ℚ → set ℚ := λ a b, { x | a ≤ x ∧ x ≤ b } 

lemma one_eq_2021_div_2021 : (1 : ℚ) = ((2021 : ℚ) / (2021 : ℚ) : ℚ) := by norm_num

theorem KSNP2021_9 {x y : ℚ} (X : set ℚ) (h1 : 2021 ≤ x → x ≤ 2022 → x ∈ X) (h2 : x ∈ X → y ∈ X → x / y ∈ X) : pos_rat_set ⊆ X :=
begin
  have h3 : (1 : ℚ) ∈ X,
  { sorry, },
  have h4 : interval x (x + 1) ⊆ X → interval (x + 1) (x + 2) ⊆ X,
  { sorry, },
  have h5 : { x : ℚ | 2021 ≤ x} ⊆ X,
  { sorry, },
  have h6 : interval 1 2 ⊆ X,
  { sorry, },
  have h7 : nat_set ⊆ X,
  { sorry, },
  have h8 : { x : ℚ | 0 < x ∧ x ≤ 1} ⊆ X,
  { sorry, },
  -- Combine all of them
  sorry,
end

end KSNP2021_9