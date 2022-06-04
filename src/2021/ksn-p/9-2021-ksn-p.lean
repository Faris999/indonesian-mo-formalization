import data.rat.basic
import data.rat.floor
import data.rat.order
import data.set.intervals.basic
import tactic

namespace KSNP2021_9

def pos_rat_set : set ℚ := { x | 0 < x }

def nat_set : set ℚ := { x | 0 < x ∧ coe (rat.floor x) = x } 

lemma one_eq_2021_div_2021 : (1 : ℚ) = ((2021 : ℚ) / (2021 : ℚ) : ℚ) := by norm_num

theorem KSNP2021_9
  {X : set ℚ}
  (h1 : set.Icc 2021 2022 ⊆ X)
  (h2 : ∀ x y, x ∈ X → y ∈ X → x / y ∈ X) :
  pos_rat_set ⊆ X :=
begin
  have X_contains_2021 : (2021 : ℚ) ∈ X,
  { have  h : (2021 : ℚ) ∈ (set.Icc 2021 2022 : set ℚ),
    rw set.mem_Icc,
    norm_num,
    apply set.mem_of_subset_of_mem h1 h,
  },
  have X_contains_one : (1 : ℚ) ∈ X,
  { rw one_eq_2021_div_2021,
    apply h2 2021 2021,
    rw set.Icc at h1,
    exact X_contains_2021,
    exact X_contains_2021, },
  have h4 : ∀ x, set.Icc x (x + 1) ⊆ X → set.Icc (x + 1) (x + 2) ⊆ X,
  { sorry, },
  have h5 : set.Ici 2021 ⊆ X,
  { sorry, },
  have h6 : set.Icc 1 2 ⊆ X,
  { sorry, },
  have h7 : nat_set ⊆ X,
  { sorry, },
  have h8 : set.Ioc 0 1 ⊆ X,
  { sorry, },
  -- Combine all of them
  sorry,
end

end KSNP2021_9