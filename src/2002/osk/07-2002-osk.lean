import data.real.basic

def dollar (x y : ℝ) := x*y - x + y

infix `$` : 50 := dollar

theorem osk2002_7 {x y : ℝ} : (x+y) $ (x-y) = x^2 - y^2 - 2 * y :=
begin
  rw dollar,
  ring,
end