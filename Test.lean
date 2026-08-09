import Mathlib

-- 1. evaluation
#eval 2 + 2

-- 2. Mathlib loaded
#check Real.pi

-- 3. elaboration + ring
example (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring

-- 4. numeric bounds on pi  (needed for the certificate section)
example : (3.14 : ℝ) < Real.pi := by exact Real.pi_gt_d2

-- 5. derivatives  (needed for the arc' identity)
example : deriv (fun x : ℝ => x^2) 1 = 2 := by simp
