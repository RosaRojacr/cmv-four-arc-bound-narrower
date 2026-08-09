/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import MinimumValue

/-!
# A rational certificate for `min g`

`MinimumValue` proved the sharp statement

  `min_{x>0} g x = 3 cos θ*`,     attained at `x* = area θ*`,

where `θ*` is the unique root of `F θ = 3θ - 3 sin θ cos θ - π`. That equality
is exact and is the actual result; this file certifies a numeric bound for it.

Cañete–Miranda–Vittone bound `g` below by `π / 4 = 0.7853981…`, giving the
threshold `lam ≥ 4 / π = 1.2732395…` for excluding four-arc isoperimetric
candidates for the strip density. Their Remark 3.17 asserts this is not optimal
but does not compute the true constant. Here:

  `3 cos 1.3026632 < min g`,   i.e.   `lam ≥ 1.2581858` suffices,

against the sharp but irrational value `lam > 1.2581840883…`. The gap is
`1.7 · 10⁻⁶`.

## Why no certificate reaches the sharp value

`cos` is strictly decreasing, so every witness `t₀ > θ*` gives a constant
strictly below `3 cos θ*`. The sharp threshold is a supremum over certificates,
attained by none. The bound is stated in exact form `3 * cos 1.3026632 < g x`
rather than as a decimal, avoiding a second layer of rounding.

## Method: three halvings

`F` strictly increasing means one witness `t₀` with `F t₀ > 0` gives
`θ* < t₀`. This needs an upper bound on `sin 2.6053264`, whose argument is far
from `0`. Reflecting gives `y = π - 2.6053264 ∈ (0.5362656, 0.5362666)`, but
`Real.sin_bound` at `y` wastes `y⁵/600 ≈ 7.6 · 10⁻⁵`, since its error term
`y⁵/100` overshoots the true `y⁵/120`.

That waste scales as the fifth power, so each halving gains a factor of `32`.
We halve three times, to `q = y/4`, `r = y/8`, `s = y/16`, and rebuild upward
using only two Mathlib inputs (`Real.sin_bound` and `Real.sin_gt_sub_cube`)
together with the two double-angle identities

  `sin 2u = 2 sin u cos u`,        `cos 2u = 1 - 2 sin²u`.

The second is what makes this cheap: it converts every cosine bound into a
bound on a *sine* at half the argument, where the polynomial estimates are
sharp.

At this depth `π` becomes the binding error source: `Real.pi_gt_d6` gives
`10⁻⁶`, entering with sensitivity about `1.5`. Mathlib has no `pi_gt_d8`, so
the witness is chosen to keep a `7 · 10⁻⁷` margin against the six-decimal
bounds.

## History

| method | threshold | gap to sharp |
|---|---|---|
| direct `sin_bound` at `y` | `1.2584157` | `2.3 · 10⁻⁴` |
| one halving | `1.2582032` | `1.9 · 10⁻⁵` |
| two halvings | `1.2581894` | `5.3 · 10⁻⁶` |
| three halvings (this file) | `1.2581857` | `1.7 · 10⁻⁶` |
| sharp `1 / (3 cos θ*)` | `1.2581841` | — |

Further halving would not help: the residual is now dominated by the precision
of `π`, not by the trigonometric estimates. Improving it requires sharper `π`
bounds, e.g. via `Real.pi_lower_bound_start` / `pi_upper_bound_start`, which
would leave every lemma below unchanged apart from the numerals.
-/

open Real Set Filter Topology

/-! ## The structural half -/

/-- One rational witness above the root bounds it. -/
lemma θstar_lt_of_F_pos {t : ℝ} (ht : t ∈ Icc 0 π) (h : 0 < F t) : θstar < t := by
  by_contra hcon
  push Not at hcon
  have hs : θstar ∈ Icc 0 π := ⟨le_of_lt θstar_pos, le_of_lt θstar_lt_pi⟩
  rcases eq_or_lt_of_le hcon with heq | hlt
  · rw [heq, θstar_spec] at h
    linarith
  · have := F_strictMonoOn ht hs hlt
    rw [θstar_spec] at this
    linarith

/-- `cos` is strictly decreasing on `[0, π]`, so an upper bound on `θ*` becomes
a lower bound on `k = 3 cos θ*`. -/
lemma three_cos_lt_of_θstar_lt {t : ℝ} (ht : t ≤ π) (h : θstar < t) :
    3 * cos t < 3 * cos θstar := by
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt θstar_pos) ht h
  linarith

/-! ## `π` to six decimals -/

lemma pi_lb : (3.141592 : ℝ) < π := by
  have := Real.pi_gt_d6
  linarith

lemma pi_ub : π < (3.141593 : ℝ) := by
  have := Real.pi_lt_d6
  linarith

/-! ## The double-angle identity for cosine -/

lemma cos_two_mul_sin_sq (u : ℝ) : cos (2 * u) = 1 - 2 * sin u ^ 2 := by
  rw [cos_two_mul]
  linear_combination (2:ℝ) * sin_sq_add_cos_sq u

/-! ## Level 4: `s = y / 16 ∈ (0.0335166, 0.0335166625)` -/

lemma sin_s_ge : (0.033510324749 : ℝ) ≤ sin ((π - 2.6053264) / 16) := by
  set s : ℝ := (π - 2.6053264) / 16 with hs
  have hlo : (0.0335166 : ℝ) < s := by rw [hs]; linarith [pi_lb]
  have hhi : s < (0.0335166625 : ℝ) := by rw [hs]; linarith [pi_ub]
  have h0 : (0:ℝ) < s := by linarith
  have hc := Real.sin_gt_sub_cube h0
  have h2 : s^2 ≤ (0.0335166625 : ℝ)^2 := by nlinarith
  have h3 : s^3 ≤ (0.0335166625 : ℝ)^3 := by nlinarith
  norm_num at h3
  linarith

lemma sin_s_le : sin ((π - 2.6053264) / 16) ≤ 0.033510387708 := by
  set s : ℝ := (π - 2.6053264) / 16 with hs
  have hlo : (0.0335166 : ℝ) < s := by rw [hs]; linarith [pi_lb]
  have hhi : s < (0.0335166625 : ℝ) := by rw [hs]; linarith [pi_ub]
  have h0 : (0:ℝ) ≤ s := by linarith
  have habs : |s| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hb := Real.sin_bound habs
  rw [abs_of_nonneg h0] at hb
  rw [abs_le] at hb
  have h2l : (0.0335166 : ℝ)^2 ≤ s^2 := by nlinarith
  have h3l : (0.0335166 : ℝ)^3 ≤ s^3 := by nlinarith
  have h2h : s^2 ≤ (0.0335166625 : ℝ)^2 := by nlinarith
  have h4h : s^4 ≤ (0.0335166625 : ℝ)^4 := by nlinarith
  have h5h : s^5 ≤ (0.0335166625 : ℝ)^5 := by nlinarith
  norm_num at h3l h5h
  linarith [hb.2]

/-! ## Level 3: `r = y / 8 ∈ (0.0670332, 0.067033325)` -/

lemma sin_r_ge : (0.066982997998 : ℝ) ≤ sin ((π - 2.6053264) / 8) := by
  set r : ℝ := (π - 2.6053264) / 8 with hr
  have hlo : (0.0670332 : ℝ) < r := by rw [hr]; linarith [pi_lb]
  have hhi : r < (0.067033325 : ℝ) := by rw [hr]; linarith [pi_ub]
  have h0 : (0:ℝ) < r := by linarith
  have hc := Real.sin_gt_sub_cube h0
  have h2 : r^2 ≤ (0.067033325 : ℝ)^2 := by nlinarith
  have h3 : r^3 ≤ (0.067033325 : ℝ)^3 := by nlinarith
  norm_num at h3
  linarith

lemma sin_r_le : sin ((π - 2.6053264) / 8) ≤ 0.066983136814 := by
  set r : ℝ := (π - 2.6053264) / 8 with hr
  have hlo : (0.0670332 : ℝ) < r := by rw [hr]; linarith [pi_lb]
  have hhi : r < (0.067033325 : ℝ) := by rw [hr]; linarith [pi_ub]
  have h0 : (0:ℝ) ≤ r := by linarith
  have habs : |r| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hb := Real.sin_bound habs
  rw [abs_of_nonneg h0] at hb
  rw [abs_le] at hb
  have h2l : (0.0670332 : ℝ)^2 ≤ r^2 := by nlinarith
  have h3l : (0.0670332 : ℝ)^3 ≤ r^3 := by nlinarith
  have h2h : r^2 ≤ (0.067033325 : ℝ)^2 := by nlinarith
  have h4h : r^4 ≤ (0.067033325 : ℝ)^4 := by nlinarith
  have h5h : r^5 ≤ (0.067033325 : ℝ)^5 := by nlinarith
  norm_num at h3l h5h
  linarith [hb.2]

lemma cos_r_le : cos ((π - 2.6053264) / 8) ≤ 0.997754116271 := by
  have h := sin_s_ge
  have hd : (π - 2.6053264) / 8 = 2 * ((π - 2.6053264) / 16) := by ring
  rw [hd, cos_two_mul_sin_sq]
  nlinarith [h]

lemma cos_r_ge : (0.997754107831 : ℝ) ≤ cos ((π - 2.6053264) / 8) := by
  have h := sin_s_le
  have h0 : (0:ℝ) ≤ sin ((π - 2.6053264) / 16) := by linarith [sin_s_ge]
  have hd : (π - 2.6053264) / 8 = 2 * ((π - 2.6053264) / 16) := by ring
  rw [hd, cos_two_mul_sin_sq]
  nlinarith [h, h0]

/-! ## Level 2: `q = y / 4` -/

lemma sin_q_le : sin ((π - 2.6053264) / 4) ≤ 0.133665400954 := by
  have hs := sin_r_le
  have hc := cos_r_le
  have hs0 : (0:ℝ) ≤ sin ((π - 2.6053264) / 8) := by linarith [sin_r_ge]
  have hc0 : (0:ℝ) ≤ cos ((π - 2.6053264) / 8) := by linarith [cos_r_ge]
  have hd : (π - 2.6053264) / 4 = 2 * ((π - 2.6053264) / 8) := by ring
  rw [hd, sin_two_mul]
  nlinarith [hs, hc, hs0, hc0]

lemma sin_q_ge : (0.133665122814 : ℝ) ≤ sin ((π - 2.6053264) / 4) := by
  have hs := sin_r_ge
  have hc := cos_r_ge
  have hd : (π - 2.6053264) / 4 = 2 * ((π - 2.6053264) / 8) := by ring
  rw [hd, sin_two_mul]
  nlinarith [hs, hc]

lemma cos_q_le : cos ((π - 2.6053264) / 4) ≤ 0.991026555959 := by
  have h := sin_r_ge
  have hd : (π - 2.6053264) / 4 = 2 * ((π - 2.6053264) / 8) := by ring
  rw [hd, cos_two_mul_sin_sq]
  nlinarith [h]

/-! ## Level 1: `h = y / 2`, then `sin y` -/

lemma sin_h_le : sin ((π - 2.6053264) / 2) ≤ 0.264931923917 := by
  have hs := sin_q_le
  have hc := cos_q_le
  have hs0 : (0:ℝ) ≤ sin ((π - 2.6053264) / 4) := by linarith [sin_q_ge]
  have hc0 : (0:ℝ) ≤ cos ((π - 2.6053264) / 4) := by
    refine le_of_lt (cos_pos_of_mem_Ioo ⟨?_, ?_⟩) <;> linarith [pi_lb, pi_ub]
  have hd : (π - 2.6053264) / 2 = 2 * ((π - 2.6053264) / 4) := by ring
  rw [hd, sin_two_mul]
  nlinarith [hs, hc, hs0, hc0]

lemma cos_h_le : cos ((π - 2.6053264) / 2) ≤ 0.964267269887 := by
  have h := sin_q_ge
  have hd : (π - 2.6053264) / 2 = 2 * ((π - 2.6053264) / 4) := by ring
  rw [hd, cos_two_mul_sin_sq]
  nlinarith [h]

lemma sin_witness_lt : sin (2.6053264 : ℝ) < 0.510930366 := by
  have hs := sin_h_le
  have hc := cos_h_le
  have hs0 : (0:ℝ) ≤ sin ((π - 2.6053264) / 2) := by
    refine le_of_lt (sin_pos_of_pos_of_lt_pi ?_ ?_) <;> linarith [pi_lb, pi_ub]
  have hc0 : (0:ℝ) ≤ cos ((π - 2.6053264) / 2) := by
    refine le_of_lt (cos_pos_of_mem_Ioo ⟨?_, ?_⟩) <;> linarith [pi_lb, pi_ub]
  have hrefl : sin (2.6053264 : ℝ) = sin (π - 2.6053264) := (sin_pi_sub _).symm
  have hd : (π - 2.6053264 : ℝ) = 2 * ((π - 2.6053264) / 2) := by ring
  rw [hrefl, hd, sin_two_mul]
  nlinarith [hs, hc, hs0, hc0]

/-- `F 1.3026632 > 0`, hence `θ* < 1.3026632`. Margin `7.0 · 10⁻⁷`. -/
lemma F_at_witness : 0 < F (1.3026632 : ℝ) := by
  have hdouble : (3:ℝ) * (sin 1.3026632 * cos 1.3026632) = 3 / 2 * sin 2.6053264 := by
    have h : (2.6053264 : ℝ) = 2 * 1.3026632 := by norm_num
    rw [h, sin_two_mul]; ring
  rw [F, hdouble]
  linarith [sin_witness_lt, pi_ub]

lemma θstar_lt_witness : θstar < 1.3026632 := by
  refine θstar_lt_of_F_pos ⟨by norm_num, ?_⟩ F_at_witness
  linarith [pi_lb]

/-! ## The bound -/

/-- **The certified bound, in exact form.**

`3 cos 1.3026632 < min (2 arc x - arc (2 x))`. Numerically the left side is
`0.7947952…`, so `lam ≥ 1.2581858` suffices — against CMV's
`4 / π = 1.2732395…` and the sharp `1.2581840883…`. -/
theorem min_g_gt_witness {x : ℝ} (hx : 0 < x) : 3 * cos (1.3026632 : ℝ) < g x := by
  have h1 : 3 * cos (1.3026632 : ℝ) < 3 * cos θstar :=
    three_cos_lt_of_θstar_lt (by linarith [pi_lb]) θstar_lt_witness
  have h2 : 3 * cos θstar ≤ g x := min_g_eq_three_mul_cos_θstar hx
  linarith

/-! ## The `π / 4` corollary -/

lemma three_cos_witness_gt_pi_div_four : π / 4 < 3 * cos (1.3026632 : ℝ) := by
  set z : ℝ := π / 2 - 1.3026632 with hz
  have hlo : (0.2681328 : ℝ) < z := by rw [hz]; linarith [pi_lb]
  have hhi : z < (0.2681333 : ℝ) := by rw [hz]; linarith [pi_ub]
  have hz0 : (0:ℝ) < z := by linarith
  have hcube := Real.sin_gt_sub_cube hz0
  have hsq_hi : z^2 ≤ (0.2681333 : ℝ)^2 := by nlinarith
  have hcube_hi : z^3 ≤ (0.2681333 : ℝ)^3 := by nlinarith
  norm_num at hcube_hi
  have hrefl : cos (1.3026632 : ℝ) = sin z := by rw [hz, sin_pi_div_two_sub]
  rw [hrefl]
  linarith [pi_ub]

/-- **CMV Remark 3.17, proved.** The published bound `π / 4` on
`min (2 arc x - arc (2 x))` is not optimal: the minimum strictly exceeds it. -/
theorem min_g_gt_pi_div_four {x : ℝ} (hx : 0 < x) : π / 4 < g x := by
  have := min_g_gt_witness hx
  linarith [three_cos_witness_gt_pi_div_four]
