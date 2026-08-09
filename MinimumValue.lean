/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Minimiser

/-!
# `x*` is the global minimum of `g`, so `min g = 3 cos θ*`

`Minimiser` showed that `x* = area θ*` is a critical point of `g` with
`g x* = 3 cos θ*`. This file upgrades "critical point" to "global minimum",
completing the closed form for the constant `k` of Cañete–Miranda–Vittone
Remark 3.17.

The argument has three steps.

1. **`x*` lies strictly inside `(π / 16, π / 8)`.** This needs no numerics: if
   `x* ≤ π / 16` then `GFunction.g_deriv_neg` would make `g' x* < 0`, and if
   `π / 8 ≤ x*` then `g_deriv_pos` would make `g' x* > 0`. Both contradict
   `g' x* = 0`.

2. **`g'` is strictly increasing on `(π / 16, π / 8)`.** There `θOf x < π / 2 <
   θOf (2 * x)`, so as `x` grows `sin (θOf x)` rises while `sin (θOf (2 * x))`
   falls, and `g' = 4 (sin (θOf x) - sin (θOf (2 * x)))` rises on both counts.
   Hence `g' < 0` strictly before `x*` and `g' > 0` strictly after.

3. **Therefore `g` decreases on `(0, x*]` and increases on `[x*, ∞)`**, so `x*`
   is the global minimum on `(0, ∞)`.
-/

open Real Set Filter Topology

/-- Abbreviation for the derivative of `g`, from `GFunction.hasDerivAt_g`. -/
noncomputable def gd (x : ℝ) : ℝ := 4 * sin (θOf x) - 4 * sin (θOf (2 * x))

lemma hasDerivAt_g' {x : ℝ} (hx : 0 < x) : HasDerivAt g (gd x) x :=
  hasDerivAt_g hx

/-! ## Step 1: locating `x*` -/

lemma gd_xstar : gd xstar = 0 := g_deriv_xstar

lemma pi_div_sixteen_lt_xstar : π / 16 < xstar := by
  by_contra h
  push Not at h
  have := g_deriv_neg xstar_pos h
  rw [← gd, gd_xstar] at this
  linarith

lemma xstar_lt_pi_div_eight : xstar < π / 8 := by
  by_contra h
  push Not at h
  have := g_deriv_pos h
  rw [← gd, gd_xstar] at this
  linarith

lemma xstar_mem_Ioo : xstar ∈ Ioo (π / 16) (π / 8) :=
  ⟨pi_div_sixteen_lt_xstar, xstar_lt_pi_div_eight⟩

/-! ## Step 2: `gd` is strictly increasing on `(π / 16, π / 8)` -/

lemma θOf_lt_pi_div_two_of_mem {x : ℝ} (hx : x ∈ Ioo (π / 16) (π / 8)) :
    θOf x < π / 2 :=
  θOf_lt_pi_div_two (lt_trans (by linarith [pi_pos]) hx.1) hx.2

lemma pi_div_two_le_θOf_two_mul {x : ℝ} (hx : x ∈ Ioo (π / 16) (π / 8)) :
    π / 2 ≤ θOf (2 * x) :=
  pi_div_two_le_θOf (by linarith [hx.1])

lemma gd_strictMonoOn : StrictMonoOn gd (Ioo (π / 16) (π / 8)) := by
  intro a ha b hb hab
  have ha0 : 0 < a := lt_trans (by linarith [pi_pos]) ha.1
  have hb0 : 0 < b := lt_trans (by linarith [pi_pos]) hb.1
  have ha2 : (0:ℝ) < 2 * a := by linarith
  have hb2 : (0:ℝ) < 2 * b := by linarith
  -- the small angles rise
  have h1 : sin (θOf a) < sin (θOf b) := by
    refine sin_lt_sin_of_le_pi_div_two (le_of_lt (θOf_mem ha0).1) ?_ ?_
    · exact θOf_strictMonoOn (mem_Ioi.mpr ha0) (mem_Ioi.mpr hb0) hab
    · exact le_of_lt (θOf_lt_pi_div_two_of_mem hb)
  -- the large angles fall
  have h2 : sin (θOf (2 * b)) < sin (θOf (2 * a)) := by
    refine sin_lt_sin_of_pi_div_two_le (pi_div_two_le_θOf_two_mul ha) ?_ ?_
    · exact θOf_strictMonoOn (mem_Ioi.mpr ha2) (mem_Ioi.mpr hb2) (by linarith)
    · exact le_of_lt (θOf_mem hb2).2
  rw [gd, gd]
  linarith

/-! ## Step 3: the sign of `gd` on either side of `x*` -/

lemma gd_neg_of_lt_xstar {x : ℝ} (hx : 0 < x) (h : x < xstar) : gd x < 0 := by
  rcases le_or_gt x (π / 16) with hle | hgt
  · have := g_deriv_neg hx hle
    rwa [← gd] at this
  · have hmem : x ∈ Ioo (π / 16) (π / 8) :=
      ⟨hgt, lt_trans h xstar_lt_pi_div_eight⟩
    have := gd_strictMonoOn hmem xstar_mem_Ioo h
    rwa [gd_xstar] at this

lemma gd_pos_of_xstar_lt {x : ℝ} (h : xstar < x) : 0 < gd x := by
  rcases le_or_gt (π / 8) x with hle | hgt
  · have := g_deriv_pos hle
    rwa [← gd] at this
  · have hmem : x ∈ Ioo (π / 16) (π / 8) :=
      ⟨lt_trans pi_div_sixteen_lt_xstar h, hgt⟩
    have := gd_strictMonoOn xstar_mem_Ioo hmem h
    rwa [gd_xstar] at this

/-! ## Step 4: `g` has its global minimum at `x*` -/

lemma g_strictAntiOn : StrictAntiOn g (Ioc 0 xstar) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioc 0 xstar)
  · exact fun x hx => (hasDerivAt_g' hx.1).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    exact (hasDerivAt_g' hx.1).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    exact gd_neg_of_lt_xstar hx.1 hx.2

lemma g_strictMonoOn_Ici : StrictMonoOn g (Ici xstar) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici xstar)
  · intro x hx
    exact (hasDerivAt_g' (lt_of_lt_of_le xstar_pos hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact (hasDerivAt_g' (lt_trans xstar_pos hx)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact gd_pos_of_xstar_lt hx

/-- **`g` attains its minimum over `(0, ∞)` at `x*`.** -/
theorem g_xstar_le {x : ℝ} (hx : 0 < x) : g xstar ≤ g x := by
  rcases le_or_gt x xstar with hle | hgt
  · rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq]
    · exact le_of_lt (g_strictAntiOn ⟨hx, hle⟩ ⟨xstar_pos, le_refl _⟩ hlt)
  · exact le_of_lt (g_strictMonoOn_Ici (mem_Ici.mpr (le_refl xstar))
      (mem_Ici.mpr (le_of_lt hgt)) hgt)

/-- **The constant of CMV Remark 3.17, in closed form.**

For every `x > 0`, `2 arc x - arc (2 x) ≥ 3 cos θ*`, where `θ*` is the unique
root of `3 θ - 3 sin θ cos θ = π`. The bound is attained at `x* = area θ*`,
so it is sharp.

Numerically `θ* = 1.30266283730…` and `3 cos θ* = 0.79479625381…`, against
CMV's published lower bound `π / 4 = 0.78539816340…`. -/
theorem min_g_eq_three_mul_cos_θstar {x : ℝ} (hx : 0 < x) :
    3 * cos θstar ≤ g x := by
  rw [← g_θstar]
  exact g_xstar_le hx

/-- The bound is attained, so no larger constant works. -/
theorem min_g_attained : g xstar = 3 * cos θstar := g_θstar

/-! ## What remains

Only the rational certificate. `F` is strictly increasing, so exhibiting a
rational `t₀` with `F t₀ > 0` gives `θ* < t₀`, and since `cos` is decreasing on
`(0, π / 2)`, `k = 3 cos θ* > 3 cos t₀`. With `t₀ = 1.3027` this gives
`k > 0.7946`, hence the threshold `lam ≥ 1.2584` — an improvement on CMV's
`4 / π = 1.27324…`.

The work there is rigorous rational bounds on `sin 2.6054` and `cos 1.3027`.
Mathlib's polynomial trigonometric bounds are stated near zero, so this will
need argument reduction rather than a direct Taylor estimate.
-/
