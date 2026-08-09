/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import MorgansArcFunction

/-!
# The function `g x = 2 * arc x - arc (2 * x)`

This file takes the derivative identity `arc' x = 2 sin (θOf x)` from
`MorgansArcFunction` and draws out the consequences needed to locate the
minimum of

  `g x = 2 * arc x - arc (2 * x)`.

This `g` is the quantity appearing in the cap-substitution step of Cañete–
Miranda–Vittone, *Some isoperimetric problems in planes with density*,
J. Geom. Anal. **20** (2010) 243–290, proof of Theorem 3.16: a four-arc
isoperimetric candidate for the strip density is excluded as soon as
`g x > 1 / lam` for the relevant `x = A / L²`. CMV bound `g` below by `π / 4`
using only Morgan's convexity properties, giving the threshold `lam ≥ 4/π`.
Their Remark 3.17 observes this is not optimal — the true threshold is
`lam > 1 / k` with `k = min g` — but does not compute `k`.

## Contents

* `arc_pi_div_eight`, `hasDerivAt_arc_pi_div_eight` — Morgan's published values
  `arc (π / 8) = π / 2` and `arc' (π / 8) = 2`, recovered as a sanity check
* `hasDerivAt_g` — `g' x = 4 (sin (θOf x) - sin (θOf (2x)))`
* `g_deriv_neg`, `g_deriv_pos` — the sign of `g'` outside `(π / 16, π / 8)`

The interior behaviour on `(π / 16, π / 8)`, the uniqueness of the minimiser, and
the closed form `k = 3 cos θ*` are left to a later file.
-/

open Real Set Filter Topology

/-! ## Two monotonicity facts for `sin`

`arc'` is `2 sin ∘ θOf`, so comparing `arc'` at two points means comparing
`sin` at two angles. On `(0, π / 2]` sine increases; on `[π / 2, π)` it decreases.
The second is obtained from the first by reflecting through `π - θ`.
-/

lemma sin_lt_sin_of_le_pi_div_two {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ π / 2) : sin a < sin b := by
  refine Real.strictMonoOn_sin ⟨by linarith [pi_pos], by linarith⟩
    ⟨by linarith [pi_pos], hb⟩ hab

lemma sin_lt_sin_of_pi_div_two_le {a b : ℝ} (ha : π / 2 ≤ a) (hab : a < b)
    (hb : b ≤ π) : sin b < sin a := by
  have h1 : sin a = sin (π - a) := (sin_pi_sub a).symm
  have h2 : sin b = sin (π - b) := (sin_pi_sub b).symm
  rw [h1, h2]
  refine Real.strictMonoOn_sin ⟨by linarith [pi_pos], by linarith⟩
    ⟨by linarith [pi_pos], by linarith⟩ (by linarith)

/-! ## The semicircle: `θOf (π / 8) = π / 2`

At `θ = π / 2` the segment is a half-disc of radius `1/2`, with area `π / 8` and
arc length `π / 2`. This pins the value of `θOf` at `π / 8` and recovers Morgan's
two published constants.
-/

lemma pi_div_eight_pos : (0:ℝ) < π / 8 := by linarith [pi_pos]

lemma area_pi_div_two : area (π / 2) = π / 8 := by
  rw [area, sin_pi_div_two, cos_pi_div_two]
  ring

lemma ell_pi_div_two : ell (π / 2) = π / 2 := by
  rw [ell, sin_pi_div_two, div_one]

lemma θOf_pi_div_eight : θOf (π / 8) = π / 2 := by
  have hmem : π / 2 ∈ Ioo 0 π := ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have := θOf_area hmem
  rwa [area_pi_div_two] at this

/-- Morgan, GMT 4th ed. §15.5: `arc (π / 8) = π / 2`. -/
theorem arc_pi_div_eight : arc (π / 8) = π / 2 := by
  rw [arc_eq, θOf_pi_div_eight, ell_pi_div_two]

/-- Morgan, GMT 4th ed. §15.5: `arc' (π / 8) = 2`. -/
theorem hasDerivAt_arc_pi_div_eight : HasDerivAt arc 2 (π / 8) := by
  have h := hasDerivAt_arc pi_div_eight_pos
  rwa [θOf_pi_div_eight, sin_pi_div_two, mul_one] at h

/-! ## Locating `θOf` relative to `π / 2`

`θOf` is strictly increasing and sends `π / 8` to `π / 2`, so it sends `(0, π / 8)`
into `(0, π / 2)` and `(π / 8, ∞)` into `(π / 2, π)`. This is the bridge between
statements about `x` and statements about the angle.
-/

lemma θOf_lt_pi_div_two {x : ℝ} (hx : 0 < x) (h : x < π / 8) : θOf x < π / 2 := by
  have := θOf_strictMonoOn (mem_Ioi.mpr hx) (mem_Ioi.mpr pi_div_eight_pos) h
  rwa [θOf_pi_div_eight] at this

lemma θOf_le_pi_div_two {x : ℝ} (hx : 0 < x) (h : x ≤ π / 8) : θOf x ≤ π / 2 := by
  rcases eq_or_lt_of_le h with heq | hlt
  · rw [heq, θOf_pi_div_eight]
  · exact le_of_lt (θOf_lt_pi_div_two hx hlt)

lemma pi_div_two_le_θOf {x : ℝ} (h : π / 8 ≤ x) : π / 2 ≤ θOf x := by
  rcases eq_or_lt_of_le h with heq | hlt
  · rw [← heq, θOf_pi_div_eight]
  · have := θOf_strictMonoOn (mem_Ioi.mpr pi_div_eight_pos)
      (mem_Ioi.mpr (lt_trans pi_div_eight_pos hlt)) hlt
    rw [θOf_pi_div_eight] at this
    exact le_of_lt this

/-! ## The function `g` and its derivative -/

/-- `g x = 2 * arc x - arc (2 * x)`. The cap-substitution argument of CMV
Theorem 3.16 succeeds exactly when `g x > 1 / lam`. -/
noncomputable def g (x : ℝ) : ℝ := 2 * arc x - arc (2 * x)

/-- The chain rule on `arc (2 * x)` contributes a factor of `2`, so both terms
carry a `4`. -/
lemma hasDerivAt_arc_two_mul {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => arc (2 * t)) (4 * sin (θOf (2 * x))) x := by
  have h2x : (0:ℝ) < 2 * x := by linarith
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2:ℝ)
  have h := (hasDerivAt_arc h2x).comp x hlin
  have heq : (arc ∘ fun t : ℝ => 2 * t) = fun t => arc (2 * t) := rfl
  rw [heq] at h
  refine h.congr_deriv ?_
  ring

theorem hasDerivAt_g {x : ℝ} (hx : 0 < x) :
    HasDerivAt g (4 * sin (θOf x) - 4 * sin (θOf (2 * x))) x := by
  have h1 : HasDerivAt (fun t => 2 * arc t) (2 * (2 * sin (θOf x))) x :=
    (hasDerivAt_arc hx).const_mul (2:ℝ)
  have h2 := hasDerivAt_arc_two_mul hx
  refine (h1.sub h2).congr_deriv ?_
  ring
/-! ## The sign of `g'` away from `(π / 16, π / 8)`

Since `x < 2x`, monotonicity of `θOf` gives `θOf x < θOf (2x)` always. The sign
of `g'` is then decided by where those two angles sit relative to `π / 2`.

* If `2x ≤ π / 8` both angles are at most `π / 2`, sine is increasing there, so
  `sin (θOf x) < sin (θOf (2x))` and `g' < 0`.
* If `π / 8 ≤ x` both angles are at least `π / 2`, sine is decreasing there, so
  `sin (θOf (2x)) < sin (θOf x)` and `g' > 0`.

Between `π / 16` and `π / 8` the two angles straddle `π / 2` and the comparison is
genuinely delicate — that is where the minimum lies.
-/

lemma θOf_lt_θOf_two_mul {x : ℝ} (hx : 0 < x) : θOf x < θOf (2 * x) := by
  have h2x : (0:ℝ) < 2 * x := by linarith
  exact θOf_strictMonoOn (mem_Ioi.mpr hx) (mem_Ioi.mpr h2x) (by linarith)

/-- On `(0, π / 16]` the derivative of `g` is negative. -/
theorem g_deriv_neg {x : ℝ} (hx : 0 < x) (h : x ≤ π / 16) :
    4 * sin (θOf x) - 4 * sin (θOf (2 * x)) < 0 := by
  have h2x : (0:ℝ) < 2 * x := by linarith
  have hle : 2 * x ≤ π / 8 := by linarith
  have hlt : θOf x < θOf (2 * x) := θOf_lt_θOf_two_mul hx
  have hup : θOf (2 * x) ≤ π / 2 := θOf_le_pi_div_two h2x hle
  have hlow : 0 ≤ θOf x := le_of_lt (θOf_mem hx).1
  have := sin_lt_sin_of_le_pi_div_two hlow hlt hup
  linarith

/-- On `[π / 8, ∞)` the derivative of `g` is positive. -/
theorem g_deriv_pos {x : ℝ} (h : π / 8 ≤ x) :
    0 < 4 * sin (θOf x) - 4 * sin (θOf (2 * x)) := by
  have hx : (0:ℝ) < x := lt_of_lt_of_le pi_div_eight_pos h
  have h2x : (0:ℝ) < 2 * x := by linarith
  have hlt : θOf x < θOf (2 * x) := θOf_lt_θOf_two_mul hx
  have hlow : π / 2 ≤ θOf x := pi_div_two_le_θOf h
  have hup : θOf (2 * x) ≤ π := le_of_lt (θOf_mem h2x).2
  have := sin_lt_sin_of_pi_div_two_le hlow hlt hup
  linarith

/-! ## What remains

The minimiser `x*` lies in `(π / 16, π / 8)`. There `θOf x* < π / 2 < θOf (2x*)`, so
`sin (θOf x)` is increasing in `x` while `sin (θOf (2x))` is decreasing, making
`g'` strictly increasing on that interval — hence a unique zero, and a unique
minimum. At that point `sin (θOf x*) = sin (θOf (2x*))` with the two angles
distinct, forcing

  `θOf x* + θOf (2x*) = π`,

which combined with `area (π - θ) = 2 * area θ` reduces to the single equation

  `3 (θ* - sin θ* cos θ*) = π`,

and then `k = g x* = 3 cos θ*`. Numerically `θ* = 1.30266…`, `k = 0.79479…`,
`1/k = 1.25818…`, against CMV's published `4/π = 1.27324…`.
-/
