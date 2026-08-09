/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import GFunction

/-!
# The critical point of `g`, and the closed form `k = 3 cos θ*`

`GFunction` established that `g' < 0` on `(0, π / 16]` and `g' > 0` on
`[π / 8, ∞)`, so the minimum of `g` lies in `(π / 16, π / 8)`. At a critical
point we need `sin (θOf x) = sin (θOf (2 * x))` with the two angles distinct,
which forces them to be supplementary:

  `θOf x + θOf (2 * x) = π`.

Feeding that through `area (π - θ) = 2 * area θ` collapses everything to a
single transcendental equation in one variable,

  `F θ = 3 θ - 3 sin θ cos θ - π = 0`,                        (`F`)

whose root `θ*` is unique because `F' = 6 sin²θ > 0`. The value of `g` there is

  `k = (3 θ* - π) / sin θ* = 3 cos θ*`.                       (`g_θstar`)

Numerically `θ* = 1.30266283730…`, `k = 0.79479625381…`, and `1 / k =
1.25818408832…`, against the bound `4 / π = 1.27323954474…` published in
Cañete–Miranda–Vittone Theorem 3.16. Their Remark 3.17 notes the published
bound is not optimal and that the true threshold is `1 / k`, but does not
compute `k`; the closed form below appears to be new.

This file does *not* prove that the critical point is the minimum — that needs
the strict monotonicity of `g'` on `(π / 16, π / 8)`, deferred to a later file.
What is proved here is that `F` has a unique root, that `x* = area θ*` is a
critical point of `g`, and that `g x* = 3 cos θ*`.
-/

open Real Set Filter Topology

/-! ## The equation `F θ = 0` -/

/-- `F θ = 3 θ - 3 sin θ cos θ - π`. Its unique root in `(0, π)` is the
half-central-angle of the smaller cap at the critical point of `g`. -/
noncomputable def F (θ : ℝ) : ℝ := 3 * θ - 3 * (sin θ * cos θ) - π

/-- `F' θ = 6 sin²θ`, using `3 - 3(cos²θ - sin²θ) = 6 sin²θ`. -/
lemma hasDerivAt_F (θ : ℝ) : HasDerivAt F (6 * sin θ ^ 2) θ := by
  have h1 : HasDerivAt (fun t : ℝ => 3 * t) 3 θ := by
    simpa using (hasDerivAt_id θ).const_mul (3 : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => sin t * cos t)
      (cos θ * cos θ + sin θ * -sin θ) θ :=
    (Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_cos θ)
  have h3 := h1.sub (h2.const_mul (3 : ℝ))
  have h4 := h3.sub_const π
  refine h4.congr_deriv ?_
  linear_combination (-3 : ℝ) * sin_sq_add_cos_sq θ

lemma F_continuous : Continuous F := by
  unfold F
  fun_prop

/-- `F` is strictly increasing on `[0, π]` since `F' = 6 sin²θ > 0` inside. -/
lemma F_strictMonoOn : StrictMonoOn F (Icc 0 π) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 π)
  · exact F_continuous.continuousOn
  · intro x _
    exact (hasDerivAt_F x).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have := sin_pos_of_pos_of_lt_pi hx.1 hx.2
    positivity

lemma F_zero : F 0 = -π := by
  rw [F, sin_zero, cos_zero]
  ring

lemma F_pi_div_two : F (π / 2) = π / 2 := by
  rw [F, sin_pi_div_two, cos_pi_div_two]
  ring

/-! ## Existence and uniqueness of the root -/

lemma exists_F_root : ∃ θ ∈ Icc 0 (π / 2), F θ = 0 := by
  have hab : (0 : ℝ) ≤ π / 2 := by linarith [pi_pos]
  have hcont : ContinuousOn F (Icc 0 (π / 2)) := F_continuous.continuousOn
  have hmem : (0 : ℝ) ∈ Icc (F 0) (F (π / 2)) := by
    rw [F_zero, F_pi_div_two]
    exact ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  obtain ⟨θ, hθ, hval⟩ := intermediate_value_Icc hab hcont hmem
  exact ⟨θ, hθ, hval⟩

/-- The root of `F` in `(0, π / 2)`. -/
noncomputable def θstar : ℝ := exists_F_root.choose

lemma θstar_spec : F θstar = 0 := exists_F_root.choose_spec.2

lemma θstar_mem_Icc : θstar ∈ Icc 0 (π / 2) := exists_F_root.choose_spec.1

/-- The root is interior: `F 0 = -π < 0` and `F (π / 2) = π / 2 > 0`. -/
lemma θstar_mem : θstar ∈ Ioo 0 (π / 2) := by
  obtain ⟨hlo, hhi⟩ := θstar_mem_Icc
  constructor
  · rcases eq_or_lt_of_le hlo with heq | hlt
    · exfalso
      have := θstar_spec
      rw [← heq, F_zero] at this
      linarith [pi_pos]
    · exact hlt
  · rcases eq_or_lt_of_le hhi with heq | hlt
    · exfalso
      have := θstar_spec
      rw [heq, F_pi_div_two] at this
      linarith [pi_pos]
    · exact hlt

lemma θstar_pos : 0 < θstar := θstar_mem.1

lemma θstar_lt_pi : θstar < π := lt_trans θstar_mem.2 (by linarith [pi_pos])

lemma sin_θstar_pos : 0 < sin θstar :=
  sin_pos_of_pos_of_lt_pi θstar_pos θstar_lt_pi

/-- Uniqueness, from strict monotonicity of `F` on `[0, π]`. -/
lemma θstar_unique {θ : ℝ} (hmem : θ ∈ Icc 0 π) (hF : F θ = 0) : θ = θstar := by
  have hs : θstar ∈ Icc 0 π := ⟨le_of_lt θstar_pos, le_of_lt θstar_lt_pi⟩
  exact F_strictMonoOn.injOn hmem hs (by rw [hF, θstar_spec])

/-! ## The supplementary-angle identity

The defining equation of `θ*` is exactly the statement that the cap of area
`2 * area θ*` is the reflection `π - θ*` of the cap of area `area θ*`.
-/

/-- `area (π - θ) = (π - θ + sin θ cos θ) / (4 sin²θ)`. -/
lemma area_pi_sub {θ : ℝ} (_hθ : θ ∈ Ioo 0 π) :
    area (π - θ) = (π - θ + sin θ * cos θ) / (4 * sin θ ^ 2) := by
  rw [area, sin_pi_sub, cos_pi_sub]
  ring

/-- **The key substitution.** If `F θ = 0` then the supplementary cap has
exactly twice the area. -/
lemma area_pi_sub_eq_two_mul {θ : ℝ} (hθ : θ ∈ Ioo 0 π) (hF : F θ = 0) :
    area (π - θ) = 2 * area θ := by
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hne : (4 : ℝ) * sin θ ^ 2 ≠ 0 := by positivity
  have hpi : π = 3 * θ - 3 * (sin θ * cos θ) := by
    have := hF; rw [F] at this; linarith
  rw [area_pi_sub hθ, area, hpi]
  field_simp
  ring

/-! ## The critical point of `g` -/

/-- `x* = area θ*`, the area of the smaller cap at the critical point. -/
noncomputable def xstar : ℝ := area θstar

lemma xstar_pos : 0 < xstar := area_pos θstar_pos θstar_lt_pi

lemma θOf_xstar : θOf xstar = θstar :=
  θOf_area ⟨θstar_pos, θstar_lt_pi⟩

lemma pi_sub_θstar_mem : π - θstar ∈ Ioo 0 π :=
  ⟨by linarith [θstar_lt_pi], by linarith [θstar_pos]⟩

/-- The doubled area corresponds to the supplementary angle. -/
lemma θOf_two_mul_xstar : θOf (2 * xstar) = π - θstar := by
  have h : area (π - θstar) = 2 * xstar :=
    area_pi_sub_eq_two_mul ⟨θstar_pos, θstar_lt_pi⟩ θstar_spec
  have := θOf_area pi_sub_θstar_mem
  rwa [h] at this

/-- `x*` is a critical point of `g`: the two sines agree because the angles are
supplementary. -/
theorem g_deriv_xstar : 4 * sin (θOf xstar) - 4 * sin (θOf (2 * xstar)) = 0 := by
  rw [θOf_xstar, θOf_two_mul_xstar, sin_pi_sub]
  ring

/-! ## The value of `g` at the critical point -/

/-- **The closed form.** `g x* = 3 cos θ*`.

`g x* = 2 ell θ* - ell (π - θ*) = (2θ* - (π - θ*)) / sin θ* = (3θ* - π) / sin θ*`,
and `F θ* = 0` gives `3θ* - π = 3 sin θ* cos θ*`. -/
theorem g_θstar : g xstar = 3 * cos θstar := by
  have hs : sin θstar ≠ 0 := ne_of_gt sin_θstar_pos
  have harc1 : arc xstar = θstar / sin θstar := by
    rw [arc_eq, θOf_xstar, ell]
  have harc2 : arc (2 * xstar) = (π - θstar) / sin θstar := by
    rw [arc_eq, θOf_two_mul_xstar, ell, sin_pi_sub]
  have hpi : 3 * θstar - π = 3 * (sin θstar * cos θstar) := by
    have := θstar_spec; rw [F] at this; linarith
  rw [g, harc1, harc2]
  field_simp
  linarith [hpi]

/-! ## What remains

To conclude that `k := g x*` is the *minimum* of `g`, and hence that CMV's
cap-substitution argument succeeds for all `lam > 1 / k`, one still needs:

* `g'` strictly increasing on `(π / 16, π / 8)` — because `sin (θOf x)` rises
  while `sin (θOf (2 * x))` falls there — giving uniqueness of the critical
  point, and with `GFunction`'s sign results, that it is the global minimum;
* a rational certificate: `F` is strictly increasing, so exhibiting `t₀` with
  `F t₀ > 0` gives `θ* < t₀` and hence `k = 3 cos θ* > 3 cos t₀`. With
  `t₀ = 1.3027` this yields `k > 0.7946` and the threshold `lam ≥ 1.2584`.
-/
