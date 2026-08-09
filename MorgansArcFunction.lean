/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Morgan's arc function

For a fixed chord of length `1`, let `arc x` denote the length of the circular
arc standing on that chord and enclosing area `x`. This function appears in
Frank Morgan, *Geometric Measure Theory: A Beginner's Guide*, 4th ed., §15.5,
where it is recorded as convex on `[0, π / 8]`, concave on `[π / 8, ∞)`, with
`arc (π / 8) = π / 2` and `arc' (π / 8) = 2`.

It is used in:

* A. Cañete, M. Miranda Jr., D. Vittone, *Some isoperimetric problems in planes
  with density*, J. Geom. Anal. **20** (2010) 243–290 (arXiv:0906.1256), in the
  proof of Theorem 3.16, where the cap-substitution argument reduces to showing
  `2 * arc x - arc (2 * x) > 1 / lam`;
* J. Díaz, N. Harman, S. Howe, D. Thompson, *Isoperimetric problems in sectors
  with density*, Adv. Geom. **12** (2012) 589–619 (arXiv:1012.0450).

Mathlib does not have `arc`, so this file constructs it from scratch as the
inverse of the segment-area parametrisation, and proves the identity

  `arc' x = 2 * sin (θOf x)`                       (`hasDerivAt_arc`)

where `θOf x` is the half-central-angle of the arc enclosing area `x`. Since the
chord has length `1`, we have `sin (θOf x) = 1 / (2 * r)`, so the identity says
that **the marginal length cost of area equals the curvature of the arc** — the
same fact that makes the isoperimetric Lagrange multiplier coincide with the
geometric curvature.

The identity is what makes the rest tractable: `arc''` has the sign of `cos θ`,
so Morgan's convexity and concavity become corollaries rather than hypotheses,
and the minimisation of `2 * arc x - arc (2 * x)` collapses to a single
transcendental equation in one variable.

## Main definitions

* `ell θ` — arc length of a unit-chord segment with half-central-angle `θ`
* `area θ` — the area it encloses
* `θOf x` — the inverse of `area`, defined for `x > 0`
* `arc x` — `ell (θOf x)`

## Main results

* `area_strictMonoOn`, `area_surjOn` — `area` is a bijection `(0, π) → (0, ∞)`
* `hasDerivAt_arc` — the derivative identity

-/

open Real Set Filter Topology

/-! ## A positivity lemma

Everything below rests on `sin θ - θ cos θ > 0` on `(0, π)`: it is the common
numerator of both `ell'` and `area'`, and its non-vanishing is what lets the two
cancel in `hasDerivAt_arc`.
-/

/-- On `(0, π)` we have `θ cos θ < sin θ`. Below `π / 2` this is `θ < tan θ`;
above `π / 2` the cosine is negative and the claim is immediate. -/
lemma sin_sub_mul_cos_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    0 < sin θ - θ * cos θ := by
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi h0 hπ
  rcases le_or_gt θ (π / 2) with h | h
  · rcases eq_or_lt_of_le h with heq | hlt
    · rw [heq]; simp
    · have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hlt⟩
      have ht : θ < tan θ := lt_tan h0 hlt
      rw [tan_eq_sin_div_cos] at ht
      have := (lt_div_iff₀ hc).mp ht
      linarith
  · have hπ' : θ < π + π / 2 := by linarith [pi_pos]
    have hc : cos θ < 0 := cos_neg_of_pi_div_two_lt_of_lt h hπ'
    nlinarith [mul_pos h0 (neg_pos.mpr hc)]

/-! ## The parametrisation

A circular segment on a chord of length `1` with half-central-angle `θ ∈ (0, π)`
has radius `1 / (2 sin θ)`. Its arc length and enclosed area are `ell θ` and
`area θ` below. At `θ = π / 2` the segment is a half-disc of radius `1/2`, giving
`ell = π / 2` and `area = π / 8`.
-/

/-- Arc length of a unit-chord circular segment with half-central-angle `θ`. -/
noncomputable def ell (θ : ℝ) : ℝ := θ / sin θ

/-- Area enclosed by a unit-chord circular segment with half-central-angle `θ`. -/
noncomputable def area (θ : ℝ) : ℝ := (θ - sin θ * cos θ) / (4 * sin θ ^ 2)

lemma hasDerivAt_ell {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    HasDerivAt ell ((sin θ - θ * cos θ) / sin θ ^ 2) θ := by
  have hs : sin θ ≠ 0 := ne_of_gt (sin_pos_of_pos_of_lt_pi h0 hπ)
  have h := HasDerivAt.div (hasDerivAt_id θ) (Real.hasDerivAt_sin θ) hs
  simp only [id_eq, one_mul] at h
  exact h

/-- The quotient rule gives a numerator `8 sin⁴θ - 8 sin θ cos θ (θ - sin θ cos θ)`,
which collapses to `sin θ - θ cos θ` after applying `sin²θ + cos²θ = 1`. Note the
same numerator as `ell'` — this is the cancellation exploited later. -/
lemma hasDerivAt_area {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    HasDerivAt area ((sin θ - θ * cos θ) / (2 * sin θ ^ 3)) θ := by
  have hs : (0:ℝ) < sin θ := sin_pos_of_pos_of_lt_pi h0 hπ
  have hs' : sin θ ≠ 0 := ne_of_gt hs
  have hd : (4 : ℝ) * sin θ ^ 2 ≠ 0 := by positivity
  have hnum : HasDerivAt (fun t => t - sin t * cos t)
      (1 - (cos θ * cos θ + sin θ * -sin θ)) θ :=
    (hasDerivAt_id θ).sub ((Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_cos θ))
  have hden : HasDerivAt (fun t => 4 * sin t ^ 2) (4 * (2 * sin θ * cos θ)) θ := by
    have := ((Real.hasDerivAt_sin θ).pow 2)
    simpa using this.const_mul 4
  have h := hnum.div hden hd
  have harea : area = ((fun t => t - sin t * cos t) / fun t : ℝ => 4 * sin t ^ 2) := rfl
  rw [harea]
  refine h.congr_deriv ?_
  have hcos : cos θ ^ 2 = 1 - sin θ ^ 2 := by nlinarith [sin_sq_add_cos_sq θ]
  field_simp
  ring_nf
  rw [hcos]
  ring

lemma area_deriv_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    0 < (sin θ - θ * cos θ) / (2 * sin θ ^ 3) := by
  have hs : (0:ℝ) < sin θ := sin_pos_of_pos_of_lt_pi h0 hπ
  have := sin_sub_mul_cos_pos h0 hπ
  positivity

lemma area_strictMonoOn : StrictMonoOn area (Ioo 0 π) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioo 0 π)
  · exact fun x hx => ((hasDerivAt_area hx.1 hx.2).continuousAt).continuousWithinAt
  · intro x hx
    rw [isOpen_Ioo.interior_eq] at hx
    exact (hasDerivAt_area hx.1 hx.2).hasDerivWithinAt
  · intro x hx
    rw [isOpen_Ioo.interior_eq] at hx
    exact area_deriv_pos hx.1 hx.2

/-! ## Endpoint behaviour

With `area_strictMonoOn`, these give that `area` is a strictly increasing
bijection from `(0, π)` onto `(0, ∞)`.
-/

/-- `area` is positive on `(0, π)`. -/
lemma area_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) : 0 < area θ := by
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi h0 hπ
  have hnum : 0 < θ - sin θ * cos θ := by
    nlinarith [sin_lt h0, neg_one_le_cos θ, cos_le_one θ, sq_nonneg (sin θ)]
  rw [area]
  positivity

/-- On `(0, 1]` the area is bounded above by `θ`. The constants come from
`sin θ > θ - θ³/6`: the numerator is `< 2θ³/3` and `4 sin²θ > 25θ²/9`, so
`area θ < 6θ/25`. -/
lemma area_lt_self {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1) : area θ < θ := by
  have hc : θ^3 ≤ θ := by nlinarith [sq_nonneg θ, mul_pos h0 h0]
  have hs : 5*θ/6 < sin θ := by
    have := sin_gt_sub_cube h0
    linarith
  have hsq : 25*θ^2/36 < sin θ^2 := by nlinarith
  have hnum : θ - sin θ * cos θ < 2*θ^3/3 := by
    have h2 : sin (2*θ) > 2*θ - (2*θ)^3/6 := sin_gt_sub_cube (by linarith)
    rw [sin_two_mul] at h2
    nlinarith
  have hden : 0 < 4 * sin θ^2 := by nlinarith
  rw [area, div_lt_iff₀ hden]
  nlinarith

/-- `area θ → 0` as `θ → 0⁺`, by squeezing between `0` and `θ`. -/
lemma area_tendsto_zero : Tendsto area (𝓝[>] 0) (𝓝 0) := by
  have hmem : ∀ᶠ θ : ℝ in 𝓝[>] 0, 0 < θ ∧ θ ≤ 1 := by
    filter_upwards [eventually_mem_nhdsWithin,
      (eventually_le_nhds (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with θ ha hb
    exact ⟨ha, hb⟩
  apply squeeze_zero'
  · filter_upwards [hmem] with θ h
    exact le_of_lt (area_pos h.1 (by linarith [pi_gt_three]))
  · filter_upwards [hmem] with θ h
    exact le_of_lt (area_lt_self h.1 h.2)
  · exact tendsto_id.mono_left nhdsWithin_le_nhds

/-- `area θ → ∞` as `θ → π⁻`: the numerator tends to `π > 0` while `4 sin²θ`
tends to `0` from above. -/
lemma area_tendsto_atTop : Tendsto area (𝓝[<] π) atTop := by
  have hnum : Tendsto (fun θ : ℝ => θ - sin θ * cos θ) (𝓝[<] π) (𝓝 π) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    exact (continuous_id.sub (continuous_sin.mul continuous_cos)).tendsto' π π (by simp)
  have h0 : ∀ᶠ θ : ℝ in 𝓝[<] π, 0 < θ :=
    (eventually_gt_nhds pi_pos).filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ θ : ℝ in 𝓝[<] π, θ < π := eventually_mem_nhdsWithin
  have hden : Tendsto (fun θ : ℝ => 4 * sin θ ^ 2) (𝓝[<] π) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      exact (continuous_const.mul (continuous_sin.pow 2)).tendsto' π 0 (by simp)
    · filter_upwards [h0, hlt] with θ ha hb
      have := sin_pos_of_pos_of_lt_pi ha hb
      simp only [mem_Ioi]
      positivity
  have key := Filter.Tendsto.pos_mul_atTop pi_pos hnum hden.inv_tendsto_nhdsGT_zero
  simp only [Pi.inv_apply] at key
  have harea : area = fun θ : ℝ => (θ - sin θ * cos θ) * (4 * sin θ ^ 2)⁻¹ := by
    funext θ; rw [area, div_eq_mul_inv]
  rw [harea]
  exact key

/-- `area` is continuous on `(0, π)` — needed for the intermediate value step. -/
lemma area_continuousOn : ContinuousOn area (Ioo 0 π) :=
  fun _θ hθ => (hasDerivAt_area hθ.1 hθ.2).continuousAt.continuousWithinAt

/-- `area` maps `(0, π)` onto `(0, ∞)`: the two limits supply points on either
side of any target, and the intermediate value theorem does the rest. -/
lemma area_surjOn : SurjOn area (Ioo 0 π) (Ioi 0) := by
  intro y hy
  simp only [mem_Ioi] at hy
  obtain ⟨a, haI, ha⟩ : ∃ a, a ∈ Ioo (0:ℝ) π ∧ area a < y := by
    have h1 : ∀ᶠ θ : ℝ in 𝓝[>] 0, area θ < y :=
      area_tendsto_zero.eventually (eventually_lt_nhds hy)
    have h2 : ∀ᶠ θ : ℝ in 𝓝[>] 0, θ ∈ Ioo (0:ℝ) π := by
      filter_upwards [eventually_mem_nhdsWithin,
        (eventually_lt_nhds pi_pos).filter_mono nhdsWithin_le_nhds] with θ ha hb
      exact ⟨ha, hb⟩
    exact (h2.and h1).exists
  obtain ⟨b, hbI, hb⟩ : ∃ b, b ∈ Ioo (0:ℝ) π ∧ y < area b := by
    have h1 : ∀ᶠ θ : ℝ in 𝓝[<] π, y < area θ :=
      area_tendsto_atTop.eventually_gt_atTop y
    have h2 : ∀ᶠ θ : ℝ in 𝓝[<] π, θ ∈ Ioo (0:ℝ) π := by
      filter_upwards [eventually_mem_nhdsWithin,
        (eventually_gt_nhds pi_pos).filter_mono nhdsWithin_le_nhds] with θ ha hb
      exact ⟨hb, ha⟩
    exact (h2.and h1).exists
  have hsub : uIcc a b ⊆ Ioo (0:ℝ) π := ordConnected_Ioo.uIcc_subset haI hbI
  have hcont : ContinuousOn area (uIcc a b) := area_continuousOn.mono hsub
  have hmem : y ∈ uIcc (area a) (area b) := by
    rw [Set.mem_uIcc]; left; exact ⟨le_of_lt ha, le_of_lt hb⟩
  obtain ⟨c, hc, hcy⟩ := intermediate_value_uIcc hcont hmem
  exact ⟨c, hsub hc, hcy⟩

/-! ## The inverse `θOf`, and `arc` -/

/-- `θOf x` is the unique `θ ∈ (0, π)` with `area θ = x`, for `x > 0`.
The junk value `π / 2` for `x ≤ 0` is never used. -/
noncomputable def θOf (x : ℝ) : ℝ :=
  if h : 0 < x then (area_surjOn (mem_Ioi.mpr h)).choose else π / 2

lemma θOf_mem {x : ℝ} (hx : 0 < x) : θOf x ∈ Ioo 0 π := by
  rw [θOf, dif_pos hx]
  exact (area_surjOn (mem_Ioi.mpr hx)).choose_spec.1

lemma area_θOf {x : ℝ} (hx : 0 < x) : area (θOf x) = x := by
  rw [θOf, dif_pos hx]
  exact (area_surjOn (mem_Ioi.mpr hx)).choose_spec.2

/-- Uniqueness: `θOf` really is the inverse on `(0, π)`. -/
lemma θOf_area {θ : ℝ} (hθ : θ ∈ Ioo 0 π) : θOf (area θ) = θ := by
  have hpos : 0 < area θ := area_pos hθ.1 hθ.2
  have h1 : θOf (area θ) ∈ Ioo 0 π := θOf_mem hpos
  have h2 : area (θOf (area θ)) = area θ := area_θOf hpos
  exact area_strictMonoOn.injOn h1 hθ h2

/-- **Morgan's arc function**: the length of a unit-chord circular arc
enclosing area `x`. -/
noncomputable def arc (x : ℝ) : ℝ := ell (θOf x)

lemma arc_eq (x : ℝ) : arc x = ell (θOf x) := rfl

/-- `θOf` inherits strict monotonicity from `area`. -/
lemma θOf_strictMonoOn : StrictMonoOn θOf (Ioi 0) := by
  intro a ha b hb hab
  simp only [mem_Ioi] at ha hb
  rw [← area_strictMonoOn.lt_iff_lt (θOf_mem ha) (θOf_mem hb)] at *
  rwa [area_θOf ha, area_θOf hb]

/-- The image of `(0, ∞)` under `θOf` is all of `(0, π)`. -/
lemma θOf_image : Ioo 0 π ⊆ θOf '' (Ioi 0) := by
  intro θ hθ
  exact ⟨area θ, mem_Ioi.mpr (area_pos hθ.1 hθ.2), θOf_area hθ⟩

lemma θOf_continuousAt {x : ℝ} (hx : 0 < x) : ContinuousAt θOf x := by
  refine θOf_strictMonoOn.continuousAt_of_image_mem_nhds ?_ ?_
  · exact Ioi_mem_nhds hx
  · exact mem_of_superset (isOpen_Ioo.mem_nhds (θOf_mem hx)) θOf_image

/-! ## The derivative identity -/

/-- The cancellation: the common factor `sin θ - θ cos θ` in `ell'` and `area'`
divides out, leaving `2 sin θ`. -/
lemma ell_div_area_deriv {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    ((sin θ - θ * cos θ) / sin θ ^ 2)
      / ((sin θ - θ * cos θ) / (2 * sin θ ^ 3)) = 2 * sin θ := by
  have hs : (0:ℝ) < sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hk : 0 < sin θ - θ * cos θ := sin_sub_mul_cos_pos hθ.1 hθ.2
  have h1 : sin θ ≠ 0 := ne_of_gt hs
  have h2 : sin θ - θ * cos θ ≠ 0 := ne_of_gt hk
  field_simp

/-- **The key identity.** `arc' x = 2 sin (θOf x)`.

The inverse function theorem gives `θOf' = (area')⁻¹`; the chain rule gives
`arc' = ell' · θOf'`; and the common factor `sin θ - θ cos θ` cancels.

Since the chord has length `1` we have `sin (θOf x) = 1 / (2 r)`, so this says
`arc' x = 1 / r`: the marginal length cost of area is the curvature of the arc.

Two consequences used downstream: `arc' (π / 8) = 2`, because `θOf (π / 8) = π / 2`;
and `arc''` has the sign of `cos (θOf x)`, giving Morgan's convexity on
`[0, π / 8]` and concavity on `[π / 8, ∞)`. -/
theorem hasDerivAt_arc {x : ℝ} (hx : 0 < x) :
    HasDerivAt arc (2 * sin (θOf x)) x := by
  have hθ : θOf x ∈ Ioo 0 π := θOf_mem hx
  have hs : (0:ℝ) < sin (θOf x) := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hk : 0 < sin (θOf x) - θOf x * cos (θOf x) := sin_sub_mul_cos_pos hθ.1 hθ.2
  set A := (sin (θOf x) - θOf x * cos (θOf x)) / (2 * sin (θOf x) ^ 3) with hAdef
  have hAne : A ≠ 0 := by rw [hAdef]; positivity
  have hfwd : HasDerivAt area A (θOf x) := hasDerivAt_area hθ.1 hθ.2
  have hloc : ∀ᶠ y in 𝓝 x, area (θOf y) = y := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact area_θOf hy
  have hθderiv : HasDerivAt θOf A⁻¹ x :=
    HasDerivAt.of_local_left_inverse (f := area) (θOf_continuousAt hx) hfwd hAne hloc
  have hchain := (hasDerivAt_ell hθ.1 hθ.2).comp x hθderiv
  have hc : (sin (θOf x) - θOf x * cos (θOf x)) / sin (θOf x) ^ 2 * A⁻¹
      = 2 * sin (θOf x) := by
    rw [hAdef]
    have h1 : sin (θOf x) ≠ 0 := ne_of_gt hs
    have h2 : sin (θOf x) - θOf x * cos (θOf x) ≠ 0 := ne_of_gt hk
    field_simp
  rw [hc] at hchain
  exact hchain
