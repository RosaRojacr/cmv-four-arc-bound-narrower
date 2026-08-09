import Section2
open Real Set Filter Topology

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

lemma area_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) : 0 < area θ := by
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi h0 hπ
  have hnum : 0 < θ - sin θ * cos θ := by
    nlinarith [sin_lt h0, neg_one_le_cos θ, cos_le_one θ, sq_nonneg (sin θ)]
  rw [area]
  positivity

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
