import TwoAxisHelicoid.HeightEndProper

namespace TwoAxisHelicoid
open Complex Filter Bornology
open scoped Topology

theorem height_normalized_helicoidal_end_tendsto
    {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ} (α b R₀ : ℝ)
    (hX : ∀ z : ℂ, R₀ < ‖z‖ → HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*α*z+F z)) 1)) z)
    (hheight : ∀ z : ℂ, R₀ < ‖z‖ → X z 2 = z.re+b)
    (hF : Tendsto F (cobounded ℂ) (𝓝 0)) :
    Tendsto X (cobounded ℂ) (cobounded (Fin 3 → ℝ)) := by
  obtain ⟨Y,hY,hRY,hsmall⟩ := helicoidal_correction_small_phase hF R₀
  apply tendsto_norm_atTop_iff_cobounded.mp
  apply tendsto_atTop.mpr
  intro B
  obtain ⟨D,_,hD⟩ := height_end_bounded_image_parameter_bound α b R₀ Y hY.le hRY hX hheight hsmall
    (show 0 ≤ max B 0 from le_max_right _ _)
  filter_upwards [eventually_cobounded_le_norm (E := ℂ) (max (R₀+1) (D+1))] with z hz
  have hRz : R₀ < ‖z‖ := by linarith [le_max_left (R₀+1) (D+1)]
  by_contra h
  have hbound := hD z hRz ((not_le.mp h).le.trans (le_max_left B 0))
  linarith [le_max_right (R₀+1) (D+1)]

theorem vertical_quarter_turn_norm (v : Fin 3 → ℝ) : ‖verticalRotation I v‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro j
    fin_cases j
    · simpa [verticalRotation_apply] using norm_le_pi_norm v 1
    · simpa [verticalRotation_apply] using norm_le_pi_norm v 0
    · simpa [verticalRotation_apply] using norm_le_pi_norm v 2
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (verticalRotation I v))).mpr
    intro j
    fin_cases j
    · simpa [verticalRotation_apply] using norm_le_pi_norm (verticalRotation I v) 1
    · simpa [verticalRotation_apply] using norm_le_pi_norm (verticalRotation I v) 0
    · simpa [verticalRotation_apply] using norm_le_pi_norm (verticalRotation I v) 2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.height_normalized_helicoidal_end_tendsto
