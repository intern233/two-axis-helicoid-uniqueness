import TwoAxisHelicoid.LogarithmicCuspMetric
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Measurable

namespace TwoAxisHelicoid
open Complex Set MeasureTheory Filter

/-- The area formula gives finite total horizontal cusp speed for
any injective finite-distortion chart on a finite-measure region. -/
theorem integrable_cusp_horizontal_speed {S : Set ℂ} (meas : MeasurableSet S)
    (finiteArea : volume S ≠ ⊤) {F : ℂ → ℂ}
    (diff : ∀ p ∈ S, DifferentiableAt ℝ F p) (inj : InjOn F S)
    (outside : ∀ p ∈ S, 2 < ‖F p‖) {K : ℝ}
    (distort : ∀ p ∈ S, ‖fderiv ℝ F p 1‖^2 ≤ K * |(fderiv ℝ F p).det|) :
    IntegrableOn (fun p => exteriorCuspDensity ‖F p‖ * ‖fderiv ℝ F p 1‖) S := by
  let J := fun p => |(fderiv ℝ F p).det| * (exteriorCuspDensity ‖F p‖)^2
  have area : IntegrableOn J S :=
    (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume meas
      (fun p hp => (diff p hp).hasFDerivAt.hasFDerivWithinAt) inj
      (fun z : ℂ => exteriorCuspDensity ‖z‖^2)).mp exterior_cusp_finite_area.integrableOn
  have major : IntegrableOn (fun p => 1 + K*J p) S :=
    (integrableOn_const finiteArea).add (area.const_mul K)
  have density : ContinuousOn (fun p => exteriorCuspDensity ‖F p‖) S := by
    intro p hp
    have atp := (diff p hp).continuousAt.norm
    have above := atp.eventually (lt_mem_nhds (outside p hp))
    have formula : (fun q => exteriorCuspDensity ‖F q‖) =ᶠ[nhds p]
        fun q => (‖F q‖ * Real.log ‖F q‖)⁻¹ := above.mono fun q h => ite_eq_left h
    have pos : 0 < ‖F p‖ := lt_trans (by norm_num) (outside p hp)
    have lp : 0 < Real.log ‖F p‖ := Real.log_pos (lt_trans (by norm_num) (outside p hp))
    exact ((atp.mul (atp.log pos.ne')).inv₀ (mul_pos pos lp).ne').congr_of_eventuallyEq
      formula |>.continuousWithinAt
  refine major.mono' ((density.aestronglyMeasurable meas).mul
    (measurable_fderiv_apply_const ℝ F (1:ℂ)).norm.aestronglyMeasurable) ?_
  apply (ae_restrict_iff' meas).mpr
  apply ae_of_all
  intro p hp
  let ρ := exteriorCuspDensity ‖F p‖
  let v := ‖fderiv ℝ F p 1‖
  have hv : 0 ≤ ρ*v := mul_nonneg (exteriorCuspDensity_nonneg _) (norm_nonneg _)
  have sq := mul_le_mul_of_nonneg_right (distort p hp) (sq_nonneg ρ)
  change ‖ρ*v‖ ≤ 1 + K*(|(fderiv ℝ F p).det| * ρ^2)
  rw [Real.norm_eq_abs,abs_of_nonneg hv]
  change v^2*ρ^2 ≤ _ at sq
  nlinarith [sq_nonneg (ρ*v-1/2)]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.integrable_cusp_horizontal_speed
