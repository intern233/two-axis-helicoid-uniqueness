import TwoAxisHelicoid.AsymptoticAxisThinTube
import TwoAxisHelicoid.ZeroFluxHorizontalCenter

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology

/-- The boundary flux hypothesis in Proposition 2.3 uses the integral of
the Euclidean unit conormal against arclength. A single translation and
a fixed rotation then work for every normal-tube width. -/
theorem zero_flux_helicoidal_end_arbitrarily_thin {R r : ℝ} (hR : 0 < R) (hr : R < r)
    {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ} (hf : Tendsto F (cobounded ℂ) (𝓝 0))
    (hhol : ∀ z : ℂ, R < ‖z‖ → DifferentiableAt ℂ F z)
    (hd : ∀ z : ℂ, R < ‖z‖ → HasFDerivAt X (nullRealDerivative
      (weierstrassTriple (exp (I*z+F z)) 1)) z)
    (hflux : ∀ j, (exteriorFluxCircle hR hr).spatialConormalFlux X j = 0) :
    ∃ b : Fin 3 → ℝ, ∀ ε : ℝ, 0 < ε → ∃ S : ℝ, ∀ z : ℂ, S < ‖z‖ →
      coordinateToTube (verticalRotation I (X z-b)) ∈ helicoidTubeEquiv.target ∧
      |helicoidSignedDistance (coordinateToTube (verticalRotation I (X z-b)))| ≤ ε := by
  obtain ⟨c,d,hc,hd'⟩ := zero_flux_height_end_horizontal_center hR hr hf hhol hd hflux
  obtain ⟨a,ha⟩ := height_end_third_coordinate hR.le hd
  let b : Fin 3 → ℝ := ![c,d,a]
  refine ⟨b,height_end_asymptotic_axis_arbitrarily_thin (X := fun z => X z-b) R
    (fun z hz => (hd z hz).sub_const b) (fun z hz => ?_) hf ?_ ?_⟩
  · change X z 2-a = z.re
    rw [ha z hz,add_sub_cancel_right]
  · simpa only [Pi.sub_apply,Matrix.cons_val_zero,sub_self,b] using hc.sub_const c
  · simpa only [Pi.sub_apply,Matrix.cons_val_one,Matrix.cons_val_zero,sub_self,b] using hd'.sub_const d

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.zero_flux_helicoidal_end_arbitrarily_thin
