import TwoAxisHelicoid.CertifiedMarkedFluxRigidity
import TwoAxisHelicoid.TorusSphericalGaussRigidity
import TwoAxisHelicoid.LopezRosRotationTangent

namespace TwoAxisHelicoid
open Complex InnerProductSpace

/-- On the certified surface the fixed-data assertion rotates the entire
spherical Gauss map, including both vertical normal directions. -/
theorem certified_fixed_data_spherical_rigidity (Y : PuncturedPeriodTorus certifiedPeriodPair → Fin 3 → ℝ)
    (hY : ∀ z ∉ certifiedPeriodPair.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback certifiedPeriodPair Y w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback certifiedPeriodPair Y) z)
    (hh : ∀ z ∉ certifiedPeriodPair.lattice, torusImmersionForms certifiedPeriodPair Y z 2 =
      torusImmersionForms certifiedPeriodPair certifiedTorusPosition z 2)
    (hΩ : ∀ z ∉ certifiedPeriodPair.lattice, torusImmersionForms certifiedPeriodPair certifiedTorusPosition z 2 ≠ 0 →
      immersionGaussLog (torusImmersionForms certifiedPeriodPair Y) z =
        immersionGaussLog (torusImmersionForms certifiedPeriodPair certifiedTorusPosition) z) :
    ∃ θ : ℝ, ∃ d : Fin 3 → ℝ, (∀ q, Y q = verticalRotation (exp ((θ:ℂ)*I)) (certifiedTorusPosition q)+d) ∧
      ∀ q, torusSphericalGauss certifiedPeriodPair Y q =
        OnePoint.map (exp ((θ:ℂ)*I)*·) (torusSphericalGauss certifiedPeriodPair certifiedTorusPosition q) := by
  let p := certifiedClosedParameters
  have h := actual_torus_rigidity_hypotheses p.height_pos p.abscissa_mem (by norm_num : (1:ℝ) ≠ 0)
    p.vertical_closed p.horizontal_closed
  obtain ⟨θ,d,he,_⟩ := certified_marked_fixed_data_phase_rigidity Y hY hh hΩ
  exact ⟨θ,d,he,torusSphericalGauss_rotate _ _ _ h.1 hY (by simp [Complex.norm_exp]) he⟩

/-- First-order closed López–Ros variations are exactly the rotation
directions on the certified surface, for every differentiable multiplier. -/
theorem certified_lopez_ros_closure_iff_rotation {k : ℝ → ℂ} {d : ℂ} (hk : HasDerivAt k d 0) (hk0 : k 0 = 1) :
    LopezRosClosedToFirstOrder certifiedPeriodPair certifiedTorusPosition k ↔ d.re = 0 := by
  let p := certifiedClosedParameters
  have h := actual_torus_rigidity_hypotheses p.height_pos p.abscissa_mem (by norm_num : (1:ℝ) ≠ 0)
    p.vertical_closed p.horizontal_closed
  exact lopez_ros_first_order_closure_iff_rotation _ _ h.1 certified_torus_has_intrinsic_nonvertical_flux hk hk0

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_fixed_data_spherical_rigidity
#print axioms TwoAxisHelicoid.certified_lopez_ros_closure_iff_rotation
