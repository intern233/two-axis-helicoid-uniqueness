import TwoAxisHelicoid.CertifiedSlopingHorizontalFlux
import TwoAxisHelicoid.ActualTorusRigidityHypotheses
import TwoAxisHelicoid.IntrinsicGaussPhaseRigidity
import TwoAxisHelicoid.IntrinsicLopezRosVariation

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace

/-- The ordinary three real coordinates of the certified Euclidean immersion. -/
noncomputable abbrev certifiedTorusPosition := fun x => WithLp.ofLp (certifiedTorusImmersion x)

/-- For the certified surface both the position and Gauss phases agree
with any other harmonic conformal solution with the same marked data. -/
theorem certified_marked_fixed_data_phase_rigidity (Y : PuncturedPeriodTorus certifiedPeriodPair → Fin 3 → ℝ)
    (hY : ∀ z ∉ certifiedPeriodPair.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback certifiedPeriodPair Y w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback certifiedPeriodPair Y) z)
    (hh : ∀ z ∉ certifiedPeriodPair.lattice, torusImmersionForms certifiedPeriodPair Y z 2 =
      torusImmersionForms certifiedPeriodPair certifiedTorusPosition z 2)
    (hlog : ∀ z ∉ certifiedPeriodPair.lattice, torusImmersionForms certifiedPeriodPair certifiedTorusPosition z 2 ≠ 0 →
      immersionGaussLog (torusImmersionForms certifiedPeriodPair Y) z =
        immersionGaussLog (torusImmersionForms certifiedPeriodPair certifiedTorusPosition) z) :
    ∃ θ : ℝ, ∃ d : Fin 3 → ℝ, (∀ q, Y q = verticalRotation (exp ((θ:ℂ)*I)) (certifiedTorusPosition q)+d) ∧
      ∀ z ∉ certifiedPeriodPair.lattice, nullGauss (torusImmersionForms certifiedPeriodPair Y z) =
        exp ((θ:ℂ)*I)*nullGauss (torusImmersionForms certifiedPeriodPair certifiedTorusPosition z) := by
  let p := certifiedClosedParameters
  have h := actual_torus_rigidity_hypotheses p.height_pos p.abscissa_mem (by norm_num : (1:ℝ) ≠ 0)
    p.vertical_closed p.horizontal_closed
  exact intrinsic_gauss_and_immersion_phase_rigidity certifiedPeriodPair certifiedTorusPosition Y h.1 hY h.2 hh hlog
    certified_torus_has_intrinsic_nonvertical_flux

/-- Equality of the actual marked Laurent principal parts suffices. -/
theorem certified_marked_fixed_parts_rigidity (Y : PuncturedPeriodTorus certifiedPeriodPair → Fin 3 → ℝ)
    (hY : ∀ z ∉ certifiedPeriodPair.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback certifiedPeriodPair Y w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback certifiedPeriodPair Y) z)
    (hH : CommonLaurentPartAt (fun z => torusImmersionForms certifiedPeriodPair certifiedTorusPosition z 2)
      (fun z => torusImmersionForms certifiedPeriodPair Y z 2) 0)
    (hΩ : ∀ z, CommonLaurentPartAt (immersionGaussLog (torusImmersionForms certifiedPeriodPair certifiedTorusPosition))
      (immersionGaussLog (torusImmersionForms certifiedPeriodPair Y)) z) :
    ∃ θ : ℝ, ∃ d : Fin 3 → ℝ, ∀ q, Y q = verticalRotation (exp ((θ:ℂ)*I)) (certifiedTorusPosition q)+d := by
  let p := certifiedClosedParameters
  have h := actual_torus_rigidity_hypotheses p.height_pos p.abscissa_mem (by norm_num : (1:ℝ) ≠ 0)
    p.vertical_closed p.horizontal_closed
  exact intrinsic_punctured_torus_fixed_parts_rigidity certifiedPeriodPair certifiedTorusPosition Y h.1 hY h.2 hH hΩ
    certified_torus_has_intrinsic_nonvertical_flux

/-- At the certified surface, genuine first-order closed periods force a
purely imaginary López–Ros velocity, without any finite closure hypothesis. -/
theorem certified_lopez_ros_velocity_pure_imaginary {k : ℝ → ℂ} {d : ℂ}
    (hk : HasDerivAt k d 0) (hk0 : k 0 = 1) (hclose : LopezRosClosedToFirstOrder certifiedPeriodPair certifiedTorusPosition k) :
    d.re = 0 := by
  let p := certifiedClosedParameters
  have h := actual_torus_rigidity_hypotheses p.height_pos p.abscissa_mem (by norm_num : (1:ℝ) ≠ 0)
    p.vertical_closed p.horizontal_closed
  exact intrinsic_lopez_ros_velocity_pure_imaginary certifiedPeriodPair certifiedTorusPosition h.1
    certified_torus_has_intrinsic_nonvertical_flux hk hk0 hclose

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_marked_fixed_data_phase_rigidity
#print axioms TwoAxisHelicoid.certified_marked_fixed_parts_rigidity
#print axioms TwoAxisHelicoid.certified_lopez_ros_velocity_pure_imaginary
