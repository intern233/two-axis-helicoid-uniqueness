import TwoAxisHelicoid.ActualTorusManifoldImmersion
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped ContDiff Manifold
set_option maxHeartbeats 1000000

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- Smooth periodic maps descend smoothly in the actual quotient atlas. -/
theorem periodTorusLift_contMDiffAt_of_contDiffAt
    (L : PeriodPair) (F : ℂ → A)
    (hp : ∀ z ω₀, ω₀ ∈ L.lattice → F (z+ω₀) = F z)
    (q : PeriodTorus L) {n : WithTop ℕ∞}
    (hF : ContDiffAt ℝ n F (chartAt ℂ q q)) :
    ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,A) n (periodTorusLift L F hp) q := by
  have hcomp : periodTorusLift L F hp ∘ (chartAt ℂ q).symm = F := by
    rw [periodTorus_chart_symm_eq_projection L q]
    rfl
  apply contMDiffAt_iff.mpr
  refine ⟨?_,?_⟩
  · have h := periodTorusLift_continuousAt L F hp hF.continuousAt
    rwa [periodTorus_chart_representative L q] at h
  · have h := hF.contDiffWithinAt (s := range 𝓘(ℝ,ℂ))
    simpa only [mfld_simps, hcomp] using! h

/-- The manifold derivative of the descended map is computed from the
actual derivative on the cover, without an auxiliary immersion model. -/
theorem periodTorusLift_hasMFDerivAt
    (L : PeriodPair) (F : ℂ → A)
    (hp : ∀ z ω₀, ω₀ ∈ L.lattice → F (z+ω₀) = F z)
    (q : PeriodTorus L) {D : ℂ →L[ℝ] A}
    (hF : HasFDerivAt F D (chartAt ℂ q q)) :
    HasMFDerivAt 𝓘(ℝ,ℂ) 𝓘(ℝ,A) (periodTorusLift L F hp) q D := by
  have hcomp : periodTorusLift L F hp ∘ (chartAt ℂ q).symm = F := by
    rw [periodTorus_chart_symm_eq_projection L q]
    rfl
  refine ⟨?_,?_⟩
  · have h := periodTorusLift_continuousAt L F hp hF.continuousAt
    rwa [periodTorus_chart_representative L q] at h
  · simpa only [writtenInExtChartAt, mfld_simps, hcomp] using!
      hF.hasFDerivWithinAt (s := range 𝓘(ℝ,ℂ))

theorem periodTorusLift_mfderiv_injective
    (L : PeriodPair) (F : ℂ → A)
    (hp : ∀ z ω₀, ω₀ ∈ L.lattice → F (z+ω₀) = F z)
    (q : PeriodTorus L)
    (hF : DifferentiableAt ℝ F (chartAt ℂ q q))
    (hi : Function.Injective (fderiv ℝ F (chartAt ℂ q q))) :
    Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,A) (periodTorusLift L F hp) q) := by
  rw [(periodTorusLift_hasMFDerivAt L F hp q hF.hasFDerivAt).mfderiv]
  exact hi

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.periodTorusLift_contMDiffAt_of_contDiffAt
#print axioms TwoAxisHelicoid.periodTorusLift_hasMFDerivAt
#print axioms TwoAxisHelicoid.periodTorusLift_mfderiv_injective
