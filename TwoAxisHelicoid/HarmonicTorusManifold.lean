import TwoAxisHelicoid.PeriodicManifoldDifferential
import TwoAxisHelicoid.HarmonicNullLift
import Mathlib.Analysis.Complex.Harmonic.Analytic

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace
open scoped ContDiff Manifold

theorem periodTorus_chart_off_lattice {L : PeriodPair} {q : PeriodTorus L}
    (hq : q ≠ 0) : chartAt ℂ q q ∉ L.lattice := by
  intro h
  apply hq
  rw [← periodTorus_chart_representative L q]
  exact (periodTorusProjection_eq_zero L _).mpr h

/-- Every actual harmonic two-axis immersion is real analytic in the
original quotient atlas, for any integer branch of its later reduction. -/
theorem TwoAxisHarmonicConformalImmersion.torus_contMDiffAt
    {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X)
    (hp : ∀ z ω₀, ω₀ ∈ L.lattice → X (z+ω₀) = X z)
    {q : PeriodTorus L} (hq : q ≠ 0) :
    ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ω (periodTorusLift L X hp) q := by
  apply periodTorusLift_contMDiffAt_of_contDiffAt
  apply contDiffAt_pi.mpr
  intro j
  exact (HarmonicAt.analyticAt (hX.harmonic _ (periodTorus_chart_off_lattice hq) j)).contDiffAt

theorem TwoAxisHarmonicConformalImmersion.torus_hasMFDerivAt
    {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X)
    (hp : ∀ z ω₀, ω₀ ∈ L.lattice → X (z+ω₀) = X z)
    {q : PeriodTorus L} (hq : q ≠ 0) :
    HasMFDerivAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) (periodTorusLift L X hp) q
      (nullRealDerivative (puncturedImmersionCoefficient L X (chartAt ℂ q q))) :=
  periodTorusLift_hasMFDerivAt L X hp q
    (puncturedImmersionCoefficient_hasFDerivAt hX (periodTorus_chart_off_lattice hq))

theorem TwoAxisHarmonicConformalImmersion.torus_mfderiv_injective
    {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X)
    (hp : ∀ z ω₀, ω₀ ∈ L.lattice → X (z+ω₀) = X z)
    {q : PeriodTorus L} (hq : q ≠ 0) :
    Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) (periodTorusLift L X hp) q) :=
  periodTorusLift_mfderiv_injective L X hp q
    (hX.differentiable _ (periodTorus_chart_off_lattice hq))
    (hX.immersion _ (periodTorus_chart_off_lattice hq))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.TwoAxisHarmonicConformalImmersion.torus_contMDiffAt
#print axioms TwoAxisHelicoid.TwoAxisHarmonicConformalImmersion.torus_hasMFDerivAt
#print axioms TwoAxisHelicoid.TwoAxisHarmonicConformalImmersion.torus_mfderiv_injective
