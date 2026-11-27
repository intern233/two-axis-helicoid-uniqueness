import TwoAxisHelicoid.ClosedPeriodParameters
import TwoAxisHelicoid.ActualTorusImmersion
import TwoAxisHelicoid.PeriodTorusTopology
import TwoAxisHelicoid.ActualGlobalEndLength

namespace TwoAxisHelicoid
open Complex Set Filter InnerProductSpace
open scoped Topology

noncomputable def certifiedPeriodPair : PeriodPair :=
  rhombicPeriodPair certifiedClosedParameters.t certifiedClosedParameters.height_pos

/-- An actual map from the certified punctured torus to Euclidean three-space. -/
noncomputable def certifiedTorusImmersion : PuncturedPeriodTorus certifiedPeriodPair →
    EuclideanSpace ℝ (Fin 3) := fun q => coordinateToEuclidean
  (actualTorusImmersion certifiedClosedParameters.height_pos certifiedClosedParameters.abscissa_mem
    (by norm_num : (1 : ℝ) ≠ 0) certifiedClosedParameters.vertical_closed
    certifiedClosedParameters.horizontal_closed q.1)

theorem certifiedTorusImmersion_continuous : Continuous certifiedTorusImmersion :=
  coordinateToEuclidean.continuous.comp (actualTorusImmersion_continuous_punctured
    certifiedClosedParameters.height_pos certifiedClosedParameters.abscissa_mem
    (by norm_num : (1 : ℝ) ≠ 0) certifiedClosedParameters.vertical_closed
    certifiedClosedParameters.horizontal_closed)

/-- Existence now includes one global primitive of the actual forms on the
entire lattice complement, with genuine lattice periodicity and descent.
Embeddedness and the helicoidal asymptotic theorem are separate obligations. -/
theorem exists_global_closed_conformal_harmonic_immersion :
    ∃ (p : ClosedPeriodParameters) (X : PeriodTorus (rhombicPeriodPair p.t p.height_pos) → Fin 3 → ℝ),
      Continuous (fun q : PuncturedPeriodTorus (rhombicPeriodPair p.t p.height_pos) => X q.1) ∧
      AnalyticOnNhd ℝ (X ∘ periodTorusProjection (rhombicPeriodPair p.t p.height_pos))
        (rhombicPeriodPair p.t p.height_pos).latticeᶜ ∧
      HarmonicOnNhd (X ∘ periodTorusProjection (rhombicPeriodPair p.t p.height_pos))
        (rhombicPeriodPair p.t p.height_pos).latticeᶜ ∧
      ∀ z ∉ (rhombicPeriodPair p.t p.height_pos).lattice,
        HasFDerivAt (X ∘ periodTorusProjection (rhombicPeriodPair p.t p.height_pos))
          (nullRealDerivative (coordinateData p.t p.a 1 p.height_pos z)) z ∧
        Function.Injective (fderiv ℝ (X ∘ periodTorusProjection (rhombicPeriodPair p.t p.height_pos)) z) ∧
        0 < nullMetric (coordinateData p.t p.a 1 p.height_pos z) := by
  let p := certifiedClosedParameters
  let X := actualTorusImmersion p.height_pos p.abscissa_mem (by norm_num : (1 : ℝ) ≠ 0)
    p.vertical_closed p.horizontal_closed
  have h := actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem
    (by norm_num : (1 : ℝ) ≠ 0) p.vertical_closed p.horizontal_closed
  refine ⟨p,X,actualTorusImmersion_continuous_punctured p.height_pos p.abscissa_mem
    (by norm_num : (1 : ℝ) ≠ 0) p.vertical_closed p.horizontal_closed,h.2.1,h.2.2.1,?_⟩
  intro z hz
  exact ⟨(h.2.2.2 z hz).1,(h.2.2.2 z hz).2.1,(h.2.2.2 z hz).2.2.1⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.certifiedTorusImmersion
#print axioms TwoAxisHelicoid.exists_global_closed_conformal_harmonic_immersion
