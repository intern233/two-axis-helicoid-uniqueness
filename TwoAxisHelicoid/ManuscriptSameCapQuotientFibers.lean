import TwoAxisHelicoid.ManuscriptQuotientGaussFibers
import TwoAxisHelicoid.ManuscriptSphericalCapMarking

namespace TwoAxisHelicoid
open Complex
open scoped OnePoint Topology

/-- The Gauss fibers of the original position in the rigid coordinates
of each marked spin cap, evaluated on the punctured quotient. -/
def HasMarkedQuotientGaussFibers (s : OriginalPositionallyAsymptoticHelicoid) : Prop :=
  HasCertifiedSpinCapGaussMarking s ∧
    ∀ S : ChartedSpace ℂ s.carrier, let _ := S
      ∀ (e : s.carrier ≃ₜ PuncturedPeriodTorus certifiedPeriodPair)
        (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)) (Z : ℂ → Fin 3 → ℝ)
        (hZ : TwoAxisHarmonicConformalImmersion certifiedPeriodPair Z) (c : ℝ),
        OriginalMarkedSpinCapData s certifiedClosedParameters.a c 1 e R Z hZ →
        ∀ x : s.carrier, let G := torusSphericalGauss certifiedPeriodPair (fun q => R (s.position (e.symm q)))
          (G (e x) = (↑(0 : ℂ) : OnePoint ℂ) ↔
            (e x).1 = periodTorusProjection certifiedPeriodPair (certifiedClosedParameters.a : ℂ)) ∧
          (G (e x) = ∞ ↔
            (e x).1 = periodTorusProjection certifiedPeriodPair (-(certifiedClosedParameters.a : ℂ)))

theorem marked_quotient_gauss_fibers_of_cover {s : OriginalPositionallyAsymptoticHelicoid}
    (given : HasSphericalGaussValuesOnCertifiedCap s) : HasMarkedQuotientGaussFibers s := by
  refine ⟨given.1,?_⟩
  intro S
  let _ := S
  refine fun e R Z hZ c cap x => ?_
  have fibers := given.2 S e R Z hZ c cap
  exact manuscript_rigidly_placed_gauss_fibers hZ fibers e.toEquiv s.position R cap.2.2.2.1 x

/-- Both original presentations have the two quotient fibers on the same
pointed cap, using the coordinates of its actual rigidly placed position. -/
theorem manuscript_C1_same_cap_quotient_gauss_fibers :
    AllManuscriptC1Surfaces HasMarkedQuotientGaussFibers ∧
      AllPlacedManuscriptC1Surfaces HasMarkedQuotientGaussFibers :=
  ⟨fun s => marked_quotient_gauss_fibers_of_cover (manuscript_C1_same_cap_spherical_gauss_markings.1 s),
    fun s g => marked_quotient_gauss_fibers_of_cover (manuscript_C1_same_cap_spherical_gauss_markings.2 s g)⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.marked_quotient_gauss_fibers_of_cover
#print axioms TwoAxisHelicoid.manuscript_C1_same_cap_quotient_gauss_fibers
