import TwoAxisHelicoid.ManuscriptC1PredicateTransport
import TwoAxisHelicoid.ManuscriptSphericalGaussFibers
import TwoAxisHelicoid.OriginalSpinCapGaussMarking

namespace TwoAxisHelicoid
open Complex Set
open scoped OnePoint Topology

/-- The existing certified marking, together with the sphere values on every actual cap
carrying that marking. The universal clause applies to the very cap in the first clause. -/
def HasSphericalGaussValuesOnCertifiedCap (s : OriginalPositionallyAsymptoticHelicoid) : Prop :=
  HasCertifiedSpinCapGaussMarking s ∧
    ∀ S : ChartedSpace ℂ s.carrier, let _ := S
      ∀ (e : s.carrier ≃ₜ PuncturedPeriodTorus certifiedPeriodPair)
        (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)) (Z : ℂ → Fin 3 → ℝ)
        (hZ : TwoAxisHarmonicConformalImmersion certifiedPeriodPair Z) (c : ℝ),
        OriginalMarkedSpinCapData s certifiedClosedParameters.a c 1 e R Z hZ →
        PhysicalSphericalGaussDivisor certifiedClosedParameters.t certifiedClosedParameters.a
          certifiedClosedParameters.height_pos Z

theorem certified_cap_gives_physical_spherical_gauss (s : OriginalPositionallyAsymptoticHelicoid)
    (marked : HasCertifiedSpinCapGaussMarking s) : HasSphericalGaussValuesOnCertifiedCap s := by
  refine ⟨marked,?_⟩
  intro S
  let _ := S
  refine fun e R Z hZ c cap => ?_
  have div := (spin_cap_parameters_and_gauss_divisor s cap).2.2
  obtain ⟨_,_,_,_,_,ha,_⟩ := cap
  exact manuscript_physical_spherical_gauss_fibers certifiedClosedParameters.height_pos ha hZ div

/-- Original Section 2 candidates in both physical presentations satisfy the two genuine
sphere-valued equalities in the same marking that realizes their certified spin cap. -/
theorem manuscript_C1_same_cap_spherical_gauss_markings :
    AllManuscriptC1Surfaces HasSphericalGaussValuesOnCertifiedCap ∧
      AllPlacedManuscriptC1Surfaces HasSphericalGaussValuesOnCertifiedCap :=
  original_property_of_all_manuscript_C1_surfaces _ (fun o =>
    certified_cap_gives_physical_spherical_gauss o.toPositional (original_graph_certified_spin_cap_gauss_marking o))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.certified_cap_gives_physical_spherical_gauss
#print axioms TwoAxisHelicoid.manuscript_C1_same_cap_spherical_gauss_markings
