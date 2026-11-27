import TwoAxisHelicoid.MarkedHelicoidSphericalFluxRigidity
import TwoAxisHelicoid.HarmonicMarkedTorusCompleteness

namespace TwoAxisHelicoid
open Complex Topology Manifold
open scoped Topology ContDiff Manifold

/-- The Bernstein–Breiner geometric flux assertion with its intrinsic
completeness hypothesis stated for the actual induced length metric. -/
def CompleteMarkedBernsteinBreinerFluxPrinciple : Prop :=
  ∀ (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ),
    MarkedEmbeddedHelicoidForFlux L X →
    ∀ (hC : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 3)) 1 (coordinateToEuclidean ∘ X))
      (hD : ∀ q, Function.Injective (mvfderiv 𝓘(ℝ,ℂ) (coordinateToEuclidean ∘ X) q)),
      @CompleteSpace (PuncturedPeriodTorus L) (euclideanImmersionEMetricSpace (coordinateToEuclidean ∘ X) hC hD).toUniformSpace →
      HasSpatialNonverticalFlux L X

/-- Each embedded marked helicoid supplying the data in C.4 or C.5
satisfies the completeness hypothesis of the cited geometric theorem. -/
theorem complete_marked_flux_applies (bbs : CompleteMarkedBernsteinBreinerFluxPrinciple) :
    MarkedBernsteinBreinerFluxPrinciple := by
  intro L X hX
  obtain ⟨hC,hD,hcomp⟩ := harmonic_marked_torus_complete L X (fun z hz => (hX.regular z hz).1)
    hX.immersion hX.closedEmbedding
  exact bbs L X hX hC hD hcomp

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.complete_marked_flux_applies
