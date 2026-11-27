import TwoAxisHelicoid.GeometricHelicoidHypotheses

namespace TwoAxisHelicoid
open Manifold Topology
open scoped Topology ContDiff Manifold

noncomputable def OriginalSmoothHelicoid.euclideanPosition (surface : OriginalSmoothHelicoid) :
    surface.carrier → EuclideanSpace ℝ (Fin 3) := coordinateToEuclidean ∘ surface.position

theorem OriginalSmoothHelicoid.euclidean_smooth (surface : OriginalSmoothHelicoid) :
    ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 3)) 1 surface.euclideanPosition :=
  coordinateToEuclidean.contMDiff.comp (surface.smooth.of_le (by simp))

theorem OriginalSmoothHelicoid.euclidean_immersion (surface : OriginalSmoothHelicoid) (x : surface.carrier) :
    Function.Injective (mvfderiv 𝓘(ℝ,ℂ) surface.euclideanPosition x) := by
  have h1 : MDifferentiableAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) surface.position x :=
    surface.smooth.mdifferentiable (by simp) x
  have h2 : MDifferentiableAt 𝓘(ℝ,Fin 3 → ℝ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 3)) coordinateToEuclidean (surface.position x) :=
    coordinateToEuclidean.differentiableAt.mdifferentiableAt
  unfold OriginalSmoothHelicoid.euclideanPosition mvfderiv
  apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (surface.euclideanPosition x)).injective.comp
  change Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,EuclideanSpace ℝ (Fin 3)) (coordinateToEuclidean ∘ surface.position) x)
  rw [mfderiv_comp x h2 h1,ContinuousLinearMap.mfderiv_eq]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective.comp (surface.immersion x)

theorem OriginalSmoothHelicoid.euclidean_proper (surface : OriginalSmoothHelicoid) :
    IsProperMap surface.euclideanPosition :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isClosedEmbedding.comp
    surface.closedEmbedding).isProperMap

/-- Completeness for the genuine induced Riemannian length metric follows
from the proper spatial embedding. It supplies the completeness condition
in the geometric compactification theorem. -/
theorem OriginalSmoothHelicoid.intrinsic_complete (surface : OriginalSmoothHelicoid) :
    letI : T3Space surface.carrier := surface.closedEmbedding.isEmbedding.t3Space
    letI := euclideanImmersionEMetricSpace surface.euclideanPosition surface.euclidean_smooth surface.euclidean_immersion
    CompleteSpace surface.carrier := by
  let : T3Space surface.carrier := surface.closedEmbedding.isEmbedding.t3Space
  exact proper_euclideanImmersion_complete surface.euclideanPosition surface.euclidean_smooth
    surface.euclidean_immersion surface.euclidean_proper

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.OriginalSmoothHelicoid.intrinsic_complete
