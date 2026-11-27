import TwoAxisHelicoid.PrescribedPlaneHarmonicCoordinate

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Manifold ContDiff
universe u v

/-- Proposition 4.4 for every smooth properly embedded one-ended handle with a
decaying single normal graph at infinity, with its prescribed marked torus. -/
theorem prescribed_smooth_handle_height_end_even_spin
    {M : Type v} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M]
    {L : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L) (X : M → Fin 3 → ℝ) (cl : IsClosedEmbedding X)
    (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (di : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x))
    (A : (Fin 3 → ℝ) ≃ₜ HelicoidTubeCoordinates) (sa : ContDiff ℝ ∞ A) (si : ContDiff ℝ ∞ A.symm)
    (height : HasHelicoidHeightEnd (A ∘ X)) :
    ∃ e : Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) M (PuncturedPeriodTorus L) ∞, EvenSpinExtensionInMarking.{u} X e :=
  prescribed_handle_spin_of_local_isothermal_theorem smooth_plane_metric_has_isothermal_coordinates
    top X cl sm di A sa si height
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.prescribed_smooth_handle_height_end_even_spin
