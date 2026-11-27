import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace TwoAxisHelicoid
open Bundle Set Filter MeasureTheory Manifold
open scoped Manifold ContDiff Topology Bundle ENNReal
set_option maxHeartbeats 1000000

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A bound on the actual differential bounds ambient distances by the
intrinsic length distance. Every C¹ path is compared with its actual image. -/
theorem edist_le_riemannianEDist_of_differential_bound {X : M → E}
    (hX : ContMDiff I 𝓘(ℝ, E) 1 X)
    (hD : ∀ x (v : TangentSpace I x), ‖mvfderiv I X x v‖ ≤ ‖v‖) (x y : M) :
    edist (X x) (X y) ≤ riemannianEDist I x y := by
  rw [riemannianEDist]
  apply le_iInf
  intro γ
  apply le_iInf
  intro hγ
  have hmap := hX.comp hγ
  have hb : riemannianEDist 𝓘(ℝ, E) (X x) (X y) ≤
      ∫⁻ u, ‖mfderiv (𝓡∂ 1) 𝓘(ℝ, E) (γ.map hX.continuous) u 1‖ₑ := by
    rw [riemannianEDist]
    exact iInf_le_of_le (γ.map hX.continuous) (iInf_le_of_le hmap le_rfl)
  rw [← IsRiemannianManifold.out] at hb
  apply hb.trans
  apply lintegral_mono
  intro u
  change ‖mfderiv (𝓡∂ 1) 𝓘(ℝ, E) (X ∘ γ) u 1‖ₑ ≤ ‖mfderiv _ _ γ u 1‖ₑ
  have he : ‖mfderiv (𝓡∂ 1) 𝓘(ℝ, E) (X ∘ γ) u 1‖ₑ =
      ‖mvfderiv (𝓡∂ 1) (X ∘ γ) u 1‖ₑ := enorm_tangentSpace_vectorSpace
  rw [he]
  rw [mvfderiv_comp_apply u (hX.mdifferentiable one_ne_zero (γ u))
    (hγ.mdifferentiable one_ne_zero u)]
  simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (hD (γ u) (mfderiv _ _ γ u 1))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.edist_le_riemannianEDist_of_differential_bound
