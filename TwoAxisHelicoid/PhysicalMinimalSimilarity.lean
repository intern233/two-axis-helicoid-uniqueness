import TwoAxisHelicoid.OrthogonalMeanCurvature
import TwoAxisHelicoid.HorizontalLineCoordinates
import TwoAxisHelicoid.RegularOneSidedCuttingBalls

namespace TwoAxisHelicoid
open Complex Matrix Set Topology
open scoped Matrix ContDiff Manifold

/-- A linear ambient similarity preserves zero mean curvature in any
regular coordinate system, for either sign of its determinant. -/
theorem coordinate_minimal_linear_similarity {f : ℂ → Fin 3 → ℝ} {z : ℂ}
    (L : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ)) {k : ℝ}
    (metric : ∀ a b, L a ⬝ᵥ L b=k*(a ⬝ᵥ b)) (minimal : coordinateMeanCurvature f z=0) :
    coordinateMeanCurvature (L ∘ f) z=0 := by
  let Y := L ∘ f
  have first : fderiv ℝ Y = fun w => L.toContinuousLinearMap.comp (fderiv ℝ f w) := by
    funext w
    exact L.comp_fderiv
  have second (u v : ℂ) : fderiv ℝ (fderiv ℝ Y) z u v=L (fderiv ℝ (fderiv ℝ f) z u v) := by
    rw [first,fderiv_continuousLinearEquiv_comp]
    rfl
  have firstAt (v : ℂ) : fderiv ℝ Y z v=L (fderiv ℝ f z v) := by rw [first]; rfl
  have triple (a b c : Fin 3 → ℝ) : L a ⬝ᵥ (L b ⨯₃ L c) =
      (a ⬝ᵥ (b ⨯₃ c))*(LinearMap.toMatrix' L.toLinearEquiv.toLinearMap).det :=
    spatial_triple_product_map L.toLinearEquiv.toLinearMap a b c
  change coordinateMeanCurvature Y z=0
  rw [coordinateMeanCurvature_zero_iff_numerator] at minimal ⊢
  simp only [meanCurvatureNumerator,firstAt,second,metric,triple] at *
  linear_combination k*(LinearMap.toMatrix' L.toLinearEquiv.toLinearMap).det * minimal

/-- The normalized physical surface is a smooth regular minimal embedding
in its original real surface charts, including for negative pitch. -/
theorem physical_frame_regular_minimal (s : OriginalSmoothHelicoid) :
    let Y := centeredHelicoidNormalization s.axes.pitch_ne ∘ s.position
    IsClosedEmbedding Y ∧ (∀ p : s.carrier, RegularImmersionChart Y (chartAt ℂ p)) ∧
      ∀ p : s.carrier, coordinateMeanCurvature (Y ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p)=0 := by
  intro Y
  let R := centeredHelicoidNormalization s.axes.pitch_ne
  have metric (a b : Fin 3 → ℝ) : R a ⬝ᵥ R b=s.axes.pitch^2*(a ⬝ᵥ b) := by
    change axisSpatialNormalization s.axes.pitch_ne 0 a ⬝ᵥ axisSpatialNormalization s.axes.pitch_ne 0 b=_
    simp only [axisSpatialNormalization_apply,map_zero,sub_zero,verticalRotation_preserves_dot (c:=I) (by simp),
      smul_dotProduct,dotProduct_smul,smul_eq_mul]
    ring
  refine ⟨R.toHomeomorph.isClosedEmbedding.comp s.closedEmbedding,?_,?_⟩
  · intro p z hz
    obtain ⟨smooth,inj⟩ := smooth_surface_regular_manifold_chart s.smooth s.immersion p z hz
    have d := (R.toContinuousLinearMap.hasFDerivAt.comp z (smooth.differentiableAt (by simp)).hasFDerivAt).fderiv
    refine ⟨R.contDiff.contDiffAt.comp z smooth,?_⟩
    change Function.Injective (fderiv ℝ (R.toContinuousLinearMap ∘ (s.position ∘ (chartAt ℂ p).symm)) z)
    rw [d]
    exact R.injective.comp inj
  · intro p
    exact coordinate_minimal_linear_similarity R metric (s.minimal p)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_frame_regular_minimal
