import TwoAxisHelicoid.ImmersionAtlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace TwoAxisHelicoid
open Set
open scoped ContDiff Manifold

variable {M E A : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- A smooth ambient homeomorphism with smooth inverse has injective
actual derivative. -/
theorem smooth_homeomorph_fderiv_injective (D : A ≃ₜ A)
    (hD : ContDiff ℝ ∞ D) (hDi : ContDiff ℝ ∞ D.symm) (x : A) :
    Function.Injective (fderiv ℝ D x) := by
  have hd := hD.differentiable (by simp)
  have hdi := hDi.differentiable (by simp)
  have hc : (fderiv ℝ D.symm (D x)).comp (fderiv ℝ D x) =
      ContinuousLinearMap.id ℝ A := by
    rw [← fderiv_comp x (hdi (D x)) (hd x)]
    have he : D.symm ∘ D = id := by funext z; exact D.symm_apply_apply z
    rw [he, fderiv_id]
  intro v w hvw
  have h := congrArg (fderiv ℝ D.symm (D x)) hvw
  simpa only [← ContinuousLinearMap.comp_apply, hc, ContinuousLinearMap.id_apply] using h

/-- The original finite-point immersion charts survive an actual smooth
ambient change of coordinates. -/
theorem regularImmersionChart_ambient_comp {F : M → A}
    {e : OpenPartialHomeomorph M E} (he : RegularImmersionChart F e)
    (D : A ≃ₜ A) (hD : ContDiff ℝ ∞ D) (hDi : ContDiff ℝ ∞ D.symm) :
    RegularImmersionChart (D ∘ F) e := by
  intro y hy
  obtain ⟨hf,hfi⟩ := he y hy
  refine ⟨hD.contDiffAt.comp y hf,?_⟩
  change Function.Injective (fderiv ℝ (D ∘ (F ∘ e.symm)) y)
  rw [fderiv_comp y (hD.differentiable (by simp) _) (hf.differentiableAt (by simp))]
  exact (smooth_homeomorph_fderiv_injective D hD hDi _).comp hfi

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.smooth_homeomorph_fderiv_injective
#print axioms TwoAxisHelicoid.regularImmersionChart_ambient_comp
