import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.ContinuousInverse

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology ContDiff

/-- A smooth immersion into finite-dimensional Euclidean space has a
smooth left inverse on a neighborhood of each parameter point. -/
theorem smooth_local_left_inverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hi : Function.Injective (fderiv ℝ f x)) :
    ∃ (g : F → E) (U : Set E), IsOpen U ∧ x ∈ U ∧
      ContDiffAt ℝ ∞ g (f x) ∧ ∀ y ∈ U, g (f y) = y := by
  obtain ⟨P,hP⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hi
  have hcomp : P.comp (fderiv ℝ f x) = ContinuousLinearMap.id ℝ E := by
    ext v
    exact hP v
  have hpf : ContDiffAt ℝ ∞ (P ∘ f) x := P.contDiff.contDiffAt.comp x hf
  have hd : HasFDerivAt (P ∘ f) ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) x := by
    have hd := P.hasFDerivAt.comp x (hf.differentiableAt (by simp)).hasFDerivAt
    rw [hcomp] at hd
    exact hd
  let e := hpf.toOpenPartialHomeomorph (P ∘ f) hd (by simp)
  have hx : x ∈ e.source := hpf.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hg : ContDiffAt ℝ ∞ e.symm (P (f x)) := hpf.to_localInverse hd (by simp)
  refine ⟨e.symm ∘ P,e.source,e.open_source,hx,hg.comp (f x) P.contDiff.contDiffAt,?_⟩
  intro y hy
  exact e.left_inv hy

/-- Smoothness may be tested after composing with a smooth immersion,
provided the tested map is continuous. This will certify the overlaps
between the old surface charts and the new cap chart. -/
theorem contDiffAt_of_comp_immersion
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : G → E} {x : G}
    (hf : ContDiffAt ℝ ∞ f (g x)) (hi : Function.Injective (fderiv ℝ f (g x)))
    (hg : ContinuousAt g x) (hfg : ContDiffAt ℝ ∞ (f ∘ g) x) :
    ContDiffAt ℝ ∞ g x := by
  obtain ⟨r,U,hU,hx,hr,hleft⟩ := smooth_local_left_inverse hf hi
  have he : r ∘ (f ∘ g) =ᶠ[𝓝 x] g := by
    filter_upwards [hg.eventually (hU.mem_nhds hx)] with y hy
    exact hleft (g y) hy
  exact (hr.comp x hfg).congr_of_eventuallyEq he.symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.smooth_local_left_inverse
#print axioms TwoAxisHelicoid.contDiffAt_of_comp_immersion

