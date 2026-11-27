import TwoAxisHelicoid.PuncturedImmersionCharts
import Mathlib.Analysis.Complex.Basic

namespace TwoAxisHelicoid
open Set
open scoped ContDiff Manifold

variable {M E E' A : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- A real linear change of chart coordinates preserves actual
regularity and injectivity of the parametrization derivative. -/
theorem regularImmersionChart_reparametrize {F : M → A}
    {e : OpenPartialHomeomorph M E} (he : RegularImmersionChart F e)
    (L : E ≃L[ℝ] E') :
    RegularImmersionChart F (e.trans L.toHomeomorph.toOpenPartialHomeomorph) := by
  intro y hy
  have hy' : L.symm y ∈ e.target := hy.2
  obtain ⟨hf,hfi⟩ := he _ hy'
  change ContDiffAt ℝ ∞ ((F ∘ e.symm) ∘ L.symm) y ∧
    Function.Injective (fderiv ℝ ((F ∘ e.symm) ∘ L.symm) y)
  refine ⟨hf.comp y L.symm.contDiff.contDiffAt,?_⟩
  rw [((hf.differentiableAt (by simp)).hasFDerivAt.comp y L.symm.hasFDerivAt).fderiv]
  exact hfi.comp L.symm.injective

/-- Original complex charts supply real plane charts for the concrete
cap construction; the real and complex coordinate models are related
by the explicit continuous real-linear equivalence. -/
theorem punctured_complex_immersion_real_charts [T1Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M] {F : M → A} {p : M}
    (hF : ∀ x ≠ p, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,A) ∞ F x)
    (hi : ∀ x ≠ p, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,A) F x)) :
    ∀ x ≠ p, ∃ e : OpenPartialHomeomorph M (ℝ × ℝ),
      RegularImmersionChart F e ∧ p ∉ e.source ∧ x ∈ e.source := by
  intro x hx
  obtain ⟨e,he,hpe,hxe⟩ := punctured_immersion_regular_charts hF hi x hx
  let L := Complex.equivRealProdCLM
  refine ⟨e.trans L.toHomeomorph.toOpenPartialHomeomorph,
    regularImmersionChart_reparametrize he L,?_,?_⟩
  · intro hp
    exact hpe hp.1
  · exact ⟨hxe,mem_univ _⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.regularImmersionChart_reparametrize
#print axioms TwoAxisHelicoid.punctured_complex_immersion_real_charts
