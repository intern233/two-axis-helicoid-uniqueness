import TwoAxisHelicoid.WeierstrassControlledTails

namespace TwoAxisHelicoid
open Complex Real Set

theorem HasControlledUnitTangentCurves.precomp
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {y : HelicoidTubeCoordinates} {D : E →L[ℝ] HelicoidTubeCoordinates} {ε A : ℝ}
    (h : HasControlledUnitTangentCurves y D ε A) (L : F →L[ℝ] E) :
    HasControlledUnitTangentCurves y (D.comp L) ε A := by
  intro v hv
  exact h (L v) hv

theorem coordinateToTube_injective : Function.Injective coordinateToTube := by
  intro v w h
  have hh := congrArg tubeCartesian h
  simpa only [tubeCartesian_coordinateToTube] using hh

noncomputable def complexChartAsReal {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) : OpenPartialHomeomorph M (ℝ × ℝ) :=
  e.transHomeomorph Complex.equivRealProdCLM.toHomeomorph

@[simp] theorem complexChartAsReal_source {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) : (complexChartAsReal e).source = e.source := rfl

theorem complex_chart_real_differential {M : Type*} [TopologicalSpace M]
    {X : M → Fin 3 → ℝ} (e : OpenPartialHomeomorph M ℂ) {q : M}
    {D : ℂ →L[ℝ] (Fin 3 → ℝ)}
    (h : HasFDerivAt (X ∘ e.symm) D (e q)) :
    HasFDerivAt ((coordinateToTube ∘ X) ∘ (complexChartAsReal e).symm)
      ((coordinateToTube.comp D).comp Complex.equivRealProdCLM.symm.toContinuousLinearMap)
      (complexChartAsReal e q) := by
  have hd := (coordinateToTube.hasFDerivAt.comp (e q) h).comp
    (complexChartAsReal e q) Complex.equivRealProdCLM.symm.hasFDerivAt
  exact hd

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.complex_chart_real_differential
