import TwoAxisHelicoid.OrientedMinimalHarmonicAtlas

namespace TwoAxisHelicoid
open Complex Filter Set InnerProductSpace
open scoped Topology ContDiff Manifold

/-- An isothermal chart expressed directly in terms of its two real
derivative columns. No orientation of any pre-existing chart is prescribed. -/
def InducedIsothermalChart {M : Type*} [TopologicalSpace M]
    (X : M → Fin 3 → ℝ) (e : OpenPartialHomeomorph M ℂ) : Prop :=
  RegularImmersionChart X e ∧ ∀ z ∈ e.target, ConformalCoordinateDerivatives (X ∘ e.symm) z

theorem real_minimal_isothermal_chart_harmonic {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℝ,ℂ) ∞ M] {X : M → Fin 3 → ℝ}
    (hsm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x))
    (hm : ∀ x : M, coordinateMeanCurvature (X ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0)
    {e : OpenPartialHomeomorph M ℂ} (he : InducedIsothermalChart X e) : HarmonicImmersionChart X e := by
  intro z hz
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ e.target := e.open_target.mem_nhds hz
  have harm := conformal_minimal_chart_harmonicAt ((he.1 z hz).1.of_le (by norm_num))
    (hnear.mono he.2) (hnear.mono fun w hw => (he.1 w hw).2)
    (hnear.mono fun _ hw => minimal_surface_chart_meanCurvature_zero (smooth_surface_regular_manifold_chart hsm hi) hm he.1 hw)
  refine ⟨?_,he.2 z hz,(he.1 z hz).2⟩
  intro j
  exact harm.comp_CLM (ContinuousLinearMap.proj j)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.real_minimal_isothermal_chart_harmonic
