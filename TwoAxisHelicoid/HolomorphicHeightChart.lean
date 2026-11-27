import TwoAxisHelicoid.NullDifferentialRegularity
import TwoAxisHelicoid.CoordinateTubeHomeomorph

namespace TwoAxisHelicoid
open Complex Real Set
open scoped Topology ContDiff

/-- Smoothness and injectivity of the actual real chart derivative follow
from the holomorphic height-normalized Weierstrass differential. -/
theorem holomorphic_height_chart_regular {M : Type*} [TopologicalSpace M]
    {X : M → Fin 3 → ℝ} (e : OpenPartialHomeomorph M ℂ)
    {W : ℂ → ℂ} {R : ℝ}
    (hW : ∀ z : ℂ, R < ‖z‖ → AnalyticAt ℂ W z)
    (hX : ∀ z : ℂ, R < ‖z‖ → HasFDerivAt (X ∘ e.symm)
      (nullRealDerivative (weierstrassTriple (exp (W z)) 1)) z)
    {q : M} (hq : R < ‖e q‖) :
    ContDiffAt ℝ (∞ : WithTop ℕ∞)
      ((coordinateToTube ∘ X) ∘ (complexChartAsReal e).symm) (complexChartAsReal e q) ∧
    Function.Injective (fderiv ℝ
      ((coordinateToTube ∘ X) ∘ (complexChartAsReal e).symm) (complexChartAsReal e q)) := by
  have hXa : AnalyticAt ℝ (X ∘ e.symm) (e q) :=
    analyticAt_of_holomorphic_real_differential (isOpen_lt continuous_const continuous_norm)
      (fun z hz => analyticAt_weierstrass_exp_triple (hW z hz)) hX hq
  have he : Complex.equivRealProdCLM.symm (complexChartAsReal e q) = e q :=
    Complex.equivRealProdCLM.symm_apply_apply (e q)
  constructor
  · have hs : ContDiffAt ℝ (∞ : WithTop ℕ∞) (coordinateToTube ∘ (X ∘ e.symm))
        (Complex.equivRealProdCLM.symm (complexChartAsReal e q)) := by
      rw [he]
      exact coordinateToTube.contDiff.contDiffAt.comp _ hXa.contDiffAt
    exact hs.comp _ Complex.equivRealProdCLM.symm.contDiff.contDiffAt
  · rw [(complex_chart_real_differential e (hX (e q) hq)).fderiv]
    exact coordinateToTube_injective.comp
      ((weierstrass_exp_real_derivative_injective (W (e q))).comp
        Complex.equivRealProdCLM.symm.injective)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.holomorphic_height_chart_regular
