import TwoAxisHelicoid.ActualComplexHeight

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology

theorem actual_complex_height_inverse {t a c : ℝ} (ht : 0 < t) (hc : c ≠ 0) :
    ∃ k : ℂ → ℂ, AnalyticAt ℂ k 0 ∧ k 0 = 0 ∧
      Tendsto (fun ξ : ℂ => k ξ⁻¹) (cobounded ℂ) (𝓝[≠] 0) ∧
      (∀ᶠ ξ : ℂ in cobounded ℂ, actualComplexHeight t a c ht (k ξ⁻¹) = ξ) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), k (actualComplexHeight t a c ht z)⁻¹ = z) ∧
      (∀ᶠ ξ : ℂ in cobounded ℂ, AnalyticAt ℂ (fun ξ : ℂ => k ξ⁻¹) ξ) := by
  obtain ⟨k,hka,hk0,hK,hR,hL,hKa⟩ := simplePoleCoordinate_inverse_at_infinity
    (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (Complex.ofReal_ne_zero.mpr hc))
    (actualHeightRegular_analyticAt_zero (a := a) (c := c) ht)
  refine ⟨k,hka,hk0,hK,?_,?_,hKa⟩
  · filter_upwards [hR,hK.eventually (rhombic_puncture_eventually_off_lattice ht)] with ξ hξ hn
    rwa [actualComplexHeight_principal_part ht hn]
  · filter_upwards [hL,rhombic_puncture_eventually_off_lattice ht] with z hz hn
    rwa [actualComplexHeight_principal_part ht hn]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_complex_height_inverse
