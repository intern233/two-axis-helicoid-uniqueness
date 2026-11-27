import TwoAxisHelicoid.ActualHeightInverse

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology

theorem complex_cobounded_eventuallyEq_nhds {E : Type*} {f g : ℂ → E}
    (h : f =ᶠ[cobounded ℂ] g) :
    ∀ᶠ z : ℂ in cobounded ℂ, f =ᶠ[𝓝 z] g := by
  obtain ⟨R,_hR,hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp h
  filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)] with z hz
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
  exact hR hw.le

/-- Any inverse germ with the correct puncture limit agrees with the
constructed analytic inverse. Thus its regularity is derived, even when
the inverse was originally specified only by its two algebraic identities. -/
theorem actual_height_inverse_eventually_analytic {K : ℂ → ℂ} {t a c : ℝ}
    (ht : 0 < t) (hc : c ≠ 0)
    (hK : Tendsto K (cobounded ℂ) (𝓝[≠] 0))
    (hR : ∀ᶠ ξ : ℂ in cobounded ℂ, actualComplexHeight t a c ht (K ξ) = ξ) :
    ∀ᶠ ξ : ℂ in cobounded ℂ, AnalyticAt ℂ K ξ := by
  obtain ⟨k,_hka,_hk0,_hKt,_hKR,hKL,hKa⟩ := actual_complex_height_inverse (a := a) ht hc
  have he : (fun ξ : ℂ => k ξ⁻¹) =ᶠ[cobounded ℂ] K := by
    filter_upwards [hK.eventually hKL,hR] with ξ hξ hr
    rwa [hr] at hξ
  filter_upwards [hKa,complex_cobounded_eventuallyEq_nhds he] with ξ hξ heξ
  exact hξ.congr heξ

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_height_inverse_eventually_analytic
