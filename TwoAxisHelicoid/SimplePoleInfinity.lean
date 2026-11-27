import TwoAxisHelicoid.SimplePoleHeightChart
import Mathlib.Analysis.Normed.Field.Lemmas

namespace TwoAxisHelicoid
open Complex Filter Bornology Set
open scoped Topology

theorem simplePoleCoordinate_tendsto {A : ℂ} (hA : A ≠ 0)
    {r : ℂ → ℂ} (hr : AnalyticAt ℂ r 0) :
    Tendsto (simplePoleCoordinate A r) (𝓝[≠] 0) (cobounded ℂ) := by
  have hv := simplePoleReciprocal_analyticAt hA hr
  have hden : ∀ᶠ z in 𝓝 (0 : ℂ), A+z*r z ≠ 0 := by
    have hc : ContinuousAt (fun z : ℂ => A+z*r z) 0 := by fun_prop
    exact hc.eventually_ne (by simpa using hA)
  have ht : Tendsto (simplePoleReciprocal A r) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa using hv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [hden.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with z hz hn
      exact div_ne_zero hn hz
  apply (tendsto_inv₀_nhdsNE_zero.comp ht).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  simp only [Function.comp_def,simplePoleReciprocal_eq_inv A r hz,inv_inv]

/-- A genuine local inverse of a simple pole, written in the reciprocal
coordinate. Both inverse identities hold on punctured neighborhoods. -/
theorem simplePoleCoordinate_inverse_at_infinity {A : ℂ} (hA : A ≠ 0)
    {r : ℂ → ℂ} (hr : AnalyticAt ℂ r 0) :
    ∃ k : ℂ → ℂ, AnalyticAt ℂ k 0 ∧ k 0 = 0 ∧
      Tendsto (fun ξ : ℂ => k ξ⁻¹) (cobounded ℂ) (𝓝[≠] 0) ∧
      (∀ᶠ ξ : ℂ in cobounded ℂ, simplePoleCoordinate A r (k ξ⁻¹) = ξ) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), k (simplePoleCoordinate A r z)⁻¹ = z) ∧
      (∀ᶠ ξ : ℂ in cobounded ℂ, AnalyticAt ℂ (fun ξ : ℂ => k ξ⁻¹) ξ) := by
  obtain ⟨k,hka,hk0,_,hkl,hkr⟩ := simplePoleReciprocal_local_inverse hA hr
  have hi := tendsto_inv₀_cobounded (α := ℂ)
  have hne : ∀ᶠ ξ : ℂ in cobounded ℂ, ξ ≠ 0 := by
    filter_upwards [eventually_cobounded_le_norm (E := ℂ) (1 : ℝ)] with ξ hξ
    intro h
    norm_num [h] at hξ
  have he := hi.eventually hkr
  have hkn : ∀ᶠ ξ : ℂ in cobounded ℂ, k ξ⁻¹ ≠ 0 := by
    filter_upwards [he,hne] with ξ hξ hn
    intro h
    rw [h,simplePoleReciprocal_zero] at hξ
    exact (inv_ne_zero hn) hξ.symm
  refine ⟨k,hka,hk0,?_,?_,?_,?_⟩
  · apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,hkn⟩
    simpa only [Function.comp_def,hk0] using hka.continuousAt.tendsto.comp hi
  · filter_upwards [he,hkn] with ξ hξ hn
    rw [simplePoleReciprocal_eq_inv A r hn] at hξ
    simpa only [inv_inv] using congrArg Inv.inv hξ
  · filter_upwards [hkl.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with z hz hn
    rwa [simplePoleReciprocal_eq_inv A r hn] at hz
  · filter_upwards [hi.eventually hka.eventually_analyticAt,hne] with ξ hξ hn
    exact hξ.comp (analyticAt_id.inv hn)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.simplePoleCoordinate_inverse_at_infinity
