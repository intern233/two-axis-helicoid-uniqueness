import TwoAxisHelicoid.ActualGlobalImmersion
import TwoAxisHelicoid.ActualEndCompleteness
import TwoAxisHelicoid.NullEuclideanMetric

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

noncomputable def actualEuclideanImmersion (t a c : ℝ) (ht : 0 < t) :
    ℂ → EuclideanSpace ℝ (Fin 3) := fun z => coordinateToEuclidean (actualGlobalImmersion t a c ht z)

theorem actualEuclideanImmersion_hasDerivAt_curve {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) {γ : ℝ → ℂ} {v : ℂ} {s : ℝ}
    (hs : γ s ∉ (rhombicPeriodPair t ht).lattice) (hγ : HasDerivAt γ v s) :
    HasDerivAt (actualEuclideanImmersion t a c ht ∘ γ)
      (coordinateToEuclidean (nullRealDerivative (coordinateData t a c ht (γ s)) v)) s := by
  have hD := (actual_global_conformal_harmonic_immersion ht ha hc hG hH).2.2.2 (γ s) hs |>.1
  exact (coordinateToEuclidean.hasFDerivAt.comp (γ s) hD).comp_hasDerivAt s hγ

theorem actualEuclideanImmersion_curve_speed {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) {γ : ℝ → ℂ} {v : ℂ} {s : ℝ}
    (hs : γ s ∉ (rhombicPeriodPair t ht).lattice) (hγ : HasDerivAt γ v s) :
    ‖deriv (actualEuclideanImmersion t a c ht ∘ γ) s‖ =
      Real.sqrt (nullMetric (coordinateData t a c ht (γ s)))*‖v‖ := by
  rw [(actualEuclideanImmersion_hasDerivAt_curve ht ha hc hG hH hs hγ).deriv]
  exact nullRealDerivative_euclidean_norm (coordinateData_null ht ha hs)
    (coordinateData_ne_zero ht ha hc hs) v

/-- Infinite length for the actual immersed Euclidean curve, with speed
defined by its derivative; no metric-density proxy remains in the conclusion. -/
theorem actual_global_end_curve_infinite_length {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0)
    {γ v : ℝ → ℂ} (hd : ∀ u < 1, HasDerivAt γ (v u) u)
    (hv : ContinuousOn v (Iio 1))
    (hreg : ∀ u < 1, γ u ∉ (rhombicPeriodPair t ht).lattice)
    (hlim : Tendsto γ (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℂ))) :
    ∃ b < (1 : ℝ), Tendsto
      (fun s => ∫ u : ℝ in b..s, ‖deriv (actualEuclideanImmersion t a c ht ∘ γ) u‖)
      (𝓝[<] (1 : ℝ)) atTop := by
  obtain ⟨b,hb,hL⟩ := actual_end_curve_infinite_length ht ha hc hd hv hreg hlim
  refine ⟨b,hb,?_⟩
  apply hL.congr'
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hb),self_mem_nhdsWithin] with s hsb hs1
  change b < s at hsb
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc b s := by simpa only [uIcc_of_le hsb.le] using hu
  have hu1 : u < 1 := hu'.2.trans_lt hs1
  exact (actualEuclideanImmersion_curve_speed ht ha hc hG hH (hreg u hu1) (hd u hu1)).symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_global_end_curve_infinite_length
