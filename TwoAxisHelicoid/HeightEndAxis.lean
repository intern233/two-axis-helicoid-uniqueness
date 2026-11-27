import TwoAxisHelicoid.ActualHeightEndCoordinate
import TwoAxisHelicoid.ActualPunctureAxis
import TwoAxisHelicoid.GaussDifferential

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology ComplexConjugate

theorem actualComplexHeight_reflection {t a c : ℝ} (ht : 0 < t) (z : ℂ) :
    actualComplexHeight t a c ht (-conj z) = conj (actualComplexHeight t a c ht z) := by
  have hreal : conj ((rhombicPeriodPair t ht).weierstrassP a) =
      (rhombicPeriodPair t ht).weierstrassP a := by
    simpa only [Complex.conj_ofReal] using (rhombic_weierstrassP_conj ht (a : ℂ)).symm
  unfold actualComplexHeight
  rw [thetaZeta_neg,thetaZeta_conj]
  simp only [map_neg,map_mul,map_add,Complex.conj_I,Complex.conj_ofReal,hreal]
  ring

/-- The actual height inverse takes large real height parameters to the
imaginary axis at the puncture. This is derived from reflection and local
inverse uniqueness. -/
theorem actual_height_inverse_preserves_axis {t a c : ℝ} (ht : 0 < t) {K : ℂ → ℂ}
    (hK : Tendsto K (cobounded ℂ) (𝓝[≠] 0))
    (hKL : ∀ᶠ z in 𝓝[≠] (0 : ℂ), K (actualComplexHeight t a c ht z) = z)
    (hKR : ∀ᶠ ξ : ℂ in cobounded ℂ, actualComplexHeight t a c ht (K ξ) = ξ) :
    ∀ᶠ ξ : ℂ in cobounded ℂ, ξ.im = 0 → (K ξ).re = 0 := by
  have hKn : Tendsto (fun ξ => -conj (K ξ)) (cobounded ℂ) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hh := (Complex.continuous_conj.comp continuous_id).neg.continuousAt.tendsto.comp
        (hK.mono_right nhdsWithin_le_nhds)
      simpa only [Function.comp_def,Pi.neg_apply,id_eq,map_zero,neg_zero] using! hh
    · filter_upwards [hK.eventually self_mem_nhdsWithin] with ξ hξ
      simpa using hξ
  filter_upwards [hKR,hKn.eventually hKL] with ξ hR hL
  intro hξ
  have hc : conj ξ = ξ := by
    apply Complex.ext <;> simp [hξ]
  rw [actualComplexHeight_reflection ht,hR,hc] at hL
  have hr := congrArg Complex.re hL
  simp only [Complex.neg_re,Complex.conj_re] at hr
  linarith

theorem actual_height_inverse_same_vertical_axis {t a c : ℝ} (ht : 0 < t)
    {X : ℂ → Fin 3 → ℝ} (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (hp : ∀ z ω : ℂ, ω ∈ (rhombicPeriodPair t ht).lattice → X (z+ω) = X z)
    {K : ℂ → ℂ} (hK : Tendsto K (cobounded ℂ) (𝓝[≠] 0))
    (hKL : ∀ᶠ z in 𝓝[≠] (0 : ℂ), K (actualComplexHeight t a c ht z) = z)
    (hKR : ∀ᶠ ξ : ℂ in cobounded ℂ, actualComplexHeight t a c ht (K ξ) = ξ) :
    ∀ᶠ ξ : ℂ in cobounded ℂ, ξ.im = 0 →
      X (K ξ) 0 = X 1 0 ∧ X (K ξ) 1 = X 1 1 := by
  have hsmall : ∀ᶠ ξ : ℂ in cobounded ℂ, ‖K ξ‖ < t := by
    simpa only [Metric.mem_ball,dist_zero_right] using
      (hK.mono_right nhdsWithin_le_nhds).eventually (Metric.ball_mem_nhds 0 ht)
  filter_upwards [actual_height_inverse_preserves_axis ht hK hKL hKR,
    hsmall,hK.eventually self_mem_nhdsWithin] with ξ hξ hs hne
  intro hi
  have he : K ξ = I*((K ξ).im : ℂ) := by
    apply Complex.ext <;> simp [hξ hi]
  have hn : (K ξ).im ≠ 0 := by
    intro hz
    apply hne
    change K ξ = 0
    rw [he,hz,Complex.ofReal_zero,mul_zero]
  have hb : |(K ξ).im| < t := (Complex.abs_im_le_norm (K ξ)).trans_lt hs
  rw [he]
  exact actual_periodic_primitive_puncture_axis ht hX hp hn hb

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_height_inverse_same_vertical_axis
