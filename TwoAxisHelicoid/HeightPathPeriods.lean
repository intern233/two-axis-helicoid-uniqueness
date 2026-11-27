import TwoAxisHelicoid.ChartAvoidingPaths
import TwoAxisHelicoid.HarmonicComplexCoefficient

namespace TwoAxisHelicoid
open Complex Set Metric InnerProductSpace
set_option maxHeartbeats 800000

namespace HolomorphicCoefficientDisks
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

noncomputable def chartHeightCoefficient (H : X → ℝ) (p : X) (z : ℂ) : ℂ :=
  scalarComplexCoefficient (fun w => H ((chartAt ℂ p).symm w)) z

theorem height_segment_real_integral {A : HolomorphicCoefficientDisks X} {U : Set X}
    {H : X → ℝ}
    (hH : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∈ U →
      HarmonicAt (fun w : ℂ => H ((chartAt ℂ p).symm w)) z)
    (p : X) {x y : X} (hx : x ∈ A.primitives.domain p) (hy : y ∈ A.primitives.domain p)
    (hU : ∀ s : ℝ, s ∈ Icc 0 1 → (chartAt ℂ p).symm (chartSegment p x y s) ∈ U) :
    (∫ s : ℝ in 0..1,
      (chartAt ℂ p y-chartAt ℂ p x)*chartHeightCoefficient H p (chartSegment p x y s)).re =
      H y-H x := by
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => H ((chartAt ℂ p).symm (chartSegment p x y s)))
        (((chartAt ℂ p y-chartAt ℂ p x)*chartHeightCoefficient H p (chartSegment p x y s)).re) s := by
    have hh := hH p _ (A.chartSegment_mem p hx hy hs) (hU s hs)
    have hf := scalarComplexCoefficient_hasFDerivAt (hh.1.differentiableAt (by norm_num))
    have he := hf.comp_hasDerivAt s
      (AffineMap.hasDerivAt_lineMap (𝕜 := ℝ)
        (a := chartAt ℂ p x) (b := chartAt ℂ p y) (x := s))
    simpa only [Function.comp_def,realCoefficientDerivative_apply,chartHeightCoefficient] using! he
  have hi := segment_coefficient_integrable
    (fun p z hz hu => (scalarComplexCoefficient_analyticAt (hH p z hz hu)).continuousAt) p hx hy hU
  have hri := And.intro (Complex.reCLM.integrable_comp hi.1) (Complex.reCLM.integrable_comp hi.2)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs)) hri
  have hInt := Complex.reCLM.intervalIntegral_comp_comm hi
  change (∫ s : ℝ in 0..1,
    ((chartAt ℂ p y-chartAt ℂ p x)*chartHeightCoefficient H p (chartSegment p x y s)).re) =
    (∫ s : ℝ in 0..1,
      (chartAt ℂ p y-chartAt ℂ p x)*chartHeightCoefficient H p (chartSegment p x y s)).re at hInt
  rw [hInt] at he
  simpa only [chartSegment,AffineMap.lineMap_apply_one,AffineMap.lineMap_apply_zero,
    (chartAt ℂ p).left_inv hx.1,(chartAt ℂ p).left_inv hy.1] using! he

theorem AvoidingPath.height_real_integral {A : HolomorphicCoefficientDisks X} {U : Set X}
    {H : X → ℝ}
    (hH : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∈ U →
      HarmonicAt (fun w : ℂ => H ((chartAt ℂ p).symm w)) z)
    {x y : X} (c : A.AvoidingPath U x y) :
    (c.integral (chartHeightCoefficient H)).re = H y-H x := by
  induction c with
  | refl => simp only [integral,zero_re,sub_self]
  | step p x y hx hy hU => exact height_segment_real_integral hH p hx hy hU
  | trans c d hc hd =>
      simp only [integral,add_re,hc,hd]
      ring

/-- Single-valued harmonic height forces the actual height differential's
closed-path real periods to vanish. -/
theorem chartHeightCoefficient_zero_real_periods {A : HolomorphicCoefficientDisks X} {U : Set X}
    {H : X → ℝ}
    (hH : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∈ U →
      HarmonicAt (fun w : ℂ => H ((chartAt ℂ p).symm w)) z) :
    A.ZeroRealAvoidingPeriods U (chartHeightCoefficient H) := by
  intro x c
  rw [c.height_real_integral hH,sub_self]

end HolomorphicCoefficientDisks
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.chartHeightCoefficient_zero_real_periods
