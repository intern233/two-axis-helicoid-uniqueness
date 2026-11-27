import TwoAxisHelicoid.HeightPeriods
import TwoAxisHelicoid.SigmaAllIdentities

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology Interval
attribute [local irreducible] thetaZeta

theorem weierstrass_line_integral_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) {z w : ℂ}
    (hreg : ∀ s ∈ Icc (0:ℝ) 1, z+(s:ℂ)*w ∉ (rhombicPeriodPair t ht0).lattice) :
    (∫ s : ℝ in (0)..1, w*(rhombicPeriodPair t ht0).weierstrassP (z+(s:ℂ)*w)) =
      thetaZeta t z-thetaZeta t (z+w) := by
  have hd (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun u : ℝ => -thetaZeta t (z+(u:ℂ)*w))
        (w*(rhombicPeriodPair t ht0).weierstrassP (z+(s:ℂ)*w)) s := by
    have harg := (((hasDerivAt_id s).ofReal_comp).mul_const w).const_add z
    have h := ((thetaZeta_hasDerivAt_of_pos ht ht0 (hreg s hs)).comp s harg).neg
    convert h using 1
    · rfl
    · simp only [Complex.ofReal_one,one_mul]
      ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hs))
    (weierstrass_line_integrable ht0 hreg)
  simpa only [Complex.ofReal_one,Complex.ofReal_zero,one_mul,zero_mul,add_zero,neg_sub_neg] using hFTC


theorem heightLineIntegral_eq_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) (c u : ℝ) {z w : ℂ}
    (hreg : ∀ s ∈ Icc (0:ℝ) 1, z+(s:ℂ)*w ∉ (rhombicPeriodPair t ht0).lattice) :
    heightLineIntegral t ht0 c u z w =
      I*c*(thetaZeta t z-thetaZeta t (z+w)-u*w) := by
  have he (s : ℝ) : w*(I*c*((rhombicPeriodPair t ht0).weierstrassP (z+(s:ℂ)*w)-u)) =
      I*c*(w*(rhombicPeriodPair t ht0).weierstrassP (z+(s:ℂ)*w)-u*w) := by ring
  unfold heightLineIntegral
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub
    (weierstrass_line_integrable ht0 hreg) intervalIntegrable_const,
    weierstrass_line_integral_of_pos ht ht0 hreg]
  simp


theorem heightLineIntegral_two_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) (c u : ℝ) {z : ℂ}
    (hreg : ∀ s ∈ Icc (0:ℝ) 1, z+(s:ℂ)*2 ∉ (rhombicPeriodPair t ht0).lattice) :
    heightLineIntegral t ht0 c u z 2 = -2*I*c*(thetaEtaExpression t+u) := by
  rw [heightLineIntegral_eq_of_pos ht ht0 c u hreg,thetaZeta_add_two]
  ring


theorem heightLineIntegral_half_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) (c u : ℝ) {z : ℂ}
    (hreg : ∀ s ∈ Icc (0:ℝ) 1, z+(s:ℂ)*(1+I*t) ∉ (rhombicPeriodPair t ht0).lattice) :
    heightLineIntegral t ht0 c u z (1+I*t) =
      -I*c*((thetaEtaExpression t+u)*(1+I*t)-Real.pi*I) := by
  have hz := hreg 0 (by norm_num)
  simp only [Complex.ofReal_zero,zero_mul,add_zero] at hz
  rw [heightLineIntegral_eq_of_pos ht ht0 c u hreg,thetaZeta_add_half_of_pos ht ht0 hz]
  ring


theorem heightPeriodTwo_eq_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) (c u : ℝ) :
    heightPeriodTwo t ht0 c u = -2*I*c*(thetaEtaExpression t+u) := by
  apply heightLineIntegral_two_of_pos ht ht0 c u
  intro s _
  have he : I*((t/2:ℝ):ℂ)+(s:ℂ)*2 = ((2*s:ℝ):ℂ)+I*((t/2:ℝ):ℂ) := by push_cast; ring
  rw [he]
  exact rhombic_midline_not_mem ht0 _


theorem heightPeriodHalf_eq_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) (c u : ℝ) :
    heightPeriodHalf t ht0 c u = -I*c*((thetaEtaExpression t+u)*(1+I*t)-Real.pi*I) := by
  apply heightLineIntegral_half_of_pos ht ht0 c u
  exact fun s _ => rhombic_sloping_line_not_mem ht0 s


theorem heightPeriodTwo_re_zero_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) (c u : ℝ) :
    (heightPeriodTwo t ht0 c u).re = 0 := by
  rw [heightPeriodTwo_eq_of_pos ht ht0 c u]
  simp [Complex.mul_re,Complex.mul_im,thetaEtaExpression_real]


theorem heightPeriodHalf_re_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) (c u : ℝ) :
    (heightPeriodHalf t ht0 c u).re = c*((thetaEtaExpression t).re*t+u*t-Real.pi) := by
  rw [heightPeriodHalf_eq_of_pos ht ht0 c u]
  simp [Complex.mul_re,Complex.mul_im,thetaEtaExpression_real]
  left
  ring


theorem height_periods_close_iff_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t)
    {c : ℝ} (hc : c ≠ 0) (u : ℝ) :
    (heightPeriodTwo t ht0 c u).re = 0 ∧ (heightPeriodHalf t ht0 c u).re = 0 ↔
      u = Real.pi/t-(thetaEtaExpression t).re := by
  rw [heightPeriodTwo_re_zero_of_pos ht ht0 c u,heightPeriodHalf_re_of_pos ht ht0 c u]
  simp only [true_and,mul_eq_zero,hc,false_or]
  constructor
  · intro h
    apply (eq_sub_iff_add_eq).mpr
    apply (eq_div_iff ht0.ne').mpr
    nlinarith
  · intro h
    rw [h]
    field_simp
    ring


theorem heightPeriodTwo_closed_value_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) (c : ℝ) :
    heightPeriodTwo t ht0 c (Real.pi/t-(thetaEtaExpression t).re) = -2*Real.pi*I*c/t := by
  rw [heightPeriodTwo_eq_of_pos ht ht0]
  have he : thetaEtaExpression t = ((thetaEtaExpression t).re:ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using thetaEtaExpression_real t
  rw [he]
  push_cast
  simp only [Complex.ofReal_re]
  ring


theorem heightPeriodHalf_closed_value_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) (c : ℝ) :
    heightPeriodHalf t ht0 c (Real.pi/t-(thetaEtaExpression t).re) = -Real.pi*I*c/t := by
  rw [heightPeriodHalf_eq_of_pos ht ht0]
  have he : thetaEtaExpression t = ((thetaEtaExpression t).re:ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using thetaEtaExpression_real t
  rw [he]
  push_cast
  simp only [Complex.ofReal_re]
  have htc : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
  field_simp
  ring


theorem heightPeriod_vertical_closed_value_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) (c : ℝ) :
    2*heightPeriodHalf t ht0 c (Real.pi/t-(thetaEtaExpression t).re)-
      heightPeriodTwo t ht0 c (Real.pi/t-(thetaEtaExpression t).re) = 0 := by
  rw [heightPeriodTwo_closed_value_of_pos ht ht0,heightPeriodHalf_closed_value_of_pos ht ht0]
  ring


end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.height_periods_close_iff_of_pos
