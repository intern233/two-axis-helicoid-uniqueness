import TwoAxisHelicoid.WeierstrassLineIntegral
import TwoAxisHelicoid.RhombicRegularPaths
import TwoAxisHelicoid.ZetaHalfPeriod

namespace TwoAxisHelicoid
open Complex Set

noncomputable def heightPeriodTwo (t : ℝ) (ht0 : 0 < t) (c u : ℝ) : ℂ :=
  heightLineIntegral t ht0 c u (I*((t/2:ℝ):ℂ)) 2

noncomputable def heightPeriodHalf (t : ℝ) (ht0 : 0 < t) (c u : ℝ) : ℂ :=
  heightLineIntegral t ht0 c u (-1) (1+I*t)

theorem heightPeriodTwo_eq {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) (c u : ℝ) :
    heightPeriodTwo t ht0 c u = -2*I*c*(thetaEtaExpression t+u) := by
  apply heightLineIntegral_two ht ht0 c u
  intro s _
  have he : I*((t/2:ℝ):ℂ)+(s:ℂ)*2 = ((2*s:ℝ):ℂ)+I*((t/2:ℝ):ℂ) := by push_cast; ring
  rw [he]
  exact rhombic_midline_not_mem ht0 _

theorem heightPeriodHalf_eq {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) (c u : ℝ) :
    heightPeriodHalf t ht0 c u = -I*c*((thetaEtaExpression t+u)*(1+I*t)-Real.pi*I) := by
  apply heightLineIntegral_half ht ht0 c u
  exact fun s _ => rhombic_sloping_line_not_mem ht0 s

theorem heightPeriodTwo_re_zero {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) (c u : ℝ) :
    (heightPeriodTwo t ht0 c u).re = 0 := by
  rw [heightPeriodTwo_eq ht ht0 c u]
  simp [Complex.mul_re,Complex.mul_im,thetaEtaExpression_real]

theorem heightPeriodHalf_re {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) (c u : ℝ) :
    (heightPeriodHalf t ht0 c u).re = c*((thetaEtaExpression t).re*t+u*t-Real.pi) := by
  rw [heightPeriodHalf_eq ht ht0 c u]
  simp [Complex.mul_re,Complex.mul_im,thetaEtaExpression_real]
  left
  ring

theorem height_periods_close_iff {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t)
    {c : ℝ} (hc : c ≠ 0) (u : ℝ) :
    (heightPeriodTwo t ht0 c u).re = 0 ∧ (heightPeriodHalf t ht0 c u).re = 0 ↔
      u = Real.pi/t-(thetaEtaExpression t).re := by
  rw [heightPeriodTwo_re_zero ht ht0 c u,heightPeriodHalf_re ht ht0 c u]
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

theorem heightPeriodTwo_closed_value {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) (c : ℝ) :
    heightPeriodTwo t ht0 c (Real.pi/t-(thetaEtaExpression t).re) = -2*Real.pi*I*c/t := by
  rw [heightPeriodTwo_eq ht ht0]
  have he : thetaEtaExpression t = ((thetaEtaExpression t).re:ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using thetaEtaExpression_real t
  rw [he]
  push_cast
  simp only [Complex.ofReal_re]
  ring

theorem heightPeriodHalf_closed_value {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) (c : ℝ) :
    heightPeriodHalf t ht0 c (Real.pi/t-(thetaEtaExpression t).re) = -Real.pi*I*c/t := by
  rw [heightPeriodHalf_eq ht ht0]
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

theorem heightPeriod_vertical_closed_value {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) (c : ℝ) :
    2*heightPeriodHalf t ht0 c (Real.pi/t-(thetaEtaExpression t).re)-
      heightPeriodTwo t ht0 c (Real.pi/t-(thetaEtaExpression t).re) = 0 := by
  rw [heightPeriodTwo_closed_value ht ht0,heightPeriodHalf_closed_value ht ht0]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.height_periods_close_iff
#print axioms TwoAxisHelicoid.heightPeriod_vertical_closed_value
