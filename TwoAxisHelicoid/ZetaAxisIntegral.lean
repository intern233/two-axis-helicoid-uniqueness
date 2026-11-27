import TwoAxisHelicoid.ZetaRectangleResidue
import TwoAxisHelicoid.ZetaVerticalQuasi

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Interval
attribute [local irreducible] thetaZeta thetaEtaExpression

theorem thetaZeta_axis_difference_integral {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) :
    I*(∫ y : ℝ in 0..2*t, zetaAxisDifference t a y) =
      -2*(a : ℂ)*zetaImaginaryQuasi t-2*Real.pi*I := by
  have hn (x : ℝ) (hx : x ∈ Icc (-a) a) :
      (x : ℂ)-(t : ℂ)*I ∉ (rhombicPeriodPair t ht).lattice := by
    have hm : (x : ℂ)-(t : ℂ)*I ∈ complexOpenRect (-1) 1 (-2*t) (2*t) := by
      simpa only [Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using
        central_rectangle_horizontal_mem ht ha.2 hx (-t) (by simp [abs_of_pos ht])
    intro hL
    have he := congrArg Complex.im (rhombic_central_rectangle_lattice ht hm hL)
    norm_num at he
    linarith
  have hbottom : IntervalIntegrable (fun x : ℝ => thetaZeta t ((x : ℂ)-(t : ℂ)*I)) volume (-a) a := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith [ha.1] : -a ≤ a)
    intro x hx
    exact ((thetaZeta_hasDerivAt_of_pos ht ht (hn x hx)).continuousAt.comp
      (f := fun x : ℝ => (x : ℂ)-(t : ℂ)*I) (by fun_prop)).continuousWithinAt
  have htop : (∫ x : ℝ in -a..a, thetaZeta t ((x : ℂ)+(t : ℂ)*I)) =
      (∫ x : ℝ in -a..a, thetaZeta t ((x : ℂ)-(t : ℂ)*I))+
        2*(a : ℂ)*zetaImaginaryQuasi t := by
    calc
      _ = ∫ x : ℝ in -a..a, thetaZeta t ((x : ℂ)-(t : ℂ)*I)+zetaImaginaryQuasi t := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by linarith [ha.1] : -a ≤ a)] at hx
        have h := thetaZeta_add_vertical ht (hn x hx)
        rw [show (x : ℂ)-(t : ℂ)*I+2*I*t = (x : ℂ)+(t : ℂ)*I by ring] at h
        exact h
      _ = _ := by
        rw [intervalIntegral.integral_add hbottom intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp only [Complex.real_smul,Complex.ofReal_sub,Complex.ofReal_neg]
        ring
  have hp : |a| < 1 := by simpa [abs_of_pos ha.1] using ha.2
  have hright := (thetaZeta_vertical_continuous ht hp ha.1.ne').intervalIntegrable (μ := volume) (-t) t
  have hleft : IntervalIntegrable (fun y : ℝ => thetaZeta t (-(a : ℂ)+(y : ℂ)*I)) volume (-t) t := by
    simpa only [Complex.ofReal_neg] using
      (thetaZeta_vertical_continuous ht (x := -a) (by simpa using hp)
        (neg_ne_zero.mpr ha.1.ne')).intervalIntegrable (μ := volume) (-t) t
  rw [zetaAxisDifference_integral_centered ht ha]
  unfold zetaAxisDifference
  rw [intervalIntegral.integral_sub hleft hright]
  have hres := thetaZeta_rectangle_residue ht ha
  unfold rectangleBoundary at hres
  rw [htop] at hres
  linear_combination -hres

/-- The holomorphic regular part of `dg/g - i α dh` on the axis for the
integer Gauss family, with the closed-height value `u = π/t - η`. -/
noncomputable def axisClosedRegularOmega (t a : ℝ) (m : ℤ) (z : ℂ) : ℂ :=
  thetaZeta t (z-a)-thetaZeta t (z+a)+2*(m : ℂ)*thetaEtaExpression t+
    2*((m : ℂ)-a)*((Real.pi : ℂ)/t-thetaEtaExpression t)

/-- The ordinary axis integral in manuscript Lemma 4.1, including its exact
constant term. The contour argument above accounts for the pole contribution. -/
theorem axisClosedRegularOmega_integral {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) :
    I*(∫ y : ℝ in 0..2*t, axisClosedRegularOmega t a m (I*y)) =
      2*Real.pi*I*(2*(m : ℂ)-1) := by
  have hD := (zetaAxisDifference_continuous ht ha).intervalIntegrable (μ := volume) 0 (2*t)
  have he : (fun y : ℝ => axisClosedRegularOmega t a m (I*y)) =
      fun y => zetaAxisDifference t a y+
        (2*(m : ℂ)*thetaEtaExpression t+2*((m : ℂ)-a)*((Real.pi : ℂ)/t-thetaEtaExpression t)) := by
    funext y
    unfold axisClosedRegularOmega zetaAxisDifference
    rw [show I*(y : ℂ)-(a : ℂ) = -(a : ℂ)+(y : ℂ)*I by ring,
      show I*(y : ℂ)+(a : ℂ) = (a : ℂ)+(y : ℂ)*I by ring]
    ring
  rw [he,intervalIntegral.integral_add hD intervalIntegrable_const,
    intervalIntegral.integral_const,mul_add,thetaZeta_axis_difference_integral ht ha]
  simp only [sub_zero,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat]
  unfold zetaImaginaryQuasi
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne']
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaZeta_axis_difference_integral
#print axioms TwoAxisHelicoid.axisClosedRegularOmega_integral
