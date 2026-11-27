import TwoAxisHelicoid.DyadicExpTrace

namespace TwoAxisHelicoid.DyadicBall

def lower (a : DyadicBall) : ℤ := max |a.re| |a.im|-a.radius

theorem lower_toBall (prec : ℕ) (a : DyadicBall) :
    (a.toBall prec).lower = (a.lower : ℚ)/(denominator prec : ℚ) := by
  have hd : (0 : ℚ) < denominator prec := by exact_mod_cast denominator_pos prec
  unfold ComplexBall.lower QComplex.absLower toBall lower
  dsimp
  rw [abs_div, abs_div, abs_of_pos hd, max_div_div_right hd.le]
  push_cast
  ring

def ChecksInv (prec : ℕ) (out a : DyadicBall) : Prop :=
  0 < a.lower ∧
    |(denominator prec)^2-(out.re*a.re-out.im*a.im)|+|out.re*a.im+out.im*a.re|+
      (|out.re|+|out.im|)*(a.radius : ℤ) ≤ (out.radius : ℤ)*a.lower

instance (prec : ℕ) (out a : DyadicBall) : Decidable (ChecksInv prec out a) := by
  unfold ChecksInv
  infer_instance

theorem inverse_residual_bound {prec : ℕ} {out a : DyadicBall}
    (h : ChecksInv prec out a) :
    let residual := ComplexBall.sub (ComplexBall.rational 1)
      (ComplexBall.mul (ComplexBall.point (out.toBall prec).center) (a.toBall prec))
    residual.center.absUpper+residual.radius ≤ (out.toBall prec).radius*(a.toBall prec).lower := by
  let D : ℚ := denominator prec
  have hd : 0 < D := by dsimp [D]; exact_mod_cast denominator_pos prec
  have hh : |D^2-((out.re : ℚ)*a.re-(out.im : ℚ)*a.im)|+
      |(out.re : ℚ)*a.im+(out.im : ℚ)*a.re|+
      (|(out.re : ℚ)|+|(out.im : ℚ)|)*(a.radius : ℚ) ≤ (out.radius : ℚ)*(a.lower : ℚ) := by
    dsimp [D]
    exact_mod_cast h.2
  dsimp only
  rw [lower_toBall]
  unfold ComplexBall.sub ComplexBall.add ComplexBall.neg ComplexBall.mul ComplexBall.point
    ComplexBall.rational QComplex.ofRat QComplex.mul QComplex.add QComplex.neg QComplex.absUpper toBall
  dsimp
  change |1+-((out.re : ℚ)/D*((a.re : ℚ)/D)-(out.im : ℚ)/D*((a.im : ℚ)/D))|+
    |0+-((out.re : ℚ)/D*((a.im : ℚ)/D)+(out.im : ℚ)/D*((a.re : ℚ)/D))|+
    (0+((|(out.re : ℚ)/D|+|(out.im : ℚ)/D|)*((a.radius : ℚ)/D)+
      (|(a.re : ℚ)/D|+|(a.im : ℚ)/D|)*0+0*((a.radius : ℚ)/D))) ≤
    ((out.radius : ℚ)/D)*((a.lower : ℚ)/D)
  simp only [zero_add, mul_zero, zero_mul, add_zero]
  have hr : 1+-((out.re : ℚ)/D*((a.re : ℚ)/D)-(out.im : ℚ)/D*((a.im : ℚ)/D)) =
      (D^2-((out.re : ℚ)*a.re-(out.im : ℚ)*a.im))/D^2 := by field_simp; ring
  have hi : -((out.re : ℚ)/D*((a.im : ℚ)/D)+(out.im : ℚ)/D*((a.re : ℚ)/D)) =
      -((out.re : ℚ)*a.im+(out.im : ℚ)*a.re)/D^2 := by ring
  rw [hr, hi]
  simp only [abs_div, abs_neg, abs_of_pos hd, abs_of_pos (pow_pos hd 2)]
  have hh' := div_le_div_of_nonneg_right hh (le_of_lt (pow_pos hd 2))
  convert hh' using 1 <;> ring

theorem inv_contains {prec : ℕ} {out a : DyadicBall} {z : ℂ}
    (ha : (a.toBall prec).Contains z) (h : ChecksInv prec out a) :
    (out.toBall prec).Contains z⁻¹ := by
  have hd : (0 : ℚ) < denominator prec := by exact_mod_cast denominator_pos prec
  have hl : 0 < (a.toBall prec).lower := by
    rw [lower_toBall]
    exact div_pos (Int.cast_pos.mpr h.1) hd
  have hz : z ≠ 0 := ComplexBall.ne_zero_of_lower_pos ha hl
  have hres := ComplexBall.sub_contains (ComplexBall.rational_contains 1)
    (ComplexBall.mul_contains (ComplexBall.point_contains (out.toBall prec).center) ha)
  have hnorm := ComplexBall.norm_le hres
  let residual := ComplexBall.sub (ComplexBall.rational 1)
    (ComplexBall.mul (ComplexBall.point (out.toBall prec).center) (a.toBall prec))
  have hb : ((residual.center.absUpper+residual.radius : ℚ) : ℝ) ≤
      (((out.toBall prec).radius*(a.toBall prec).lower : ℚ) : ℝ) :=
    Rat.cast_le.mpr (inverse_residual_bound h)
  have hzero : ((1 : ℚ) : ℂ) = 1 := by norm_num
  rw [hzero] at hnorm
  have hsmall : ‖1-(out.toBall prec).center.val*z‖ ≤
      ((out.toBall prec).radius : ℝ)*((a.toBall prec).lower : ℝ) := by
    exact hnorm.trans (by simpa only [Rat.cast_mul] using hb)
  have hr0 : (0 : ℝ) ≤ (out.toBall prec).radius := by
    change (0 : ℝ) ≤ (((out.radius : ℚ)/(denominator prec : ℚ) : ℚ) : ℝ)
    exact Rat.cast_nonneg.mpr (div_nonneg (by positivity) hd.le)
  have he : ‖z⁻¹-(out.toBall prec).center.val‖*‖z‖ =
      ‖1-(out.toBall prec).center.val*z‖ := by
    rw [← norm_mul]
    congr 1
    field_simp
  apply (mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr hz)).mp
  rw [he]
  exact hsmall.trans (mul_le_mul_of_nonneg_left (ComplexBall.lower_le_norm ha) hr0)

end TwoAxisHelicoid.DyadicBall

#print axioms TwoAxisHelicoid.DyadicBall.inv_contains
