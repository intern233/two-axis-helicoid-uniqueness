import TwoAxisHelicoid.JacobiRealSeries
import TwoAxisHelicoid.HalfThetaF

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] thetaLogSecond

theorem jacobiExp_one : jacobiExp (1 : ℂ) = -1 := by
  simpa only [jacobiExp, mul_one, mul_comm] using Complex.exp_pi_mul_I

theorem jacobiRealE_at_neg_one (Q : ℝ) :
    jacobiRealE Q (-1) = -1/4 - 2 *
      ∑' n : ℕ, Q^(n+1)/(1+Q^(n+1))^2 := by
  have he : jacobiGeometricSeries Q (-Q) =
      -(∑' n : ℕ, Q^(n+1)/(1+Q^(n+1))^2) := by
    rw [jacobiGeometricSeries, ← tsum_neg]
    apply tsum_congr
    intro n
    simp only [jacobiFraction, pow_succ, mul_neg, sub_neg_eq_add, neg_div]
  simp only [jacobiRealE, mul_neg, mul_one, div_neg, div_one, he]
  norm_num only [jacobiFraction]
  ring

/-- An actual Lambert-type expansion of the half-period elliptic value.
The nome is negative for the rhombic marking. This identity precedes the
arithmetic rearrangement into the manuscript's positive divisor coefficients. -/
theorem ellipticFReal_lambert {t : ℝ} (ht : 0 < t) :
    ellipticFReal t = Real.pi^2 * (1/4 + 2 *
      ∑' n : ℕ, (-Real.exp (-Real.pi*t))^(n+1) /
        (1+(-Real.exp (-Real.pi*t))^(n+1))^2) := by
  have hx : jacobiExp (1 : ℂ) ≠ 1 := by rw [jacobiExp_one]; norm_num
  have hp : ‖jacobiNome t‖ * ‖jacobiExp (1 : ℂ)‖ < 1 := by
    simpa only [jacobiExp_one, norm_neg, norm_one, mul_one] using jacobiNome_norm_lt_one ht
  have hm : ‖jacobiNome t‖ * ‖(jacobiExp (1 : ℂ))⁻¹‖ < 1 := by
    simpa only [jacobiExp_one, inv_neg, inv_one, norm_neg, norm_one, mul_one] using
      jacobiNome_norm_lt_one ht
  have h := thetaLogSecond_eq_jacobiSecondE ht hx hp hm
  rw [jacobiNome_eq_neg_exp, jacobiExp_one, ← Complex.ofReal_neg,
    show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num, jacobiSecondE_ofReal] at h
  have hr := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, ← Complex.ofReal_pow, mul_zero, sub_zero] at hr
  change ellipticFReal t = _ at hr
  rw [hr, jacobiRealE_at_neg_one]
  ring

theorem ellipticFReal_lambert_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => (-Real.exp (-Real.pi*t))^(n+1) /
      (1+(-Real.exp (-Real.pi*t))^(n+1))^2) := by
  let Q := -Real.exp (-Real.pi*t)
  have hQ : |Q| < 1 := by
    dsimp [Q]
    rw [abs_neg, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) ht
  change Summable (fun n : ℕ => Q^(n+1)/(1+Q^(n+1))^2)
  have hs := (jacobiGeometricSeries_summable (Q := Q) (a := -Q)
    hQ (by simpa only [abs_neg] using hQ)).neg
  convert hs using 1
  funext n
  simp only [jacobiFraction, pow_succ, mul_neg, sub_neg_eq_add, neg_div, neg_neg]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ellipticFReal_lambert
#print axioms TwoAxisHelicoid.ellipticFReal_lambert_summable
