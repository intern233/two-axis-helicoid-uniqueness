import TwoAxisHelicoid.PdfNegativePrimalSampling
import Mathlib.Analysis.Real.Pi.Bounds

namespace TwoAxisHelicoid.PdfVertical
open Complex Set

private theorem exp_lower_integer (m : ℕ) : (27/10:ℝ)^m ≤ Real.exp (m:ℝ) := by
  rw [show (m:ℝ)=(m:ℕ)*(1:ℝ) by simp,Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _

theorem negative_rate_twelve : (1000000:ℝ) ≤ Real.exp (2*Real.pi*((12:ℝ)*(3/16))) :=
  ((by norm_num : (1000000:ℝ)≤(27/10)^14).trans (exp_lower_integer 14)).trans
    (Real.exp_le_exp.mpr (by linarith [Real.pi_gt_d2]))

theorem negative_rate_sixteen : (50000000:ℝ) ≤ Real.exp (2*Real.pi*((16:ℝ)*(3/16))) :=
  ((by norm_num : (50000000:ℝ)≤(27/10)^18).trans (exp_lower_integer 18)).trans
    (Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three]))

/-- A bound on the analytic strip and the sampled exponential rate give
a rational error for the mean of the real parts of the original kernel. -/
theorem negative_short_node_error {M N D : ℕ} (hn : 0<N) (hd : 1<D)
    (rate : (D:ℝ)≤Real.exp (2*Real.pi*((N:ℝ)*(3/16)))) {t a : ℝ} (ht : 9/10≤t)
    (bd : ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/16 → ‖thetaA t a (z+I*((t/2:ℝ):ℂ))‖≤(M:ℝ)) :
    |(1/(N:ℝ))*(∑ k∈Finset.range N,(thetaA t a (((-1+(k:ℝ)/N:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re)
      -thetaHorizontalPeriod t a|≤2*(M:ℝ)/((D:ℝ)-1) := by
  have sample := periodic_theta_sample_error hn (s:=3/16) (by norm_num) (by linarith) bd
  apply sample.trans
  let r := Real.exp (-(2*Real.pi*((N:ℝ)*(3/16))))
  have pos : 0<r := Real.exp_pos _
  have large : (1:ℝ)<D := by exact_mod_cast hd
  have bounded : r*(D:ℝ)≤1 := by
    dsimp only [r]
    rw [Real.exp_neg,inv_mul_eq_div]
    exact (div_le_one (Real.exp_pos _)).mpr rate
  have below : r<1 := by nlinarith [mul_pos pos (sub_pos.mpr large)]
  have scaled := mul_le_mul_of_nonneg_left bounded (show 0≤(M:ℝ) by positivity)
  change 2*((M:ℝ)*r/(1-r))≤2*(M:ℝ)/((D:ℝ)-1)
  rw [← mul_div_assoc,div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.negative_short_node_error
