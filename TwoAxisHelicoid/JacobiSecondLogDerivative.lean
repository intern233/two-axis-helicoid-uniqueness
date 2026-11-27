import TwoAxisHelicoid.JacobiLogDerivative
import Mathlib.Analysis.Calculus.SmoothSeries

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
set_option maxHeartbeats 400000

theorem jacobiEulerLog_eq_tsum {q x : ℂ} (hq : ‖q‖ < 1)
    (hx : ‖q‖*‖x‖ < 1) :
    x*logDeriv (jacobiFactorProduct q) x =
      ∑' n : ℕ, -q^(n+1)*x/(1-q^(n+1)*x) := by
  rw [jacobiFactorProduct_logDeriv hq hx, ← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

theorem jacobiEulerTerm_hasDerivAt (q : ℂ) (n : ℕ) {x : ℂ}
    (hx : 1-q^(n+1)*x ≠ 0) :
    HasDerivAt (fun y : ℂ => -q^(n+1)*y/(1-q^(n+1)*y))
      (-q^(n+1)/(1-q^(n+1)*x)^2) x := by
  have hd := ((hasDerivAt_id x).const_mul (-q^(n+1))).div
    (((hasDerivAt_id x).const_mul (q^(n+1))).const_sub 1) hx
  convert hd using 1
  · funext y
    rfl
  · dsimp
    ring

theorem jacobiEulerSeries_hasDerivAt_on_ball {q x : ℂ} {R : ℝ}
    (hq : ‖q‖ < 1) (hR : ‖q‖*R < 1) (hx : ‖x‖ < R) :
    HasDerivAt (fun y : ℂ => ∑' n : ℕ, -q^(n+1)*y/(1-q^(n+1)*y))
      (∑' n : ℕ, -q^(n+1)/(1-q^(n+1)*x)^2) x := by
  have hsum : Summable (fun n : ℕ => ‖q‖^(n+1)) := by
    simpa only [norm_mul, norm_pow, norm_one, mul_one] using
      jacobi_factor_norm_summable hq (1 : ℂ)
  have hvalid {y : ℂ} (hy : y ∈ Metric.ball (0 : ℂ) R) : ‖q‖*‖y‖ < 1 := by
    have hny : ‖y‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hy
    exact (mul_le_mul_of_nonneg_left hny.le (norm_nonneg q)).trans_lt hR
  have hder (n : ℕ) (y : ℂ) (hy : y ∈ Metric.ball (0 : ℂ) R) :=
    jacobiEulerTerm_hasDerivAt q n (jacobi_factor_ne_zero hq (hvalid hy) n)
  have hbound (n : ℕ) (y : ℂ) (hy : y ∈ Metric.ball (0 : ℂ) R) :
      ‖-q^(n+1)/(1-q^(n+1)*y)^2‖ ≤ ‖q‖^(n+1)/(1-‖q‖*R)^2 := by
    have hny : ‖y‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hy
    have hd : 1-‖q‖*R ≤ ‖1-q^(n+1)*y‖ :=
      (sub_le_sub_left (mul_le_mul_of_nonneg_left hny.le (norm_nonneg q)) 1).trans
        (jacobi_factor_denominator_bound hq y n)
    rw [norm_div, norm_neg, norm_pow, norm_pow]
    exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg q) _)
      (sq_pos_of_pos (sub_pos.mpr hR))
      (pow_le_pow_left₀ (sub_pos.mpr hR).le hd 2)
  have hxmem : x ∈ Metric.ball (0 : ℂ) R := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hconv : Summable (fun n : ℕ => -q^(n+1)*x/(1-q^(n+1)*x)) := by
    convert (jacobi_log_terms_summable hq (hvalid hxmem)).mul_right x using 1
    ext n
    ring
  exact hasDerivAt_tsum_of_isPreconnected (hsum.div_const ((1-‖q‖*R)^2))
    Metric.isOpen_ball (convex_ball (0 : ℂ) R).isPreconnected hder hbound hxmem hconv hxmem

theorem jacobiEulerLog_hasDerivAt {q x : ℂ}
    (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hx : ‖q‖*‖x‖ < 1) :
    HasDerivAt (fun y : ℂ => y*logDeriv (jacobiFactorProduct q) y)
      (∑' n : ℕ, -q^(n+1)/(1-q^(n+1)*x)^2) x := by
  have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hxr : ‖x‖ < 1/‖q‖ := (lt_div_iff₀ hqn).mpr (by simpa only [mul_comm] using hx)
  obtain ⟨R, hxR, hR⟩ := exists_between hxr
  have hqR : ‖q‖*R < 1 := by
    simpa only [mul_comm] using (lt_div_iff₀ hqn).mp hR
  apply (jacobiEulerSeries_hasDerivAt_on_ball hq hqR hxR).congr_of_eventuallyEq
  have hopen : IsOpen {y : ℂ | ‖q‖*‖y‖ < 1} := isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact jacobiEulerLog_eq_tsum hq hy

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiEulerLog_hasDerivAt
