import TwoAxisHelicoid.ThetaScaledDerivative
import TwoAxisHelicoid.JacobiProductQuasiPeriod
import Mathlib.Analysis.Normed.Group.Tannery

namespace TwoAxisHelicoid
open Complex Filter
open scoped Topology
set_option maxHeartbeats 800000

theorem exp_neg_positive_mul_tendsto_zero {C : ℝ} (hC : 0 < C) :
    Tendsto (fun t : ℝ => Real.exp (-C*t)) atTop (𝓝 0) := by
  have ht := tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hC)
  simpa only [Function.comp_def,id_eq] using Real.tendsto_exp_atBot.comp ht

theorem thetaTerm_one_zero_high_height (n : ℕ) :
    Tendsto (fun t : ℝ => thetaTerm t 1 n 0) atTop (𝓝 (if n = 0 then (1 : ℂ) else 0)) := by
  by_cases hn : n = 0
  · subst n
    simp [thetaTerm,thetaSign,sineJet_one]
  · have hpos : 0 < Real.pi*(n : ℝ)*(n+1)/2 := by
      have hn' : 0 < n := Nat.pos_of_ne_zero hn
      positivity
    have he : Tendsto (fun t : ℝ => Real.exp (-Real.pi*t*n*(n+1)/2)) atTop (𝓝 0) := by
      convert exp_neg_positive_mul_tendsto_zero hpos using 1
      funext t
      congr 1
      ring
    have hc := ((Complex.continuous_ofReal.tendsto 0).comp he).const_mul (thetaSign n)
    simpa only [Function.comp_def,thetaTerm,pow_one,mul_zero,sineJet_one,Complex.cos_zero,mul_one,
      Complex.ofReal_zero,zero_mul,mul_zero,ite_eq_right hn] using hc.mul_const (2*n+1 : ℂ)

theorem thetaScaledJet_one_high_height :
    Tendsto (fun t : ℝ => thetaScaledJet t 1 0) atTop (𝓝 ((Real.pi/2 : ℝ) : ℂ)) := by
  have hs := tendsto_tsum_of_dominated_convergence
    (thetaMajorant_summable (by norm_num : (0 : ℝ) < 1) 0 1)
    thetaTerm_one_zero_high_height
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht n
      exact thetaTerm_norm_le ht (by simp) 1 n)
  have ht : Tendsto (fun t : ℝ => thetaJet t 1 0) atTop (𝓝 (1 : ℂ)) := by
    simpa only [thetaJet,tsum_ite_eq] using hs
  simpa only [thetaScaledJet,pow_one,mul_zero,mul_one,Complex.ofReal_div,
    Complex.ofReal_ofNat] using ht.const_mul (Real.pi/2 : ℂ)

theorem jacobiNome_high_height : Tendsto jacobiNome atTop (𝓝 (0 : ℂ)) := by
  have he := (Complex.continuous_ofReal.tendsto 0).comp
    (exp_neg_positive_mul_tendsto_zero Real.pi_pos)
  simpa only [Function.comp_def,← jacobiNome_eq_neg_exp,Complex.ofReal_zero,neg_zero] using he.neg

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaScaledJet_one_high_height
