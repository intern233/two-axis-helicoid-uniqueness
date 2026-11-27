import TwoAxisHelicoid.ThetaConvergence
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.RealDeriv

/-! The normalized heat equation (9.3), justified by a summable derivative majorant. -/

namespace TwoAxisHelicoid
open Complex Set

theorem sineJet_add_two (j : ℕ) (z : ℂ) : sineJet (j+2) z = -sineJet j z := by
  simp only [sineJet, pow_add]
  norm_num
  ring

theorem thetaTerm_add_two (t : ℝ) (j n : ℕ) (v : ℂ) :
    thetaTerm t (j+2) n v = -(2*n+1 : ℂ)^2 * thetaTerm t j n v := by
  simp only [thetaTerm, pow_add, sineJet_add_two]
  ring

theorem thetaTerm_heat_identity (t : ℝ) (j n : ℕ) (v : ℂ) :
    (Real.pi / 8 : ℂ) * (thetaTerm t (j+2) n v + thetaTerm t j n v) =
      (-Real.pi * n * (n+1) / 2 : ℂ) * thetaTerm t j n v := by
  rw [thetaTerm_add_two]
  ring

theorem hasDerivAt_thetaTerm_parameter (t : ℝ) (j n : ℕ) (v : ℂ) :
    HasDerivAt (fun s : ℝ => thetaTerm s j n v)
      ((Real.pi / 8 : ℂ) * (thetaTerm t (j+2) n v + thetaTerm t j n v)) t := by
  have ha : HasDerivAt (fun s : ℝ => -Real.pi*s*n*(n+1)/2)
      (-Real.pi*n*(n+1)/2) t := by
    convert ((((hasDerivAt_id t).const_mul (-Real.pi)).mul_const (n : ℝ)).mul_const
      (n+1)).div_const 2 using 1 <;> simp
  have hd := (((ha.exp.ofReal_comp).const_mul (thetaSign n)).mul_const
    ((2*n+1 : ℂ)^j)).mul_const (sineJet j ((2*n+1 : ℂ)*v))
  rw [thetaTerm_heat_identity]
  convert hd using 1
  · rfl
  · simp only [thetaTerm]
    push_cast
    ring

theorem theta_parameter_derivative_bound {t tlo : ℝ} (ht : tlo ≤ t)
    (j n : ℕ) (v : ℂ) :
    ‖(Real.pi / 8 : ℂ) * (thetaTerm t (j+2) n v + thetaTerm t j n v)‖ ≤
      (Real.pi / 8) * (thetaMajorant tlo |v.im| (j+2) n + thetaMajorant tlo |v.im| j n) := by
  have hp : ‖(Real.pi / 8 : ℂ)‖ = Real.pi / 8 := by
    norm_num [norm_div, Complex.norm_of_nonneg Real.pi_pos.le]
  rw [norm_mul, hp]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_add_le _ _).trans
    (add_le_add (thetaTerm_norm_le ht le_rfl (j+2) n) (thetaTerm_norm_le ht le_rfl j n))

/-- The heat equation holds for every derivative order and every complex spatial argument. -/
theorem thetaJet_parameter_hasDerivAt {t : ℝ} (ht : 0 < t) (j : ℕ) (v : ℂ) :
    HasDerivAt (fun s : ℝ => thetaJet s j v)
      ((Real.pi / 8 : ℂ) * (thetaJet t (j+2) v + thetaJet t j v)) t := by
  let U : Set ℝ := Ioi (t/2)
  have htlo : 0 < t/2 := by positivity
  have hmem : t ∈ U := by change t/2 < t; linarith
  have hmaj := ((thetaMajorant_summable htlo |v.im| (j+2)).add
    (thetaMajorant_summable htlo |v.im| j)).mul_left (Real.pi/8)
  have hd := hasDerivAt_tsum_of_isPreconnected hmaj isOpen_Ioi isPreconnected_Ioi
    (fun n s (_ : s ∈ U) => hasDerivAt_thetaTerm_parameter s j n v)
    (fun n s (hs : s ∈ U) => theta_parameter_derivative_bound hs.le j n v)
    hmem (thetaTerm_summable ht j v) hmem
  convert hd using 1
  · rfl
  · rw [tsum_mul_left, Summable.tsum_add (thetaTerm_summable ht (j+2) v)
        (thetaTerm_summable ht j v)]
    rfl

theorem theta_heat_equation {t : ℝ} (ht : 0 < t) (v : ℂ) :
    deriv (fun s : ℝ => thetaJet s 0 v) t =
      (Real.pi / 8 : ℂ) * (iteratedDeriv 2 (thetaJet t 0) v + thetaJet t 0 v) := by
  rw [thetaJet_iteratedDeriv ht]
  exact (thetaJet_parameter_hasDerivAt ht 0 v).deriv

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.theta_heat_equation
