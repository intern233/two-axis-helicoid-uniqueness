import TwoAxisHelicoid.PolynomialHeightDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace TwoAxisHelicoid
open Complex Set Metric Filter
open scoped Topology

/-- Exponential growth of the real part of a holomorphic primitive
gives a finite-order exponential bound on its complex derivative.
No estimates for the imaginary part are used. -/
theorem derivative_of_exponential_real_growth {H : ℂ → ℂ} {R C A : ℝ} (hC : 0<C) (hA : 0<A) (N : ℕ)
    (diff : ∀ z : ℂ, 0<‖z‖ → ‖z‖<R → DifferentiableAt ℂ H z)
    (growth : ∀ z : ℂ, 0<‖z‖ → ‖z‖<R → |(H z).re|≤A*Real.exp (C/‖z‖^N))
    {z : ℂ} (nz : 0<‖z‖) (small : ‖z‖<R/2) (unit : ‖z‖≤1) :
    ‖deriv H z‖≤Real.exp ((16*A+2^N*C)/‖z‖^(N+1)) := by
  let s := ‖z‖
  let r := s/2
  have pr : 0<r := half_pos nz
  have near (w : ℂ) (hw : w∈ball z r) : r≤‖w‖ ∧ ‖w‖<R := by
    have d : ‖w-z‖<r := by simpa only [mem_ball,dist_eq_norm] using hw
    have a := norm_sub_norm_le w z
    have b := norm_sub_norm_le z w
    rw [norm_sub_rev] at b
    dsimp [r,s] at *
    constructor <;> linarith
  have mx := derivative_bound_of_bounded_real_part (H := H) (z := z) pr (mul_pos hA (Real.exp_pos (C/r^N)))
    (fun w hw => (diff w (pr.trans_le (near w hw).1) (near w hw).2).differentiableWithinAt)
    (fun w hw => (growth w (pr.trans_le (near w hw).1) (near w hw).2).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hC.le (pow_pos pr _)
        (pow_le_pow_left₀ pr.le (near w hw).1 _))) hA.le))
  have power : C/r^N=2^N*C/s^N := by dsimp [r]; rw [div_pow]; field_simp
  have mul : 8*(A*Real.exp (C/r^N))/r=(16*A/s)*Real.exp (2^N*C/s^N) := by rw [power]; dsimp [r]; ring
  have sh : s^(N+1)≤s^N := by rw [pow_succ]; exact (mul_le_mul_of_nonneg_left unit (pow_nonneg nz.le _)).trans_eq (mul_one _)
  have ss : s^(N+1)≤s := by rw [pow_succ]; exact (mul_le_mul_of_nonneg_right (pow_le_one₀ nz.le unit) nz.le).trans_eq (one_mul _)
  have fac : 16*A/s≤Real.exp (16*A/s) := by linarith [Real.add_one_le_exp (16*A/s)]
  have c1 := div_le_div_of_nonneg_left (show 0≤16*A by positivity) (pow_pos nz _) ss
  have c2 := div_le_div_of_nonneg_left (show 0≤2^N*C by positivity) (pow_pos nz _) sh
  calc
    ‖deriv H z‖ ≤ (16*A/s)*Real.exp (2^N*C/s^N) := mx.trans_eq mul
    _ ≤ Real.exp (16*A/s)*Real.exp (2^N*C/s^N) := mul_le_mul_of_nonneg_right fac (Real.exp_pos _).le
    _ ≤ _ := by rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; rw [add_div]; exact add_le_add c1 c2

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.derivative_of_exponential_real_growth
