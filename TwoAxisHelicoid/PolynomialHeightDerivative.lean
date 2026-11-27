import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue

namespace TwoAxisHelicoid
open Complex Set Metric Filter
open scoped Topology

/-- A bound on the real part in a disk controls the complex
derivative at its center without an imaginary-part hypothesis. -/
theorem derivative_bound_of_bounded_real_part {H : ℂ → ℂ} {z : ℂ} {R M : ℝ}
    (hR : 0<R) (hM : 0<M) (diff : DifferentiableOn ℂ H (ball z R))
    (bound : ∀ w∈ball z R, |(H w).re|≤M) : ‖deriv H z‖≤8*M/R := by
  let f := fun w : ℂ => H (z+w)-H z
  have inBall {w : ℂ} (hw : w∈ball (0:ℂ) R) : z+w∈ball z R := by
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hw
  have df : DifferentiableOn ℂ f (ball (0:ℂ) R) := by
    intro w hw
    exact ((diff.differentiableAt (isOpen_ball.mem_nhds (inBall hw))).comp w
      ((hasDerivAt_id w).const_add z).differentiableAt).sub_const _ |>.differentiableWithinAt
  have upper : MapsTo f (ball (0:ℂ) R) {q : ℂ | q.re≤2*M} := by
    intro w hw
    change (H (z+w)-H z).re≤2*M
    rw [sub_re]
    linarith [(abs_le.mp (bound _ (inBall hw))).2,(abs_le.mp (bound z (mem_ball_self hR))).1]
  have zero : f 0=0 := by simp [f]
  have est : ‖deriv f 0‖≤8*M/R := by
    apply norm_deriv_le_of_lip' (by positivity)
    filter_upwards [ball_mem_nhds (0:ℂ) (half_pos hR)] with w hw
    have small : ‖w‖<R/2 := by simpa only [mem_ball,dist_zero_right] using hw
    have rad : R/2≤R-‖w‖ := by linarith
    have b := Complex.borelCaratheodory_zero (mul_pos (by norm_num) hM) df upper hR
      (ball_subset_ball (half_le_self hR.le) hw) zero
    rw [zero,sub_zero,sub_zero]
    apply b.trans
    rw [div_le_iff₀ ((half_pos hR).trans_le rad)]
    have cmp := mul_le_mul_of_nonneg_left rad (show 0≤(8*M/R)*‖w‖ by positivity)
    calc
      2*(2*M)*‖w‖ = (8*M/R)*‖w‖*(R/2) := by field_simp; ring
      _ ≤ _ := cmp
  have atZ := (diff.differentiableAt (ball_mem_nhds _ hR)).hasDerivAt
  have fd : HasDerivAt f (deriv H z) 0 := by
    have base : HasDerivAt H (deriv H z) (z+0) := by simpa only [add_zero] using atZ
    have tr := base.comp_const_add (x := (0:ℂ)) (a := z)
    simpa [f] using! tr.sub_const (H z)
  rwa [fd.deriv] at est

/-- Polynomial growth of the real height in a punctured coordinate
gives a polynomial bound on its holomorphic derivative. -/
theorem polynomial_real_height_derivative_bound {H : ℂ → ℂ} {R C : ℝ} (hC : 0<C) (N : ℕ)
    (diff : ∀ z : ℂ, 0<‖z‖ → ‖z‖<R → DifferentiableAt ℂ H z)
    (bound : ∀ z : ℂ, 0<‖z‖ → ‖z‖<R → |(H z).re|≤C/‖z‖^N)
    {z : ℂ} (nz : 0<‖z‖) (small : ‖z‖<R/2) :
    ‖deriv H z‖≤(16*2^N*C)/‖z‖^(N+1) := by
  let r := ‖z‖/2
  have hr : 0<r := half_pos nz
  have ann {w : ℂ} (hw : w∈ball z r) : r≤‖w‖ ∧ ‖w‖<R := by
    have d : ‖w-z‖<r := by simpa only [mem_ball,dist_eq_norm] using hw
    have f := norm_sub_norm_le w z
    have g := norm_sub_norm_le z w
    rw [norm_sub_rev] at g
    dsimp [r] at *
    constructor <;> linarith
  have estimate := derivative_bound_of_bounded_real_part (H := H) (z := z) hr (div_pos hC (pow_pos hr N))
    (fun w hw => (diff _ (hr.trans_le (ann hw).1) (ann hw).2).differentiableWithinAt)
    (fun w hw => (bound _ (hr.trans_le (ann hw).1) (ann hw).2).trans
      (div_le_div_of_nonneg_left hC.le (pow_pos hr _) (pow_le_pow_left₀ hr.le (ann hw).1 _)))
  apply estimate.trans_eq
  dsimp [r]
  rw [div_pow,pow_succ]
  field_simp
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.polynomial_real_height_derivative_bound
