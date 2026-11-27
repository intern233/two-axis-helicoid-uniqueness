import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.CauchyIntegral

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped Topology

/-- A uniform bound on the logarithmic derivative propagates a
derivative estimate along every straight radius of a coordinate disk. -/
theorem holomorphic_derivative_growth {f : ℂ → ℂ} {a : ℂ} {r K : ℝ}
    (hol : AnalyticOnNhd ℂ f (ball a r)) (bound : ∀ w∈ball a r, ‖deriv (deriv f) w‖≤K*‖deriv f w‖)
    {z : ℂ} (hz : z∈ball a r) :
    ‖deriv f z‖≤‖deriv f a‖*Real.exp (K*‖z-a‖) := by
  let v := z-a
  let γ := fun t : ℝ => a+(t:ℂ)*v
  have inside (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : γ t∈ball a r := by
    rw [mem_ball,dist_eq_norm]
    change ‖a+(t:ℂ)*v-a‖<r
    rw [add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt (by simpa [mem_ball,dist_eq_norm,v] using hz)
  have g0 : γ 0=a := by simp [γ]
  have g1 : γ 1=z := by simp [γ,v]
  let G := fun t => deriv f (γ t)
  let D := fun t => deriv (deriv f) (γ t)*v
  have dh (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt G (D t) t := by
    have affine : HasDerivAt (fun u : ℂ => a+u*v) v (t:ℂ) := by
      simpa using ((hasDerivAt_id (t:ℂ)).mul_const v).const_add a
    exact (((hol _ (inside t ht)).deriv.differentiableAt.hasDerivAt.comp (t:ℂ) affine).comp_ofReal)
  have at0 : ‖G 0‖≤‖deriv f a‖ := by simp [G,g0]
  have grow := norm_le_gronwallBound_of_norm_deriv_right_le (fun t ht => (dh t ht).continuousAt.continuousWithinAt)
    (fun t ht => (dh t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt) at0
    (K:=K*‖v‖) (ε:=0) (fun t ht => by
      change ‖deriv (deriv f) (γ t)*v‖≤K*‖v‖*‖deriv f (γ t)‖+0
      rw [norm_mul,add_zero,mul_right_comm]
      exact mul_le_mul_of_nonneg_right (bound _ (inside t ⟨ht.1,ht.2.le⟩)) (norm_nonneg _))
    1 (right_mem_Icc.mpr zero_le_one)
  simpa [G,g1,v,gronwallBound_ε0] using grow

/-- The same estimate bounds all function values on the disk using
only its radius, central first jet, and the logarithmic derivative. -/
theorem holomorphic_value_growth {f : ℂ → ℂ} {a : ℂ} {r K : ℝ} (kn : 0≤K)
    (hol : AnalyticOnNhd ℂ f (ball a r)) (bound : ∀ w∈ball a r, ‖deriv (deriv f) w‖≤K*‖deriv f w‖)
    {z : ℂ} (hz : z∈ball a r) :
    ‖f z‖≤‖f a‖+‖deriv f a‖*Real.exp (K*r)*r := by
  have rp : 0<r := dist_nonneg.trans_lt hz
  have lim (w : ℂ) (hw : w∈ball a r) : ‖deriv f w‖≤‖deriv f a‖*Real.exp (K*r) :=
    (holomorphic_derivative_growth hol bound hw).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (show ‖w-a‖≤r by simpa only [← dist_eq_norm] using (mem_ball.mp hw).le) kn)) (norm_nonneg _))
  have h := (convex_ball a r).norm_image_sub_le_of_norm_deriv_le (𝕜:=ℂ)
    (fun w hw => (hol w hw).differentiableAt) lim (mem_ball_self rp) hz
  have eq : f z=(f z-f a)+f a := by abel
  calc
    ‖f z‖ = ‖(f z-f a)+f a‖ := congrArg norm eq
    _ ≤ ‖f z-f a‖+‖f a‖ := norm_add_le _ _
    _ ≤ ‖f a‖+‖deriv f a‖*Real.exp (K*r)*r := by
      linarith [h.trans (mul_le_mul_of_nonneg_left (show ‖z-a‖≤r by simpa only [← dist_eq_norm] using (mem_ball.mp hz).le)
        (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le))]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.holomorphic_value_growth
