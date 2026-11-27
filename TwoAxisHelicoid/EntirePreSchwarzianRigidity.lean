import TwoAxisHelicoid.UnivalentAnalyticRegularity
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace TwoAxisHelicoid
open Complex Set Function Metric Filter Topology
open scoped Topology

/-- An entire univalent function cannot have a bounded logarithmic
derivative of its derivative with value one at the origin. Liouville
would force the normalized function to be the exponential minus one. -/
theorem normalized_entire_preSchwarzian_impossible {f : ℂ → ℂ}
    (hol : ∀ z, AnalyticAt ℂ f z) (inj : Injective f) (d0 : deriv f 0=1)
    (dd0 : deriv (deriv f) 0=1) (bound : ∀ z, ‖deriv (deriv f) z‖≤2*‖deriv f z‖) : False := by
  have reg (z : ℂ) : deriv f z≠0 :=
    univalent_analytic_deriv_ne_zero isOpen_univ (fun w _ => hol w) inj.injOn (mem_univ z)
  let P := fun z => deriv (deriv f) z / deriv f z
  have dp : Differentiable ℂ P := fun z =>
    ((hol z).deriv.deriv.differentiableAt.div (hol z).deriv.differentiableAt (reg z))
  have bounded : Bornology.IsBounded (range P) := isBounded_closedBall.subset (by
    rintro _ ⟨z,rfl⟩
    apply mem_closedBall_zero_iff.mpr
    rw [show P z=deriv (deriv f) z/deriv f z from rfl,norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr (reg z))).mpr (bound z))
  have ode (z : ℂ) : deriv (deriv f) z=deriv f z := by
    have h := dp.apply_eq_apply_of_bounded bounded z 0
    change deriv (deriv f) z/deriv f z=deriv (deriv f) 0/deriv f 0 at h
    rw [dd0,d0,div_one,div_eq_iff (reg z),one_mul] at h
    exact h
  let H := fun z => deriv f z*Complex.exp (-z)
  have dh (z : ℂ) : HasDerivAt H 0 z := by
    have h := (hol z).deriv.differentiableAt.hasDerivAt.mul
      (Complex.hasDerivAt_exp (-z) |>.comp z (hasDerivAt_id z).neg)
    change HasDerivAt H (deriv (deriv f) z*Complex.exp (-z)+deriv f z*(Complex.exp (-z)*(-1))) z at h
    simpa [ode] using h
  have de (z : ℂ) : deriv f z=Complex.exp z := by
    have h := is_const_of_deriv_eq_zero (fun w => (dh w).differentiableAt) (fun w => (dh w).deriv) z 0
    change deriv f z*Complex.exp (-z)=deriv f 0*Complex.exp (-0) at h
    rw [d0,neg_zero,Complex.exp_zero,one_mul,Complex.exp_neg,← div_eq_mul_inv,div_eq_iff (Complex.exp_ne_zero _),one_mul] at h
    exact h
  have diff (z : ℂ) : HasDerivAt (fun w => f w-Complex.exp w) 0 z := by
    have h := (hol z).differentiableAt.hasDerivAt.sub (Complex.hasDerivAt_exp z)
    change HasDerivAt (fun w => f w-Complex.exp w) (deriv f z-Complex.exp z) z at h
    rwa [de,sub_self] at h
  let w : ℂ := 2*Real.pi*I
  have h := is_const_of_deriv_eq_zero (fun z => (diff z).differentiableAt) (fun z => (diff z).deriv) w 0
  change f w-Complex.exp w=f 0-Complex.exp 0 at h
  rw [show Complex.exp w=1 from Complex.exp_two_pi_mul_I,Complex.exp_zero] at h
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (2:ℂ)≠0) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero)
    (inj (sub_left_inj.mp h))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.normalized_entire_preSchwarzian_impossible
