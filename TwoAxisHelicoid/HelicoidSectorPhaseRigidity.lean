import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Set Filter Complex
open scoped Topology

/-- A fixed-frequency complex rotation having a nonzero limit has zero
frequency. Translation of the real parameter leaves the limit unchanged. -/
theorem constant_phase_of_limit {C : ℂ} {v : ℝ}
    (h : Tendsto (fun t : ℝ => C*exp (((v*t:ℝ):ℂ)*I)) atTop (𝓝 1)) : v=0 ∧ C=1 := by
  have zero : v=0 := by
    by_contra nz
    let s := Real.pi/v
    have sh : Tendsto (fun t : ℝ => t+s) atTop atTop := tendsto_id.atTop_add tendsto_const_nhds
    have other : Tendsto (fun t : ℝ => C*exp (((v*(t+s):ℝ):ℂ)*I)) atTop (𝓝 (-1)) := by
      apply (show Tendsto (fun t : ℝ => (C*exp (((v*t:ℝ):ℂ)*I))*(-1)) atTop (𝓝 (-1)) by simpa only [one_mul] using h.mul_const (-1)).congr
      intro t
      have vs : v*s=Real.pi := by dsimp [s]; field_simp
      rw [mul_add,vs,ofReal_add,add_mul,exp_add,exp_pi_mul_I,mul_assoc]
    exact (by norm_num : (1:ℂ)≠ -1) (tendsto_nhds_unique (h.comp sh) other)
  refine ⟨zero,?_⟩
  have k : Tendsto (fun _ : ℝ => C) atTop (𝓝 1) := by simpa only [zero,zero_mul,ofReal_zero,exp_zero,mul_one] using h
  exact tendsto_nhds_unique tendsto_const_nhds k

/-- The directions of horizontal positions in the positive exponential
half-plane determine the full linear coefficient and rule out every
nonzero winding power. Two directions suffice for the linear part.
The shifted real line then detects the integer by differentiation. -/
theorem helicoid_sector_phase_determines_both_coefficients {c K : ℂ} (nc : c≠0) (nK : K≠0) (m : ℤ)
    (rays : ∀ z : ℂ, 0<(c*z).re → (c*z).im=z.re ∧ (K*z^m).im=0) : c=I ∧ m=0 := by
  have first : (c⁻¹).re=0 := by
    have h := (rays c⁻¹ (by rw [mul_inv_cancel₀ nc]; norm_num)).1
    simpa only [mul_inv_cancel₀ nc,one_im] using h.symm
  have one : c*((1+I)*c⁻¹)=1+I := by field_simp
  have second := (rays ((1+I)*c⁻¹) (by rw [one]; norm_num)).1
  rw [one,add_mul,one_mul,Complex.add_re,Complex.I_mul_re,first,Complex.add_im,Complex.one_im,Complex.I_im] at second
  have inv : c⁻¹= -I := Complex.ext (by simpa using first) (by simpa using (show (c⁻¹).im= -1 by linarith))
  have eq : c=I := by simpa using congrArg Inv.inv inv
  refine ⟨eq,?_⟩
  subst c
  let z : ℂ := -I
  have nz : z≠0 := neg_ne_zero.mpr I_ne_zero
  let R := K*z^m
  have rN : R≠0 := mul_ne_zero nK (zpow_ne_zero _ nz)
  have real (t : ℝ) : (K*((t:ℂ)-I)^m).im=0 := (rays _ (by simp)).2
  have ri : R.im=0 := by simpa [R,z] using real 0
  have rr : R.re≠0 := fun h => rN (Complex.ext h ri)
  have path : HasDerivAt (fun t : ℝ => (t:ℂ)-I) 1 0 := Complex.ofRealCLM.hasDerivAt.sub_const I
  have pp : HasDerivAt (fun a : ℂ => a^m) ((m:ℂ)*z^(m-1)) (((0:ℝ):ℂ)-I) := by simpa only [ofReal_zero,zero_sub] using hasDerivAt_zpow m z (Or.inl nz)
  have d := (pp.scomp (0:ℝ) path).const_mul K
  have derivative : HasDerivAt (fun t : ℝ => K*((t:ℂ)-I)^m) (K*((m:ℂ)*z^(m-1))) 0 := by simpa using d
  have imag := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 derivative
  have value : (K*((m:ℂ)*z^(m-1))).im=0 := (imag.congr_of_eventuallyEq (Eventually.of_forall (fun t => (real t).symm))).unique (hasDerivAt_const _ _)
  have factor : K*((m:ℂ)*z^(m-1))=(m:ℂ)*I*R := by
    rw [zpow_sub₀ nz,zpow_one,div_eq_mul_inv]
    have zi : z⁻¹=I := by simp [z]
    rw [zi]
    dsimp [R]
    ring
  rw [factor] at value
  have prod : (m:ℝ)*R.re=0 := by simpa [Complex.mul_re,Complex.mul_im] using value
  exact_mod_cast (mul_eq_zero.mp prod).resolve_right rr

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.constant_phase_of_limit
#print axioms TwoAxisHelicoid.helicoid_sector_phase_determines_both_coefficients
