import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex
open scoped ComplexConjugate

/-- Normalize the first nonzero coefficients of the two horizontal
primitives and the height primitive at a simple zero of the Gauss map.
The relation follows from the null identity for the three derivatives.
A complex rescaling of the parameter puts the limiting cubic in Enneper
form with positive vertical scale. -/
theorem lopez_ros_enneper_leading_coefficients {a b c : ℂ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hnull : 3*a*b + 4*c^2 = 0) :
    ∃ (ρ : ℂ) (d : ℝ), ρ ≠ 0 ∧ 0 < d ∧ c*ρ^2 = (d:ℂ) ∧ 3*a*ρ^3 = -conj (b*ρ) := by
  let d : ℝ := ‖b‖^2/(4*‖c‖)
  have hb' := norm_pos_iff.mpr hb
  have hc' := norm_pos_iff.mpr hc
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨ρ,hρ⟩ := IsAlgClosed.exists_pow_nat_eq ((d:ℂ)/c) (by decide : 0 < 2)
  have hcr : c*ρ^2 = (d:ℂ) := by rw [hρ]; field_simp
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h,zero_pow (by decide),mul_zero] at hcr
    exact (Complex.ofReal_ne_zero.mpr hd.ne') hcr.symm
  have hscale : ‖c‖*‖ρ‖^2 = d := by
    simpa only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd] using congrArg norm hcr
  have hb2 : ‖b‖^2 = 4*‖c‖*d := by dsimp [d]; field_simp
  have hmag : ‖b*ρ‖^2 = 4*d^2 := by
    rw [norm_mul,mul_pow,hb2]
    calc
      _ = 4*d*(‖c‖*‖ρ‖^2) := by ring
      _ = 4*d^2 := by rw [hscale]; ring
  have hnorm : conj (b*ρ)*(b*ρ) = 4*(d:ℂ)^2 := by
    rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,hmag]
    push_cast
    rfl
  refine ⟨ρ,d,hρ0,hd,hcr,?_⟩
  apply mul_right_cancel₀ (mul_ne_zero hb hρ0)
  calc
    3*a*ρ^3*(b*ρ) = (3*a*b)*ρ^4 := by ring
    _ = -(4*(c*ρ^2)^2) := by linear_combination ρ^4*hnull
    _ = -conj (b*ρ)*(b*ρ) := by rw [hcr,neg_mul,hnorm]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lopez_ros_enneper_leading_coefficients
