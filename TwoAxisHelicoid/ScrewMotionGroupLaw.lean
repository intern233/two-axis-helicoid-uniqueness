import TwoAxisHelicoid.NonperiodicCompactnessCutoffs

namespace TwoAxisHelicoid
open Complex Set Topology

theorem unit_screw_coordinates (t : ℝ) (p : Fin 3 → ℝ) :
    unitHelicoidScrew t p=![Real.cos (2*t)*p 0-Real.sin (2*t)*p 1,
      Real.sin (2*t)*p 0+Real.cos (2*t)*p 1,p 2+2*t] := by
  change verticalRotation (exp ((2*t:ℝ)*I)) p+![0,0,2*t]=_
  rw [verticalRotation_apply,exp_ofReal_mul_I_re,exp_ofReal_mul_I_im]
  ext j
  fin_cases j <;> simp

theorem unit_screw_add (t u : ℝ) (p : Fin 3 → ℝ) :
    unitHelicoidScrew (t+u) p=unitHelicoidScrew t (unitHelicoidScrew u p) := by
  rw [unit_screw_coordinates,unit_screw_coordinates,unit_screw_coordinates]
  simp only [mul_add,Real.cos_add,Real.sin_add]
  ext j
  fin_cases j <;> simp <;> ring

theorem unit_screw_jointly_continuous :
    Continuous (fun p : ℝ × (Fin 3 → ℝ) => unitHelicoidScrew p.1 p.2) := by
  simp only [unit_screw_coordinates]
  apply continuous_pi
  intro j
  fin_cases j <;> simp <;> fun_prop

theorem unit_screw_inverse_is_negative (h : ℝ) (p : Fin 3 → ℝ) :
    (unitHelicoidScrew h).symm p = unitHelicoidScrew (-h) p := by
  apply (unitHelicoidScrew h).injective
  rw [Homeomorph.apply_symm_apply,←unit_screw_add,add_neg_cancel,unit_screw_coordinates]
  ext i
  fin_cases i <;> simp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.unit_screw_add
#print axioms TwoAxisHelicoid.unit_screw_jointly_continuous
#print axioms TwoAxisHelicoid.unit_screw_inverse_is_negative
