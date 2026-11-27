import TwoAxisHelicoid.ComplexExteriorConnected

namespace TwoAxisHelicoid
open Complex Set

/-- The actual third coordinate is forced by the Weierstrass differential
on the connected exterior. It is not a separate geometric hypothesis. -/
theorem height_end_third_coordinate {X : ℂ → Fin 3 → ℝ} {g : ℂ → ℂ}
    {R : ℝ} (hR : 0 ≤ R)
    (hX : ∀ z : ℂ, R < ‖z‖ → HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (g z) 1)) z) :
    ∃ b : ℝ, ∀ z : ℂ, R < ‖z‖ → X z 2 = z.re+b := by
  have hd (z : ℂ) (hz : R < ‖z‖) :
      HasFDerivAt (fun w => X w 2) Complex.reCLM z := by
    have h := (ContinuousLinearMap.proj 2 : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z (hX z hz)
    have he : (ContinuousLinearMap.proj 2 : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
        (nullRealDerivative (weierstrassTriple (g z) 1)) = Complex.reCLM := by
      ext w
      change (w*1).re = w.re
      rw [mul_one]
    simpa only [he,Function.comp_def] using! h
  exact (isOpen_lt continuous_const continuous_norm).exists_eq_add_of_fderiv_eq
    (complex_norm_exterior_isPreconnected hR)
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z _ => Complex.reCLM.differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).fderiv.trans
      (show HasFDerivAt Complex.re Complex.reCLM z from Complex.reCLM.hasFDerivAt).fderiv.symm)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.height_end_third_coordinate
