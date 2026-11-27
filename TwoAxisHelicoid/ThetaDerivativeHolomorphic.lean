import TwoAxisHelicoid.DerivativeExpressions

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaJet thetaA thetaQuotient

theorem thetaAa_differentiableAt {t : ℝ} (ht : 0 < t) (a : ℝ) {z : ℂ}
    (hz : z ∈ thetaRegular t) (hm : z-(a : ℂ) ∈ thetaRegular t) :
    DifferentiableAt ℂ (thetaAa t a) z := by
  have hzj (j : ℕ) : DifferentiableAt ℂ (fun w : ℂ => thetaQuotient t j (Real.pi*w/2)) z := by
    exact (thetaQuotient_hasDerivAt ht j (Real.pi*z/2) hz).differentiableAt.comp z
      (f := fun w : ℂ => Real.pi*w/2) (by fun_prop)
  have hmj (j : ℕ) : DifferentiableAt ℂ (fun w : ℂ => thetaQuotient t j (Real.pi*(w-a)/2)) z := by
    exact (thetaQuotient_hasDerivAt ht j (Real.pi*(z-a)/2) hm).differentiableAt.comp z
      (f := fun w : ℂ => Real.pi*(w-a)/2) (by fun_prop)
  exact (thetaA_differentiableAt ht a hz).mul
    ((((hzj 1).sub (hmj 1)).sub_const _).const_mul _)

theorem thetaAtMidline_differentiableAt {t : ℝ} (ht : 0 < t) (a : ℝ) {z : ℂ}
    (hz : z ∈ thetaRegular t) (hm : z-(a : ℂ) ∈ thetaRegular t) :
    DifferentiableAt ℂ (thetaAtMidline t a) z := by
  have hzj (j : ℕ) : DifferentiableAt ℂ (fun w : ℂ => thetaQuotient t j (Real.pi*w/2)) z := by
    exact (thetaQuotient_hasDerivAt ht j (Real.pi*z/2) hz).differentiableAt.comp z
      (f := fun w : ℂ => Real.pi*w/2) (by fun_prop)
  have hmj (j : ℕ) : DifferentiableAt ℂ (fun w : ℂ => thetaQuotient t j (Real.pi*(w-a)/2)) z := by
    exact (thetaQuotient_hasDerivAt ht j (Real.pi*(z-a)/2) hm).differentiableAt.comp z
      (f := fun w : ℂ => Real.pi*(w-a)/2) (by fun_prop)
  have hlt : DifferentiableAt ℂ (thetaLt t a) z :=
    (((differentiableAt_const _).add (hmj 2) |>.sub (hzj 2)).const_mul _).add
      (((hzj 3).sub ((hzj 1).mul (hzj 2))).const_mul _)
  have hlz : DifferentiableAt ℂ (thetaLz t a) z :=
    (((hmj 1).sub (hzj 1)).const_mul _).add (((hzj 2).sub ((hzj 1).pow 2)).const_mul _)
  exact (thetaA_differentiableAt ht a hz).mul (hlt.add (hlz.const_mul _))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaAtMidline_differentiableAt
