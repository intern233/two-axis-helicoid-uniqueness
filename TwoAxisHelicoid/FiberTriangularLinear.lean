import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic

namespace TwoAxisHelicoid

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def fiberTriangularLinear (a : ℝ) (b : P →L[ℝ] ℝ) :
    (ℝ × P) →L[ℝ] (ℝ × P) :=
  ((ContinuousLinearMap.fst ℝ ℝ P).smulRight a+b.comp (ContinuousLinearMap.snd ℝ ℝ P)).prod
    (ContinuousLinearMap.snd ℝ ℝ P)

theorem fiberTriangularLinear_apply (a : ℝ) (b : P →L[ℝ] ℝ) (x : ℝ × P) :
    fiberTriangularLinear a b x = (a*x.1+b x.2,x.2) := by
  change (x.1*a+b x.2,x.2) = (a*x.1+b x.2,x.2)
  rw [mul_comm x.1 a]

noncomputable def fiberTriangularLinearEquiv (a : ℝ) (b : P →L[ℝ] ℝ) (ha : a ≠ 0) :
    (ℝ × P) ≃L[ℝ] (ℝ × P) where
  toLinearEquiv :=
    { (fiberTriangularLinear a b).toLinearMap with
      invFun := fun x => ((x.1-b x.2)/a,x.2)
      left_inv := by
        intro x
        change (((fiberTriangularLinear a b x).1-b (fiberTriangularLinear a b x).2)/a,
          (fiberTriangularLinear a b x).2) = x
        rw [fiberTriangularLinear_apply]
        apply Prod.ext
        · dsimp only
          field_simp
          ring
        · rfl
      right_inv := by
        intro x
        change fiberTriangularLinear a b ((x.1-b x.2)/a,x.2) = x
        rw [fiberTriangularLinear_apply]
        apply Prod.ext
        · dsimp only
          field_simp
          ring
        · rfl }
  continuous_toFun := (fiberTriangularLinear a b).continuous
  continuous_invFun := by
    change Continuous (fun x : ℝ × P => ((x.1-b x.2)/a,x.2))
    fun_prop

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.fiberTriangularLinearEquiv
