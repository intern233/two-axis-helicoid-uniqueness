import TwoAxisHelicoid.NormalFiberIsotopy
import TwoAxisHelicoid.FiberTriangularLinear
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace TwoAxisHelicoid
open Set
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem normalFiberShift_contDiff {χ : ℝ → ℝ} {u : P → ℝ}
    (hχ : ContDiff ℝ (∞ : WithTop ℕ∞) χ) (hu : ContDiff ℝ (∞ : WithTop ℕ∞) u) (time : ℝ) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (normalFiberShift χ u time) := by
  unfold normalFiberShift scalarFiberShift
  fun_prop

theorem normalFiberShift_hasFDerivAt {χ : ℝ → ℝ} {u : P → ℝ}
    (hχ : Differentiable ℝ χ) (hu : Differentiable ℝ u) (time : ℝ) (x : ℝ × P) :
    HasFDerivAt (normalFiberShift χ u time)
      (fiberTriangularLinear (1+deriv χ x.1*(time*u x.2)) ((time*χ x.1) • fderiv ℝ u x.2)) x := by
  have hs : HasFDerivAt (Prod.fst : ℝ × P → ℝ) (ContinuousLinearMap.fst ℝ ℝ P) x := hasFDerivAt_fst
  have hp : HasFDerivAt (Prod.snd : ℝ × P → P) (ContinuousLinearMap.snd ℝ ℝ P) x := hasFDerivAt_snd
  have hχd := (hχ x.1).hasDerivAt.hasFDerivAt.comp x hs
  have hud := (hu x.2).hasFDerivAt.comp x hp
  have hd := (hs.add (hχd.mul (hud.const_mul time))).prodMk hp
  convert! hd using 1
  ext v <;>
    simp [fiberTriangularLinear,ContinuousLinearMap.smulRight_apply,mul_add,mul_assoc,mul_comm,mul_left_comm]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem normalFiberShift_normal_derivative_pos {χ : ℝ → ℝ} {u : P → ℝ} {C R U time : ℝ}
    (hχ : FiberCutoff χ C R) (hu : ∀ p, |u p| ≤ U) (hsmall : U*C < 1)
    (htime : time ∈ Icc (0 : ℝ) 1) (x : ℝ × P) : 0 < 1+deriv χ x.1*(time*u x.2) := by
  have he : |deriv χ x.1*(time*u x.2)| < 1 := by
    rw [abs_mul,mul_comm]
    exact (mul_le_mul_of_nonneg_left (hχ.derivative_bound x.1) (abs_nonneg _)).trans_lt
      (hχ.small_coefficient hu hsmall htime x.2)
  have hh := (abs_lt.mp he).1
  linarith

variable [ProperSpace P]

/-- The inverse of each actual normal-fiber homeomorphism is smooth.
Invertibility of its triangular derivative is proved, not assumed. -/
theorem normalFiberHomeomorph_symm_contDiff {χ : ℝ → ℝ} {C R U time : ℝ}
    (hχ : FiberCutoff χ C R) {u : P → ℝ}
    (hχs : ContDiff ℝ (∞ : WithTop ℕ∞) χ) (hus : ContDiff ℝ (∞ : WithTop ℕ∞) u)
    (hu : ∀ p, |u p| ≤ U) (hsmall : U*C < 1) (htime : time ∈ Icc (0 : ℝ) 1) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (normalFiberHomeomorph hχ hus.continuous hu hsmall htime).symm := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  let H := normalFiberHomeomorph hχ hus.continuous hu hsmall htime
  let x := H.symm y
  let D := fiberTriangularLinearEquiv (1+deriv χ x.1*(time*u x.2))
    ((time*χ x.1) • fderiv ℝ u x.2)
    (ne_of_gt (normalFiberShift_normal_derivative_pos hχ hu hsmall htime x))
  apply H.toOpenPartialHomeomorph.contDiffAt_symm (f₀' := D)
  · exact mem_univ y
  · exact normalFiberShift_hasFDerivAt hχ.differentiable (hus.differentiable (by simp)) time x
  · exact (normalFiberShift_contDiff hχs hus time).contDiffAt

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.normalFiberHomeomorph_symm_contDiff
