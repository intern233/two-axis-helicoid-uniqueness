import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Filter Metric
open scoped Topology

/-- Absorbing the differentiability remainder gives a quantitative local
estimate from the stated linear a priori estimate. No Fredholm or
surjectivity assumption is needed. -/
theorem differentiable_coercive_local_estimate
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M : E → F} {L : E →L[ℝ] F} {C : ℝ}
    (hM : HasFDerivAt M L 0) (h0 : M 0 = 0) (hC : 0 < C)
    (hcoercive : ∀ u, ‖u‖ ≤ C*‖L u‖) :
    ∀ᶠ u in 𝓝 (0 : E), ‖u‖ ≤ 2*C*‖M u‖ := by
  have hR := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hM).bound
    (show 0 < (2*C)⁻¹ by positivity)
  filter_upwards [hR] with u hu
  simp only [zero_add,h0,sub_zero] at hu
  have hhalf : C*‖M u-L u‖ ≤ ‖u‖/2 := by
    calc
      _ ≤ C*((2*C)⁻¹*‖u‖) := mul_le_mul_of_nonneg_left hu hC.le
      _ = _ := by field_simp
  have htriangle : ‖L u‖ ≤ ‖M u‖+‖M u-L u‖ := norm_le_insert (M u) (L u)
  have hbound := mul_le_mul_of_nonneg_left htriangle hC.le
  nlinarith [hcoercive u]

/-- The conditional local rigidity criterion of Appendix D.4, in its stated
Banach-space abstraction. The estimate for a particular geometric Jacobi
operator is deliberately not supplied as an axiom. -/
theorem differentiable_coercive_isolated_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M : E → F} {L : E →L[ℝ] F} {C : ℝ}
    (hM : HasFDerivAt M L 0) (h0 : M 0 = 0)
    (hcoercive : ∀ u, ‖u‖ ≤ C*‖L u‖) :
    ∃ r > 0, ∀ u, ‖u‖ < r → M u = 0 → u = 0 := by
  have hCp : 0 < max C 1 := lt_of_lt_of_le (by norm_num) (le_max_right C 1)
  have hco : ∀ u, ‖u‖ ≤ max C 1*‖L u‖ := fun u =>
    (hcoercive u).trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (norm_nonneg _))
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp
    (differentiable_coercive_local_estimate hM h0 hCp hco)
  refine ⟨r,hr,?_⟩
  intro u hu hzero
  have he := hsub (show u ∈ ball (0 : E) r by simpa using hu)
  change ‖u‖ ≤ 2*max C 1*‖M u‖ at he
  rw [hzero,norm_zero,mul_zero] at he
  exact norm_eq_zero.mp (le_antisymm he (norm_nonneg _))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.differentiable_coercive_isolated_zero
