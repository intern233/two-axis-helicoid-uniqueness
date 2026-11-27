import TwoAxisHelicoid.NormalFiberHomeomorph
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace TwoAxisHelicoid
open Set Metric
open scoped Topology ContDiff

/-- A concrete smooth cutoff, equal to one on the quarter tube and zero
outside the half tube. -/
noncomputable def normalStraighteningCutoff : ContDiffBump (0 : ℝ) :=
  ⟨1/4,1/2,by norm_num,by norm_num⟩

theorem normalStraighteningCutoff_contDiff :
    ContDiff ℝ (∞ : WithTop ℕ∞) normalStraighteningCutoff := normalStraighteningCutoff.contDiff

theorem normalStraighteningCutoff_one {s : ℝ} (hs : |s| ≤ 1/4) :
    normalStraighteningCutoff s = 1 := by
  apply normalStraighteningCutoff.one_of_mem_closedBall
  simpa only [mem_closedBall,dist_zero_right,Real.norm_eq_abs,normalStraighteningCutoff] using hs

/-- The derivative bound required for the fiber isotopy exists for the
actual chosen smooth cutoff, by compactness of its derivative's support. -/
theorem normalStraighteningCutoff_exists_bound :
    ∃ C : ℝ, 0 < C ∧ FiberCutoff normalStraighteningCutoff C (1/2) := by
  have hd := normalStraighteningCutoff_contDiff.continuous_deriv (by simp)
  obtain ⟨B,hB⟩ := (normalStraighteningCutoff.hasCompactSupport.deriv.isCompact_range hd).isBounded.exists_norm_le
  refine ⟨max B 1,zero_lt_one.trans_le (le_max_right _ _),?_⟩
  refine ⟨normalStraighteningCutoff_contDiff.differentiable (by simp),?_,?_,by norm_num,?_,?_⟩
  · intro s
    have hs := hB (deriv normalStraighteningCutoff s) ⟨s,rfl⟩
    exact (show |deriv normalStraighteningCutoff s| ≤ B by simpa only [Real.norm_eq_abs] using hs).trans
      (le_max_left _ _)
  · intro s
    rw [abs_of_nonneg normalStraighteningCutoff.nonneg]
    exact normalStraighteningCutoff.le_one
  · intro s hs
    apply normalStraighteningCutoff.zero_of_le_dist
    simpa only [dist_zero_right,Real.norm_eq_abs,normalStraighteningCutoff] using hs
  · exact normalStraighteningCutoff_one (by norm_num)

theorem normalStraighteningCutoff_small_graph_size :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ 1/4 ∧ δ*C < 1 ∧
      FiberCutoff normalStraighteningCutoff C (1/2) := by
  obtain ⟨C,hC,hχ⟩ := normalStraighteningCutoff_exists_bound
  let δ : ℝ := min (1/4) (1/(2*C))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  refine ⟨C,δ,hC,hδ,min_le_left _ _,?_,hχ⟩
  have hbound := mul_le_mul_of_nonneg_right (min_le_right (1/4 : ℝ) (1/(2*C))) hC.le
  have he : (1/(2*C))*C = 1/2 := by field_simp
  rw [he] at hbound
  exact hbound.trans_lt (by norm_num)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.normalStraighteningCutoff_small_graph_size
