import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Set Metric Filter
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

/-- A bounded smooth function defined near infinity admits a bounded
global smooth extension agreeing with it outside a slightly larger disk.
No regularity of the supplied function inside the original disk is used. -/
theorem bounded_smooth_exterior_extension {G : ℂ → ℂ} {R L : ℝ}
    (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hG : ∀ z : ℂ, R < ‖z‖ → ContDiffAt ℝ (∞ : WithTop ℕ∞) G z)
    (hbound : ∀ z : ℂ, R < ‖z‖ → ‖G z‖ ≤ L) :
    ∃ F : ℂ → ℂ, ContDiff ℝ (∞ : WithTop ℕ∞) F ∧
      (∀ z, ‖F z‖ ≤ L) ∧ ∀ z : ℂ, R+2 ≤ ‖z‖ → F z = G z := by
  let b : ContDiffBump (0 : ℂ) := ⟨R+1,R+2,by linarith,by linarith⟩
  let F : ℂ → ℂ := fun z => (1-b z) • G z
  refine ⟨F,?_,?_,?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : R < ‖z‖
    · exact (contDiffAt_const.sub b.contDiffAt).smul (hG z hz)
    · have hball : z ∈ ball (0 : ℂ) b.rIn := by
        change dist z 0 < R+1
        rw [dist_zero_right]
        linarith [le_of_not_gt hz]
      have he : F =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
        filter_upwards [b.eventuallyEq_one_of_mem_ball hball] with w hw
        change b w = (1 : ℝ) at hw
        change (1-b w) • G w = 0
        rw [hw,sub_self,zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  · intro z
    by_cases hz : R < ‖z‖
    · have h0 : 0 ≤ 1-b z := sub_nonneg.mpr b.le_one
      have h1 : 1-b z ≤ 1 := by linarith [b.nonneg (x := z)]
      change ‖(1-b z) • G z‖ ≤ L
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg h0]
      calc (1-b z)*‖G z‖ ≤ 1*L := by gcongr; exact hbound z hz
           _ = L := one_mul _
    · have hb : b z = 1 := b.one_of_mem_closedBall (by
        change dist z 0 ≤ R+1
        rw [dist_zero_right]
        linarith [le_of_not_gt hz])
      simpa only [F,hb,sub_self,zero_smul,norm_zero] using hL
  · intro z hz
    have hb : b z = 0 := b.zero_of_le_dist (by simpa only [dist_zero_right] using hz)
    simp only [F,hb,sub_zero,one_smul]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.bounded_smooth_exterior_extension
