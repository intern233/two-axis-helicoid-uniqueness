import TwoAxisHelicoid.ClosedArcOnRealManifold
import TwoAxisHelicoid.NonseparatingPoint
import TwoAxisHelicoid.JordanPatchDisk

namespace TwoAxisHelicoid
open Set Function Topology TopologicalSpace Metric

/-- Every compact connected Hausdorff manifold locally modelled on the
open real line is a circle. Delete a nonseparating point, join its two
local sides in the punctured manifold, and use one-dimensional invariance
of domain to show that the resulting simple loop fills the manifold. -/
theorem compact_connected_real_manifold_is_circle {M : Type*} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [ChartedSpace ℝ M] :
    Nonempty (M ≃ₜ sphere (0:ℂ) 1) := by
  classical
  let p := Classical.arbitrary M
  obtain ⟨a,ea,ap⟩ := open_line_at_point p
  have ap' : a 1≠p := fun eq => one_ne_zero (ea.injective (eq.trans ap.symm))
  let _ : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℝ _
  obtain ⟨x,_,conn⟩ := exists_nonseparating_point p (a 1) ap'
  obtain ⟨j,ej,jx⟩ := open_line_at_point x
  let U : Opens M := ⟨{x}ᶜ,isOpen_ne⟩
  let _ : ConnectedSpace U := isConnected_iff_connectedSpace.mp conn
  let v : U := ⟨j (-1),fun h => (by norm_num : (-1:ℝ)≠0) (ej.injective (h.trans jx.symm))⟩
  let w : U := ⟨j 1,fun h => (one_ne_zero : (1:ℝ)≠0) (ej.injective (h.trans jx.symm))⟩
  rcases real_manifold_simple_arc_joined v w with h|⟨δ,di⟩
  · exact ((by norm_num : (-1:ℝ)≠1) (ej.injective (congrArg Subtype.val h))).elim
  · let γ := δ.map continuous_subtype_val
    have avoid : j 0∉range γ := by
      rintro ⟨t,h⟩
      exact (δ t).2 (h.trans jx)
    exact simple_closed_loop_from_bypass j ej γ (Subtype.val_injective.comp di) avoid

theorem compact_real_curve_classification : CompactRealCurveClassification :=
  fun _ _ _ _ _ _ => compact_connected_real_manifold_is_circle

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_connected_real_manifold_is_circle
#print axioms TwoAxisHelicoid.compact_real_curve_classification
