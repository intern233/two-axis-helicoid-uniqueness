import TwoAxisHelicoid.BoundedPlaneFill

namespace TwoAxisHelicoid
open Set Metric Bornology Topology

theorem boundedPlaneFill_mono {U V : Set ℂ} (inc : U⊆V) : boundedPlaneFill U⊆boundedPlaneFill V :=
  fun x hx => (show IsBounded (connectedComponentIn Uᶜ x) from hx).subset
    (connectedComponentIn_mono x (compl_subset_compl.mpr inc))

/-- Filling a compact subset of a bounded domain keeps it compact and
inside the domain whenever the domain's complement is connected. -/
theorem boundedPlaneFill_compact_inside {K D : Set ℂ} (ck : IsCompact K) (inc : K⊆D)
    (bounded : IsBounded D) (outside : IsPreconnected Dᶜ) :
    IsCompact (boundedPlaneFill K) ∧ boundedPlaneFill K⊆D := by
  classical
  obtain ⟨B,bb⟩ := bounded.exists_norm_le
  let R := max B 0
  have rp : 0≤R := le_max_right _ _
  let p : ℂ := (R+1:ℝ)
  have far : R<‖p‖ := by dsimp only [p]; rw [Complex.norm_real,Real.norm_of_nonneg (by linarith)]; linarith
  have bound (z : ℂ) (hz : z∈D) : ‖z‖≤R := (bb _ hz).trans (le_max_left _ _)
  obtain ⟨eq,small⟩ := boundedPlaneFill_eq_exterior rp (fun z hz => bound z (inc hz)) far
  have closed : IsClosed (boundedPlaneFill K) := by
    rw [eq,fillAwayFrom]
    exact (ck.isClosed.isOpen_compl.connectedComponentIn).isClosed_compl
  have pc : p∈Dᶜ := fun hd => far.not_ge (bound p hd)
  have large : Dᶜ⊆connectedComponentIn Kᶜ p := outside.subset_connectedComponentIn pc (compl_subset_compl.mpr inc)
  refine ⟨(isCompact_closedBall (0:ℂ) R).of_isClosed_subset closed small,?_⟩
  rw [eq]
  intro z hz
  by_contra away
  exact hz (large away)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.boundedPlaneFill_compact_inside
