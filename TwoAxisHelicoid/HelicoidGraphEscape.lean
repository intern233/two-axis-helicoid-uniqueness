import TwoAxisHelicoid.HelicoidProjectionBound

namespace TwoAxisHelicoid
open Set Bornology

/-- The inverse of an actual bounded-height normal graph escapes every
compact subset of the parameter surface as its base coordinate escapes. -/
theorem helicoid_graph_inverse_avoids_compact {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (hX : Continuous X)
    {B : Set (ℝ × ℝ)} {Y : B → M} {u : B → ℝ}
    (hu : ∀ b, |u b| ≤ 1)
    (hgraph : ∀ b, X (Y b) = helicoidTubeMap ((u b,b.1.1),b.1.2))
    {K : Set M} (hK : IsCompact K) :
    ∃ T : ℝ, 0 < T ∧ ∀ b : B, T < ‖b.1‖ → Y b ∉ K := by
  obtain ⟨C,hC0,hC⟩ := (hK.image hX).isBounded.exists_pos_norm_le
  refine ⟨2*C+2,by positivity,?_⟩
  intro b hb hk
  have hc := hC (X (Y b)) ⟨Y b,hk,rfl⟩
  have hbound := helicoid_normal_parameters_norm_bound b.1.1 b.1.2 (u b) (hu b)
  rw [← hgraph b] at hbound
  change ‖b.1‖ ≤ 2*‖X (Y b)‖+1 at hbound
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoid_graph_inverse_avoids_compact
