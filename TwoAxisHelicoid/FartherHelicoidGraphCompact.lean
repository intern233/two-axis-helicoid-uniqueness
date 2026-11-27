import TwoAxisHelicoid.ExteriorGraphRestriction
import TwoAxisHelicoid.HelicoidEndDomain
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

namespace TwoAxisHelicoid
open Set Metric

/-- Passing to a farther part of a bounded-height normal graph still
leaves a genuinely compact parameter complement. This uses the actual
proper spatial map and the compact normal block above a bounded base. -/
theorem farther_helicoid_graph_compact_complement {M : Type*} [TopologicalSpace M] [T2Space M]
    {X : M → HelicoidTubeCoordinates} (hX : IsProperMap X) {S : Set M} (hS : IsCompact Sᶜ)
    {R B : ℝ} (E : S ≃ₜ exteriorPlaneBase R)
    (hE : ∀ q : S, (E q).1 = helicoidBaseCoordinates (X q.1))
    {u : exteriorPlaneBase R → ℝ} (hu : ∀ p, |u p| ≤ 1/2)
    (hgraph : ∀ q : S, X q.1 = helicoidTubeMap ((u (E q),(E q).1.1),(E q).1.2)) :
    IsCompact (fartherExteriorSet (helicoidBaseCoordinates ∘ X) S B)ᶜ := by
  have hSopen : IsOpen S := by simpa only [compl_compl] using hS.isClosed.isOpen_compl
  have hclosed : IsClosed (fartherExteriorSet (helicoidBaseCoordinates ∘ X) S B)ᶜ :=
    (fartherExteriorSet_isOpen hSopen E hE).isClosed_compl
  have hblock : IsCompact (helicoidHeightBlock (1/2) (closedBall (0 : ℝ × ℝ) B)) :=
    helicoidHeightBlock_isCompact _ (isCompact_closedBall _ _)
  apply (hS.union (hX.isCompact_preimage hblock)).of_isClosed_subset hclosed
  intro q hq
  by_cases hqS : q ∈ S
  · right
    have hbound : ‖helicoidBaseCoordinates (X q)‖ ≤ B :=
      le_of_not_gt (fun h => hq ⟨hqS,h⟩)
    change X q ∈ helicoidHeightBlock (1/2) (closedBall (0 : ℝ × ℝ) B)
    rw [hgraph ⟨q,hqS⟩]
    refine ⟨(u (E ⟨q,hqS⟩),(E ⟨q,hqS⟩).1),⟨abs_le.mp (hu _),?_⟩,rfl⟩
    rw [mem_closedBall,dist_zero_right,hE]
    exact hbound
  · exact Or.inl hqS

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.farther_helicoid_graph_compact_complement
