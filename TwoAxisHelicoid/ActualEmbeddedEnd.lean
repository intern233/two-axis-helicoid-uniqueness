import TwoAxisHelicoid.ActualHeightEndCoordinate
import TwoAxisHelicoid.HeightEndEmbedding
import TwoAxisHelicoid.VerticalQuarterTurnHomeomorph

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology

/-- A genuine embedded end of the explicit spatial primitive, with a
height-coordinate inverse covering a punctured neighborhood of zero. -/
theorem actual_primitive_has_embedded_height_end {X : ℂ → Fin 3 → ℝ} {t a c : ℝ}
    (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht) :
    ∃ (K : ℂ → ℂ) (R : ℝ),
      Tendsto K (cobounded ℂ) (𝓝[≠] 0) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), K (actualComplexHeight t a c ht z) = z) ∧
      (∀ ξ : ℂ, R ≤ ‖ξ‖ → actualComplexHeight t a c ht (K ξ) = ξ) ∧
      IsClosedEmbedding (fun ξ : {ξ : ℂ // R ≤ ‖ξ‖} => X (K ξ.1)) := by
  obtain ⟨K,F,b,R₀,hK,hF,hKL,hcoord⟩ := actual_primitive_height_end_coordinate ht ha hc hX
  obtain ⟨R,hR,hEmb⟩ := height_normalized_helicoidal_end_eventually_embedded
    (2*(a-1)/c) b R₀ (fun z hz => (hcoord z hz).2.1) (fun z hz => (hcoord z hz).2.2) hF
  exact ⟨K,R,hK,hKL,(fun ξ hξ => (hcoord ξ (hR.trans_le hξ)).1),
    (vertical_quarter_turn_embedding_iff _).mp hEmb⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_primitive_has_embedded_height_end
