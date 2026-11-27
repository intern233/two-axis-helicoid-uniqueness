import TwoAxisHelicoid.ExteriorHeightEscape
import TwoAxisHelicoid.ManuscriptC1GraphAdmissibility

namespace TwoAxisHelicoid
open Set Filter Bornology Topology
open scoped Topology ContDiff

/-- On every smooth physical candidate, the manuscript's C¹ graph on
complements of arbitrary compact sets gives the classified end condition. -/
theorem original_compact_complement_C1_graph_iff (s : OriginalSmoothHelicoid) :
    let Y := coordinateToTube ∘ axisSpatialNormalization s.axes.pitch_ne ![0,0,0] ∘ s.position
    HasCompactComplementC1Graph Y ↔ HasHelicoidC1End Y := by
  intro Y
  refine ⟨fun h => (original_manuscript_C1_graph_iff s).mp (h.round_exterior ?_ ?_),
    fun h => h.manuscript_graph.off_compact⟩
  · have zero : (![0,0,0] : Fin 3 → ℝ) = 0 := by ext i; fin_cases i <;> rfl
    dsimp only [Y]
    rw [zero]
    exact coordinateToTube.continuous.comp (physical_frame_regular_minimal s).1.continuous
  · exact homeomorphic_punctured_surface_connected_tails (0 : PeriodTorus s.modelTorus) s.topologicalType

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.original_compact_complement_C1_graph_iff
