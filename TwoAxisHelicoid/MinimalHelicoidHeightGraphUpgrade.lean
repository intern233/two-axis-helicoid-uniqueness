import TwoAxisHelicoid.HeightGraphEndCurvature
import TwoAxisHelicoid.HeightEndThinTubes
import TwoAxisHelicoid.GeneralThinTubeLemma
import TwoAxisHelicoid.PhysicalMinimalSimilarity
import TwoAxisHelicoid.UnmarkedPositionalGraph

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold

/-- A properly embedded one-ended smooth minimal surface which is a
single helicoidal normal graph with height tending to zero is a C¹ end
in the very same physical coordinates and over the same helicoid. -/
theorem minimal_helicoid_height_graph_is_C1 {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    (X : M → Fin 3 → ℝ) (embedded : IsClosedEmbedding X) (regular : ∀ q, RegularImmersionChart X (chartAt ℂ q))
    (minimal : ∀ q, coordinateMeanCurvature (X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q)=0)
    (tail : ∀ K : Set M, IsCompact K → ∃ U : Set M, IsConnected U ∧ IsCompact Uᶜ ∧ Disjoint U K)
    (height : HasHelicoidHeightEnd (coordinateToTube ∘ X)) : HasHelicoidC1End (coordinateToTube ∘ X) := by
  obtain ⟨K,kc,bound⟩ := minimal_height_graph_end_shape_bound X embedded.isProperMap regular minimal height
  have thin := height.arbitrarily_thin (coordinateToTube_isProperMap embedded.isProperMap)
  apply general_one_end_thin_C1_graph_of_bounded_weingarten X embedded tail (chartAt ℂ)
    (mem_chart_source ℂ) regular kc (by norm_num : (0:ℝ)≤12288)
    (bounded_surface_weingarten_of_cross (mem_chart_source ℂ) regular bound)
  intro ε ep
  obtain ⟨U,compact,onTube⟩ := thin (min ε 1) (lt_min ep zero_lt_one)
  refine ⟨Uᶜ,compact,?_⟩
  intro q out
  obtain ⟨s,r,θ,sm,eq⟩ := onTube q (not_not.mp out)
  have inStrip : ((s,r),θ)∈helicoidTubeStrip := sm.trans_le (min_le_right _ _)
  change coordinateToTube (X q)=_ at eq
  rw [eq,helicoidSignedDistance_on_normal inStrip]
  exact ⟨helicoidTubeEquiv.map_source inStrip,sm.le.trans (min_le_left _ _)⟩

/-- For a smooth original double-axis handle, height decay suffices to
verify the end condition used by the independent pointed classification. -/
theorem original_helicoid_graph_height_iff_C1 (s : OriginalSmoothHelicoid) :
    HasHelicoidHeightEnd (coordinateToTube ∘ axisSpatialNormalization s.axes.pitch_ne ![0,0,0] ∘ s.position) ↔
    HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization s.axes.pitch_ne ![0,0,0] ∘ s.position) := by
  refine ⟨?_,HasHelicoidC1End.heightEnd⟩
  intro height
  have zero : (![0,0,0] : Fin 3 → ℝ)=0 := by ext i; fin_cases i <;> rfl
  rw [zero] at height ⊢
  obtain ⟨emb,reg,min⟩ := physical_frame_regular_minimal s
  exact minimal_helicoid_height_graph_is_C1 (centeredHelicoidNormalization s.axes.pitch_ne ∘ s.position) emb reg min
    (punctured_handle_connected_tails s.topologicalType) height

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.minimal_helicoid_height_graph_is_C1
#print axioms TwoAxisHelicoid.original_helicoid_graph_height_iff_C1
