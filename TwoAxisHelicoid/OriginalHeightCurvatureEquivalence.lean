import TwoAxisHelicoid.MinimalHelicoidHeightGraphUpgrade
import TwoAxisHelicoid.PositionalBoundedCurvatureGraph

namespace TwoAxisHelicoid
open Set Topology

/-- Height decay on a single normal graph gives a uniform upper bound
on the actual chart shape operator in the original signed-pitch frame. -/
theorem original_height_graph_physical_curvature (s : OriginalSmoothHelicoid)
    (graph : HasHelicoidHeightEnd (coordinateToTube ∘ centeredHelicoidNormalization s.axes.pitch_ne ∘ s.position)) :
    HasBoundedPhysicalEndCurvature s := by
  obtain ⟨closed,regular,minimal⟩ := physical_frame_regular_minimal s
  obtain ⟨K,compact,estimate⟩ := minimal_height_graph_end_shape_bound
    (centeredHelicoidNormalization s.axes.pitch_ne ∘ s.position) closed.isProperMap regular minimal graph
  exact ⟨K,12288,compact,by norm_num,estimate⟩

/-- For a properly embedded positional candidate the physical curvature
condition is equivalent to the existence of an exterior normal graph
with decaying height. Both quantities refer to the fixed asymptotic helicoid. -/
theorem positional_shape_iff_height_graph (s : OriginalPositionallyAsymptoticHelicoid) :
    HasBoundedPhysicalEndCurvature s.toOriginalSmoothHelicoid ↔
      HasHelicoidHeightEnd (coordinateToTube ∘ centeredHelicoidNormalization s.axes.pitch_ne ∘ s.position) := by
  refine ⟨?_,original_height_graph_physical_curvature s.toOriginalSmoothHelicoid⟩
  intro bounded
  have graph := (positional_c1_graph_of_bounded_shape s bounded).heightEnd
  have zero : (![0,0,0] : Fin 3 → ℝ)=0 := by ext i;fin_cases i <;> rfl
  rw [zero] at graph
  exact graph

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_height_graph_physical_curvature
#print axioms TwoAxisHelicoid.positional_shape_iff_height_graph
