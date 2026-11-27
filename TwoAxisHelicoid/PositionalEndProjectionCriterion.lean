import TwoAxisHelicoid.TransverseProjectionHeightEnd
import TwoAxisHelicoid.PhysicalMinimalSimilarity
import TwoAxisHelicoid.UnmarkedPositionalGraph

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold

/-- For each original positional candidate, a single exterior graph
of decaying height is equivalent to nonsingularity of its nearest-base
projection outside a compact set. The right hand side is evaluated in
the original surface charts after the signed-pitch normalization. -/
theorem original_positional_height_iff_noncritical (s : OriginalPositionallyAsymptoticHelicoid) :
    let X := coordinateToTube ∘ centeredHelicoidNormalization s.axes.pitch_ne ∘ s.position
    HasHelicoidHeightEnd X ↔ NoncriticalHelicoidEndProjection X := by
  let Y := centeredHelicoidNormalization s.axes.pitch_ne ∘ s.position
  let Z := coordinateToTube ∘ Y
  change HasHelicoidHeightEnd Z ↔ NoncriticalHelicoidEndProjection Z
  obtain ⟨cl,regular,_⟩ := physical_frame_regular_minimal s.toOriginalSmoothHelicoid
  have reg (q : s.carrier) := regular q _ ((chartAt ℂ q).map_source (mem_chart_source ℂ q))
  have sm (q : s.carrier) : ContDiffAt ℝ ∞ (Z ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q) :=
    coordinateToTube.contDiff.contDiffAt.comp _ (reg q).1
  constructor
  · intro graph
    apply graph.noncritical_projection
    intro q
    refine ⟨(sm q).differentiableAt (by simp),?_⟩
    have eqn := (coordinateToTube.hasFDerivAt.comp ((chartAt ℂ q) q)
      ((reg q).1.differentiableAt (by simp)).hasFDerivAt).fderiv
    change Function.Injective (fderiv ℝ (coordinateToTube ∘ (Y ∘ (chartAt ℂ q).symm)) ((chartAt ℂ q) q))
    rw [eqn]
    exact coordinateToTube_injective.comp (reg q).2
  · intro h
    apply height_graph_from_noncritical_projection (coordinateToTube_isProperMap cl.isProperMap)
      (coordinateToTube_injective.comp cl.injective) (punctured_handle_connected_tails s.topologicalType) sm _ h
    intro ε ep
    obtain ⟨U,k,inTube⟩ := positional_standard_end_actual_tubes cl.isProperMap
      (reference_frame_positional_standard _ s.axes.pitch_ne s.approaches) (min ε 1) (lt_min ep zero_lt_one)
    refine ⟨Uᶜ,k,?_⟩
    intro q hq
    obtain ⟨v,r,θ,small,eq⟩ := inTube q (not_not.mp hq)
    have strip : ((v,r),θ)∈helicoidTubeStrip := small.trans_le (min_le_right _ _)
    change Z q∈helicoidTubeEquiv.target ∧ |helicoidSignedDistance (Z q)|≤ε
    change Z q=helicoidTubeMap ((v,r),θ) at eq
    rw [eq,helicoidSignedDistance_on_normal strip]
    exact ⟨helicoidTubeEquiv.map_source strip,small.le.trans (min_le_left _ _)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_positional_height_iff_noncritical
