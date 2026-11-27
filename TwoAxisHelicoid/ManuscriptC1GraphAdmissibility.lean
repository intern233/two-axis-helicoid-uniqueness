import TwoAxisHelicoid.ManuscriptCompactGraphRestriction
import TwoAxisHelicoid.DifferentiableHelicoidGraphSmooth
import TwoAxisHelicoid.HelicoidHeightDecayStraightening
import TwoAxisHelicoid.PhysicalMinimalSimilarity

namespace TwoAxisHelicoid
open Set Filter Bornology Topology
open scoped Topology ContDiff Manifold

theorem HasHelicoidC1End.manuscript_graph {M : Type*} [TopologicalSpace M] {Y : M → HelicoidTubeCoordinates}
    (h : HasHelicoidC1End Y) : HasManuscriptC1HelicoidGraph Y := by
  obtain ⟨C,_,R,pos,core,E,_,u,sm,graph,decay⟩ := h
  exact ⟨_,core,R,pos,E,u,sm.of_le (by simp),graph,decay⟩

/-- For a smooth regular spatial immersion the parametrization of the C¹ graph
is its actual helicoid normal projection. Its original derivative decay is
retained on exactly the given compact complement. -/
theorem HasManuscriptC1HelicoidGraph.regular_end {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {Y : M → HelicoidTubeCoordinates}
    (regular : ∀ x : M, let e := chartAt ℂ x
      ContDiffAt ℝ ∞ (Y ∘ e.symm) (e x) ∧ Function.Injective (fderiv ℝ (Y ∘ e.symm) (e x)))
    (h : HasManuscriptC1HelicoidGraph Y) : HasHelicoidC1End Y := by
  obtain ⟨S,compact,R,pos,E,u,one,graph,decay⟩ := h
  have sm := differentiable_helicoid_normal_graph_is_smooth Y regular (exteriorPlaneBase_isOpen R)
    E u (one.differentiableOn (by decide)) (fun b => (graph b).1.trans_lt (by norm_num)) (fun b => (graph b).2)
  have projection (q : S) : helicoidBaseCoordinates (Y q.1) = (E q).1 := by
    have shape : Y q.1 = helicoidTubeMap ((u (E q),(E q).1.1),(E q).1.2) := by
      simpa only [Homeomorph.symm_apply_apply] using (graph (E q)).2
    rw [shape]
    exact normal_graph_coordinates_exact ((graph (E q)).1.trans_lt (by norm_num)) _
  let D := helicoidProjectedEnd Y Sᶜ (exteriorPlaneBase R)
  have equal : D = S := by
    ext x
    change (x ∉ Sᶜ ∧ helicoidBaseCoordinates (Y x) ∈ exteriorPlaneBase R) ↔ x ∈ S
    simp only [notMem_compl_iff]
    refine ⟨And.left,fun hx => ⟨hx,?_⟩⟩
    rw [projection ⟨x,hx⟩]
    exact (E ⟨x,hx⟩).2
  let changeSet : D ≃ₜ S := Homeomorph.setCongr equal
  let F := changeSet.trans E
  refine ⟨Sᶜ,compact,R,pos,?_,F,?_,u,sm,?_,decay⟩
  · change IsCompact Dᶜ
    simpa only [equal] using compact
  · exact funext fun x => Subtype.ext (projection (changeSet x)).symm
  · exact fun b => ⟨(graph b).1,(graph b).2⟩

theorem HasManuscriptC1HelicoidGraph.height_end {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {Y : M → HelicoidTubeCoordinates}
    (regular : ∀ x : M, let e := chartAt ℂ x
      ContDiffAt ℝ ∞ (Y ∘ e.symm) (e x) ∧ Function.Injective (fderiv ℝ (Y ∘ e.symm) (e x)))
    (h : HasManuscriptC1HelicoidGraph Y) : HasHelicoidHeightEnd Y :=
  (h.regular_end regular).heightEnd

/-- For the unparametrized minimal surface hypotheses of Theorem 1.1 the
printed regularity and the formal classification end condition are equivalent. -/
theorem original_manuscript_C1_graph_iff (s : OriginalSmoothHelicoid) :
    let Y := coordinateToTube ∘ axisSpatialNormalization s.axes.pitch_ne ![0,0,0] ∘ s.position
    HasManuscriptC1HelicoidGraph Y ↔ HasHelicoidC1End Y := by
  intro Y
  refine ⟨?_,HasHelicoidC1End.manuscript_graph⟩
  intro graph
  apply HasManuscriptC1HelicoidGraph.regular_end (Y:=Y) _ graph
  have zero : (![0,0,0] : Fin 3 → ℝ)=0 := by ext i; fin_cases i <;> rfl
  have framed := (physical_frame_regular_minimal s).2.1
  have coordsInj : Function.Injective coordinateToTube := fun a b eq => by
    simpa only [tubeCartesian_coordinateToTube] using congrArg tubeCartesian eq
  intro x
  let e := chartAt ℂ x
  change ContDiffAt ℝ ∞ (Y ∘ e.symm) (e x) ∧ Function.Injective (fderiv ℝ (Y ∘ e.symm) (e x))
  let Z := centeredHelicoidNormalization s.axes.pitch_ne ∘ s.position ∘ e.symm
  obtain ⟨sm,inject⟩ := framed x (e x) (e.map_source (mem_chart_source ℂ x))
  have formula : Y ∘ e.symm=coordinateToTube ∘ Z := by
    dsimp only [Y,Z]
    rw [zero]; rfl
  change ContDiffAt ℝ ∞ Z (e x) at sm
  change Function.Injective (fderiv ℝ Z (e x)) at inject
  rw [formula]
  refine ⟨coordinateToTube.contDiff.contDiffAt.comp _ sm,?_⟩
  have d := coordinateToTube.hasFDerivAt.comp (e x) (sm.differentiableAt (by simp)).hasFDerivAt
  rw [d.fderiv]
  exact coordsInj.comp inject

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasHelicoidC1End.manuscript_graph
#print axioms TwoAxisHelicoid.HasManuscriptC1HelicoidGraph.regular_end
#print axioms TwoAxisHelicoid.HasManuscriptC1HelicoidGraph.height_end
#print axioms TwoAxisHelicoid.original_manuscript_C1_graph_iff
