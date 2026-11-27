import TwoAxisHelicoid.GraphEndAtPhysicalPitch
import TwoAxisHelicoid.OneEndedHelicoidGraphProper
import TwoAxisHelicoid.ExteriorDifferentialOfMeasuredGauss
import TwoAxisHelicoid.ExteriorOnePointPoleModel
import TwoAxisHelicoid.PlacedHelicoidFrame
import TwoAxisHelicoid.PuncturedTorusRealOrientation
import TwoAxisHelicoid.PuncturedCurveNoncompact

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold
universe v

/-- An orientable topological reference supplies the sign of the normal
field on the real immersion. No differentiability of the reference
map, or compatibility of its charts with the immersion, is required. -/
theorem minimal_harmonic_atlas_of_topological_reference
    {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M]
    [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ,ℂ) ω N]
    {f : M → N} (localRef : IsLocalHomeomorph f)
    {X : M → Fin 3 → ℝ} (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (imm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x))
    (min : ∀ x, coordinateMeanCurvature (X ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)=0) :
    ∃ S : ChartedSpace ℂ M, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω M ∧ ∀ e∈atlas ℂ M, InducedIsothermalChart X e ∧ HarmonicImmersionChart X e := by
  obtain ⟨d,dom,positive⟩ : ∃ d : M → OpenPartialHomeomorph M ℂ, (∀ x, x∈(d x).source) ∧
      ∀ x y z, z∈(d x).source → z∈(d y).source → planeChartIndex (d x) (d y) z=1 := by
    let _ := holomorphicCoverAtlas localRef
    let _ := holomorphicCoverAtlas_isManifold localRef
    exact ⟨chartAt ℂ,mem_chart_source ℂ,fun x y _ hx hy => planeChartIndex_holomorphic
      (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ x))
      (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ y)) hx hy⟩
  have reg := smooth_surface_regular_manifold_chart sm imm
  obtain ⟨V,cv,trans⟩ := surface_transverse_field_of_topological_atlas (chartAt ℂ) d
    (mem_chart_source ℂ) dom reg positive
  have convertChart {e : OpenPartialHomeomorph M ℂ} (h : OrientedIsothermalChart X V e) :
      InducedIsothermalChart X e ∧ HarmonicImmersionChart X e := by
    have c := oriented_isothermal_chart_actual_harmonic reg min h
    exact ⟨⟨h.1,fun z hz => (c z hz).2.1⟩,c⟩
  obtain ⟨S,man,oriented⟩ := smooth_minimal_manifold_induced_complex_structure sm imm cv min trans
  let _ := S
  refine ⟨S,man,?_⟩
  intro e he
  exact convertChart (oriented e he)

/-- A one-ended physical C¹ graph realizes the finite-topology
publication's differential and two-pole conclusions in the specified
ambient frame. Properness is proved from the graph and the topology. -/
theorem harmonic_graph_in_frame_gives_finite_end {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [NoncompactSpace M]
    (tail : HasConnectedCompactTails M) (X : M → Fin 3 → ℝ) (emb : IsEmbedding X)
    (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (F : HelicoidSpatialFrame) {α : ℝ} (ha : α≠0)
    (graph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization ha ![0,0,0] ∘ F.homeo ∘ X)) :
    IsClosedEmbedding X ∧ Nonempty (PublishedConformalPoleModel X) ∧
    ∃ A : GeometricExteriorInSomeFrame X, A.frame=F.linear.toLinearEquiv ∧ A.offset=F.offset ∧
      A.pitch=α ∧ A.exterior.pitch=α ∧ A.exterior.correction 0=0 ∧
      Nonempty (FiniteTopologyExteriorDifferential (F.homeo ∘ X)) := by
  let Y := F.homeo ∘ X
  let T := (axisSpatialNormalization ha ![0,0,0]).trans coordinateTubeHomeomorph
  have cy : Continuous Y := F.homeo.continuous.comp emb.continuous
  have cY : ∀ e∈atlas ℂ M, HarmonicImmersionChart Y e :=
    orthogonal_affine_harmonic_charts X charts F.linear.toLinearEquiv F.orthogonal F.offset
  have proper : IsProperMap (T ∘ Y) := graph.heightEnd.proper_of_one_end (T.continuous.comp cy) tail
  have properY : IsProperMap Y := by
    have eq : T.symm ∘ (T ∘ Y)=Y := funext fun x => T.symm_apply_apply _
    exact eq ▸ (T.symm.isClosedEmbedding.isProperMap.comp proper)
  have closedY := IsClosedEmbedding.of_continuous_injective_isClosedMap cy (F.homeo.injective.comp emb.injective) properY.isClosedMap
  have closed : IsClosedEmbedding X := by
    have eq : F.homeo.symm ∘ Y=X := funext fun x => F.homeo.symm_apply_apply _
    exact eq ▸ F.homeo.symm.isClosedEmbedding.comp closedY
  obtain ⟨D,dp,zero,_⟩ := graph_end_at_physical_pitch Y closedY cY ha graph
  let A : GeometricExteriorInSomeFrame X := ⟨F.linear.toLinearEquiv,F.orthogonal,F.offset,D,α,ha,
    (reference_graph_positional_asymptote Y cy ha graph).2⟩
  exact ⟨closed,exterior_frame_constructs_compact_pole_model emb.continuous charts tail A,
    A,rfl,rfl,rfl,dp,zero,⟨D.toFiniteTopologyDifferential⟩⟩

/-- Proposition 2.1 for any orientable finite genus with a given graph
asymptote, in arbitrary Euclidean placement. The marking by a punctured
compact reference surface here is only a homeomorphism. Smoothness,
minimality and the Weierstrass differentials refer to the physical map. -/
theorem unmarked_graph_gives_finite_end_differential {M : Type} {N : Type v}
    [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M]
    [TopologicalSpace N] [T2Space N] [CompactSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ,ℂ) ω N]
    (p : N) (top : M ≃ₜ {q : N // q≠p}) (X : M → Fin 3 → ℝ) (emb : IsEmbedding X)
    (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (imm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x))
    (min : ∀ x, coordinateMeanCurvature (X ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)=0)
    (F : HelicoidSpatialFrame) {α : ℝ} (ha : α≠0)
    (graph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization ha ![0,0,0] ∘ F.homeo ∘ X)) :
    IsClosedEmbedding X ∧ Nonempty (PublishedConformalPoleModel X) ∧
      ∃ S : ChartedSpace ℂ M, let _ := S
        IsManifold 𝓘(ℂ,ℂ) ω M ∧ (∀ e∈atlas ℂ M, InducedIsothermalChart X e ∧ HarmonicImmersionChart X e) ∧
        ∃ A : GeometricExteriorInSomeFrame X, A.frame=F.linear.toLinearEquiv ∧ A.offset=F.offset ∧
          A.pitch=α ∧ A.exterior.pitch=α ∧ A.exterior.correction 0=0 ∧ Nonempty (FiniteTopologyExteriorDifferential (F.homeo ∘ X)) := by
  let _ := punctured_complex_curve_noncompact p
  let _ : NoncompactSpace M := ⟨fun h => noncompact_univ {q : N // q≠p} (by
    simpa only [image_univ,top.surjective.range_eq] using h.image top.continuous)⟩
  have op : IsOpen {q : N | q≠p} := isOpen_compl_singleton
  have localRef : IsLocalHomeomorph (fun x => (top x).1) :=
    (op.isOpenEmbedding_subtypeVal.comp top.isOpenEmbedding).isLocalHomeomorph
  obtain ⟨S,man,charts⟩ := minimal_harmonic_atlas_of_topological_reference localRef sm imm min
  let _ := S
  let _ := man
  obtain ⟨closed,model,data⟩ := harmonic_graph_in_frame_gives_finite_end
    (homeomorphic_punctured_surface_connected_tails p top) X emb (fun e he => (charts e he).2) F ha graph
  exact ⟨closed,model,S,man,charts,data⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.minimal_harmonic_atlas_of_topological_reference
#print axioms TwoAxisHelicoid.harmonic_graph_in_frame_gives_finite_end
#print axioms TwoAxisHelicoid.unmarked_graph_gives_finite_end_differential
