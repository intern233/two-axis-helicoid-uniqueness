import TwoAxisHelicoid.AffineEndComplexPotentials
import TwoAxisHelicoid.PhysicalGraphPuncturePoleOrders
import TwoAxisHelicoid.OriginalGraphPoleModel
import TwoAxisHelicoid.ExteriorOnePointPoleModel
import TwoAxisHelicoid.NormalizedGeometricExteriorCoordinate

namespace TwoAxisHelicoid
open Complex Set Filter Metric Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- For arbitrary genus, a physical C¹ helicoidal end with two straight axes and
a single conformal puncture forces both exact pole orders in
the original frame. The horizontal line can be at any height and
direction. The actual signs of the spatial normalization are retained. -/
theorem physical_two_axis_graph_orders_in_given_puncture {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [PreconnectedSpace M] {X : M → Fin 3 → ℝ}
    (emb : IsClosedEmbedding X) (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d)
    (axes : OriginalHelicoidAxes (range X))
    (graph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization axes.pitch_ne ![0,0,0] ∘ X))
    (E : PuncturedComplexEnd M) (hol : E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) :
    let Y := X ∘ E.coord.symm
    (MeromorphicAt (fun z => immersionComplexCoefficient Y z 2) 0 ∧ meromorphicOrderAt (fun z => immersionComplexCoefficient Y z 2) 0=(-2:ℤ)) ∧
      MeromorphicAt (immersionGaussLogDerivative Y) 0 ∧ meromorphicOrderAt (immersionGaussLogDerivative Y) 0=(-2:ℤ) := by
  intro Y
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℂ M
  let _ : NoncompactSpace M := noncompactSpace_of_neBot E.from_zero.neBot
  let L := centeredHelicoidNormalization axes.pitch_ne
  let R := axisSpatialNormalization axes.pitch_ne ![0,0,0]
  have zero : (![0,0,0] : Fin 3 → ℝ)=0 := by ext i; fin_cases i <;> rfl
  have ident : (fun z => L (Y z)+(0:Fin 3 → ℝ))=R ∘ Y := by
    funext z
    simp only [add_zero,Function.comp_apply,R,zero]
    rfl
  have asy := (reference_graph_positional_asymptote X emb.continuous axes.pitch_ne graph).1
  have pot := original_placed_axes_have_end_potentials emb charts axes asy E hol
  have all : HasEndCartesianPotentials (R ∘ Y) := ident ▸ pot.affine L.toLinearEquiv.toLinearMap 0
  have target : E.coord.target∈𝓝[≠] (0:ℂ) := by
    rw [E.target_eq]
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) E.radius_pos)) self_mem_nhdsWithin
  have chart := harmonic_immersion_chart_maximal charts hol
  have regular : ∀ᶠ z in 𝓝[≠] (0:ℂ), (∀ j, HarmonicAt (fun w => Y w j) z) ∧
      ConformalCoordinateDerivatives Y z ∧ Function.Injective (fderiv ℝ Y z) :=
    Filter.mem_of_superset target (fun z hz => chart z hz)
  obtain ⟨⟨_,h⟩,_,g⟩ := physical_graph_puncture_double_poles (R ∘ X) (R.isProperMap.comp emb.isProperMap) graph E
    (regular.mono (fun z q => reference_frame_harmonic_chart q.1 q.2.1 q.2.2 axes.pitch_ne)) all
  have diff : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ Y z :=
    regular.mono (fun z q => (analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (q.1 j))).differentiableAt)
  have ord := reference_frame_end_orders axes.pitch_ne diff
  have height := ord.1.symm.trans h
  have gauss := ord.2.symm.trans g
  exact ⟨⟨meromorphicAt_of_meromorphicOrderAt_ne_zero (height.trans_ne (by norm_num)),height⟩,
    meromorphicAt_of_meromorphicOrderAt_ne_zero (gauss.trans_ne (by norm_num)),gauss⟩

/-- For an actual original C¹ handle, compactification of the physical
end by a single conformal point suffices to construct the genuine
normalized exterior. The compact handle need not be uniformized. -/
theorem original_C1_exterior_from_conformal_puncture {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [PreconnectedSpace M] {X : M → Fin 3 → ℝ}
    (emb : IsClosedEmbedding X) (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d)
    (axes : OriginalHelicoidAxes (range X))
    (graph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization axes.pitch_ne ![0,0,0] ∘ X))
    (E : PuncturedComplexEnd M) (hol : E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) :
    ∃ G : GeometricExteriorCoordinate X, G.correction 0=0 := by
  obtain ⟨⟨h,ho⟩,g,go⟩ := physical_two_axis_graph_orders_in_given_puncture emb charts axes graph E hol
  let D : GeometricDoublePoleEnd X := ⟨E,hol,h,ho,g,go⟩
  have asy := (reference_graph_positional_asymptote X emb.continuous axes.pitch_ne graph).1
  obtain ⟨B⟩ := original_positional_poles_give_exterior emb charts axes asy D
  obtain ⟨G,_,norm⟩ := B.normalized emb.continuous E.connected_tails
  exact ⟨G,norm⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_two_axis_graph_orders_in_given_puncture
#print axioms TwoAxisHelicoid.original_C1_exterior_from_conformal_puncture
