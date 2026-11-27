import TwoAxisHelicoid.OriginalGraphExteriorNormalization
import TwoAxisHelicoid.HarmonicMarkedTorusCompleteness
import TwoAxisHelicoid.HarmonicImmersionReparametrization

namespace TwoAxisHelicoid
open Complex Set Topology Filter InnerProductSpace
open scoped Topology ContDiff Manifold

/-- The chartwise regular harmonic immersion on the given marked torus
pulls back regularly at every representative in the lattice complement. -/
theorem marked_punctured_atlas_pullback_regular (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (charts : ∀ e∈atlas ℂ (PuncturedPeriodTorus L), HarmonicImmersionChart X e) (z : ℂ) (hz : z∉L.lattice) :
    (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z ∧ Function.Injective (fderiv ℝ (puncturedTorusPullback L X) z) := by
  let P := puncturedTorusPullback L X
  let q := puncturedPlaneProjection L ⟨z,hz⟩
  let e := chartAt ℂ q
  let x := e q
  have atx : x∉L.lattice := puncturedPeriodTorus_chart_not_lattice L q
  have trans : x-z∈L.lattice := (periodTorusProjection_eq_iff L z x).mp (puncturedPeriodTorus_chart_representative L q).symm
  have ep := TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq (H := ℂ) (puncturedPeriodTorusOpen L) (x := q)
  have germ : X ∘ e.symm=ᶠ[𝓝 x] P := by
    filter_upwards [ep,L.isClosed_lattice.isOpen_compl.mem_nhds atx] with w hw off
    change w∉L.lattice at off
    have eq : (e.symm w).1=periodTorusProjection L w := by
      rw [← periodTorus_chart_symm_eq_projection L q.1]
      exact hw.symm
    exact (congrArg X (Subtype.ext eq : e.symm w=puncturedPlaneProjection L ⟨w,off⟩)).trans
      (by simp [P,puncturedTorusPullback,off])
  let u := fun w : ℂ => w+(x-z)
  have uz : u z=x := by dsimp [u]; abel
  have du : HasDerivAt u 1 z := (hasDerivAt_id z).add_const _
  have cu : Tendsto u (𝓝 z) (𝓝 x) := uz ▸ du.continuousAt
  have eq : (X ∘ e.symm) ∘ u=ᶠ[𝓝 z] P :=
    (germ.comp_tendsto cu).trans (.of_forall fun w => puncturedTorusPullback_periodic L X w (x-z) trans)
  obtain ⟨h,c,i⟩ := charts e (chart_mem_atlas ℂ q) x (e.map_source (mem_chart_source ℂ q))
  obtain ⟨hr,cr,ir⟩ := harmonic_immersion_reparametrization (u := u) (z := z)
    (uz.symm ▸ h) (uz.symm ▸ c) (uz.symm ▸ i) (analyticAt_id.add analyticAt_const) (du.deriv.trans_ne one_ne_zero)
  have d : DifferentiableAt ℝ ((X ∘ e.symm) ∘ u) z := (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hr j)).differentiableAt
  refine ⟨fun j => (harmonicAt_congr_nhds (eq.mono fun _ v => congrFun v j)).mp (hr j),?_,(eq.fderiv_eq (𝕜 := ℝ)) ▸ ir⟩
  apply (conformalCoordinateDerivatives_iff_dot (d.congr_of_eventuallyEq eq.symm)).mpr
  rw [← eq.fderiv_eq]
  exact (conformalCoordinateDerivatives_iff_dot d).mp cr

/-- In an already marked torus, a physical helicoid graph of arbitrary
signed pitch gives the exact normalized exterior in the original
spatial frame directly. -/
theorem fixed_marked_graph_has_normalized_exterior (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (cl : IsClosedEmbedding X) (charts : ∀ e∈atlas ℂ (PuncturedPeriodTorus L), HarmonicImmersionChart X e)
    {α : ℝ} (ha : α≠0) (graph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization ha ![0,0,0] ∘ X)) :
    ∃ A : GeometricExteriorCoordinate X, A.correction 0=0 := by
  let R := axisSpatialNormalization ha ![0,0,0]
  let Y := R ∘ X
  have regular : ∀ e∈atlas ℂ (PuncturedPeriodTorus L), HarmonicImmersionChart Y e :=
    fun e he z hz => reference_frame_harmonic_chart (charts e he z hz).1 (charts e he z hz).2.1 (charts e he z hz).2.2 ha
  obtain ⟨A⟩ := arbitrary_torus_physical_exterior L Y (R.isClosedEmbedding.comp cl).isProperMap graph
    (marked_punctured_atlas_pullback_regular L Y regular)
  exact physical_exterior_back_in_original_frame (Homeomorph.refl _) X cl charts ha A

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_punctured_atlas_pullback_regular
#print axioms TwoAxisHelicoid.fixed_marked_graph_has_normalized_exterior
