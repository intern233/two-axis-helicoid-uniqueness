import TwoAxisHelicoid.PublishedMarkedEmbeddedExample
import TwoAxisHelicoid.MarkedGraphPhysicalPoles

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology

/-- An injectivity proof for the certified primitive supplies the full
marked existence input, including both intrinsic orders in the same
physical frame. -/
theorem marked_embedded_example_of_certified_injective
    (hi : Function.Injective certifiedTorusImmersion) : PublishedMarkedEmbeddedHelicoidExample := by
  let p := certifiedClosedParameters
  have hc : (1:ℝ)≠0 := one_ne_zero
  let X := fun q : PeriodTorus certifiedPeriodPair =>
    actualTorusImmersion p.height_pos p.abscissa_mem hc p.vertical_closed p.horizontal_closed q -
      actualGlobalImmersion p.t p.a 1 p.height_pos 1
  let Xp := fun q : PuncturedPeriodTorus certifiedPeriodPair => X q.1
  let H := certified_converse_immersion
  have cl : IsClosedEmbedding Xp := by
    apply IsClosedEmbedding.of_continuous_injective_isClosedMap H.proper.continuous _ H.proper.isClosedMap
    intro x y h
    apply hi
    apply congrArg coordinateToEuclidean
    have eq := congrArg (fun v : Fin 3 → ℝ => v+actualGlobalImmersion p.t p.a 1 p.height_pos 1) h
    simpa only [centeredActualTorusImmersion,p,sub_add_cancel] using eq
  have reg (z : ℂ) (hz : z∉certifiedPeriodPair.lattice) :
      (∀ j, HarmonicAt (fun w => X (periodTorusProjection certifiedPeriodPair w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection certifiedPeriodPair) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection certifiedPeriodPair) z) := by
    let P := centeredActualPrimitive p.t p.a 1 p.height_pos
    change (∀ j, HarmonicAt (fun w => P w j) z) ∧ ConformalCoordinateDerivatives P z ∧ Function.Injective (fderiv ℝ P z)
    have hh : HarmonicAt P z := ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem hc
      p.vertical_closed p.horizontal_closed).2.2.1 z hz).sub (harmonicAt_const _)
    have d : HasFDerivAt P (nullRealDerivative (coordinateData p.t p.a 1 p.height_pos z)) z :=
      centeredActualPrimitive_hasFDerivAt p.height_pos p.abscissa_mem hc p.vertical_closed p.horizontal_closed hz
    have n : ComplexNull (coordinateData p.t p.a 1 p.height_pos z) := coordinateData_null p.height_pos p.abscissa_mem hz
    have ne := coordinateData_ne_zero p.height_pos p.abscissa_mem hc hz
    refine ⟨fun j => hh.comp_CLM (ContinuousLinearMap.proj j),?_,d.fderiv.symm ▸ nullRealDerivative_injective n ne⟩
    have hj (j : Fin 3) : fderiv ℝ (fun w => P w j) z =
        (ContinuousLinearMap.proj j).comp (nullRealDerivative (coordinateData p.t p.a 1 p.height_pos z)) :=
      ((ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z d).fderiv
    obtain ⟨_,h₁,h₂,h₃⟩ := nullRealDerivative_conformal n ne
    unfold ConformalCoordinateDerivatives
    simp only [hj,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
    exact ⟨h₁.trans h₂.symm,h₃⟩
  let α := 2*(p.a-1)/1
  have hα : α≠0 := certified_normalization_scale_ne_zero
  have hx (r : ℝ) : r • (![1,0,0] : Fin 3 → ℝ) = ![r,0,0] := by
    ext j
    fin_cases j <;> simp
  let axes : OriginalHelicoidAxes (range Xp) := {
    horizontalDirection := 1, unit := norm_one, horizontalPoint := 0
    horizontal := fun r => by
      change (0 : Fin 3 → ℝ) + r • ![1,0,0] ∈ range Xp
      rw [zero_add,hx]
      exact H.horizontal_axis r
    vertical := H.vertical_axis, pitch := α, pitch_ne := hα }
  have hzero : (![0,0,0] : Fin 3 → ℝ) = 0 := by ext j; fin_cases j <;> rfl
  have normalize : axisSpatialNormalization hα ![0,0,0] ∘ Xp = certifiedNormalizedTorusImmersion := by
    funext q
    rw [Function.comp_apply,certifiedNormalizedTorusImmersion_eq_fixed_similarity hα q,hzero]
    simp only [axisSpatialNormalization_apply,map_zero,sub_zero,Xp,X,map_sub]
    rfl
  have graph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization hα ![0,0,0] ∘ Xp) := by
    rw [normalize]
    exact certifiedTorusImmersion_C1_helicoid_end
  obtain ⟨height,gauss⟩ := marked_graph_physical_poles certifiedPeriodPair X cl axes reg graph
  exact ⟨certifiedPeriodPair,X,cl,H.horizontal_axis,H.vertical_axis,reg,height,gauss⟩

/-- The only unresolved datum in marked embedded existence is an actual
double-point exclusion on a single compact subset of the certified torus. -/
theorem marked_example_iff_certified_core_injective :
    ∃ K : Set (PuncturedPeriodTorus certifiedPeriodPair), IsCompact K ∧
      immersionDoublePoints certifiedTorusImmersion ⊆ K ×ˢ K ∧
      (PublishedMarkedEmbeddedHelicoidExample ↔ InjOn certifiedTorusImmersion K) := by
  obtain ⟨_,K,k,d,check⟩ := certified_compact_embedding_criterion
  exact ⟨K,k,d,⟨fun h => check.mp (certified_embedding_of_published_marked_example h),
    fun h => marked_embedded_example_of_certified_injective (check.mpr h).injective⟩⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_embedded_example_of_certified_injective
#print axioms TwoAxisHelicoid.marked_example_iff_certified_core_injective
