import TwoAxisHelicoid.ClosedOriginalNormalPairs
import TwoAxisHelicoid.FixedCutoffPointNormalCompactness
import TwoAxisHelicoid.FellCompactDistanceProfiles
import TwoAxisHelicoid.MeasuredPositiveScrewCutoff

namespace TwoAxisHelicoid
open Set Filter Metric Topology TopologicalSpace
open scoped Topology

/-- Every member of the one cutoff has a nonempty closed physical
point-normal set, including periodic members of the original class. -/
theorem cutoff_member_has_closed_normals {I : Type*} (diskTop : TorusDiskComplementHandleProperty)
    (η : ℝ) (family : FixedAxisHelicoidNormalClass I)
    (slab : ∀ m, HasNoScrewBelow η (physicalNormalPositions (family.normal m)) →
      (∃ h : ℝ, 0<h ∧ unitHelicoidScrew h '' physicalNormalPositions (family.normal m)=physicalNormalPositions (family.normal m)) →
      Nonempty (PeriodicSlabNormalMember (family.normal m)))
    (m : I) (cut : HasNoScrewBelow η (physicalNormalPositions (family.normal m))) :
    IsClosed (family.normal m) ∧ (family.normal m).Nonempty := by
  by_cases periodic : ∃ h : ℝ, 0<h ∧ unitHelicoidScrew h '' physicalNormalPositions (family.normal m)=physicalNormalPositions (family.normal m)
  · obtain ⟨P⟩ := slab m cut periodic
    obtain ⟨f,_⟩ := diskTop P.torus P.disk P.embeddedDisk
    obtain ⟨C⟩ := exists_torus_generating_core_model P.torus
    let b : PuncturedPeriodTorus P.torus := ⟨C.base.1,fun eq => C.closure_avoids (eq ▸ subset_closure C.base.2)⟩
    rw [P.measured]
    apply closed_normal_pairs _ P.regular.1 (P.slab (f b)).1
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isClosedEmbedding.comp P.closed
  · obtain ⟨s,eq⟩ := family.nonperiodic m (fun h hp symm => periodic ⟨h,hp,symm⟩)
    rw [←eq]
    exact s.normal_pairs_closed_nonempty

/-- One compact class in any parameter topology suffices. Only the
open/compact tests for the actual physical point-normal sets on that
cutoff are required. The convergent subsequence and all regularity and
nonemptiness properties of the limiting set are derived. -/
theorem fixed_class_fell_compactness_gives_handle_limit {I : Type*} [TopologicalSpace I]
    (diskTop : TorusDiskComplementHandleProperty) (η : ℝ) (family : FixedAxisHelicoidNormalClass I)
    (compact : IsCompact {m : I | HasNoScrewBelow η (physicalNormalPositions (family.normal m))})
    (smooth : ContinuousFellOn family.normal {m : I | HasNoScrewBelow η (physicalNormalPositions (family.normal m))})
    (slab : ∀ m, HasNoScrewBelow η (physicalNormalPositions (family.normal m)) →
      (∃ h : ℝ, 0<h ∧ unitHelicoidScrew h '' physicalNormalPositions (family.normal m)=physicalNormalPositions (family.normal m)) →
      Nonempty (PeriodicSlabNormalMember (family.normal m))) :
    FixedCutoffHandleCompactness η := by
  apply point_normal_cutoff_subsequence_gives_handle_limit diskTop η family _ slab
  intro a inside
  have reg := cutoff_member_has_closed_normals diskTop η family slab
  obtain ⟨m,hm,φ,mono,limit⟩ := compact_fell_distances_have_common_subsequence compact
    (fun i hi => (reg i hi).2) smooth (denseSeq PhysicalPositionNormal) a inside
  refine ⟨m,hm,φ,mono,dense_distances_determine_local_limit (fun n => (reg _ (inside (φ n))).2)
    (reg m hm).2 (reg m hm).1 (tendsto_pi_nhds.mpr limit)⟩

/-- Both Appendix B conclusions along the single-cutoff flux proof,
using the actual compact class and its physical normal pairs. -/
theorem original_appendix_B_from_fell_compact_class {I : Type*} [TopologicalSpace I]
    (diskTop : TorusDiskComplementHandleProperty) (η : ℝ) (eta : Real.pi/2<η) (family : FixedAxisHelicoidNormalClass I)
    (halfPeriod : I → WithTop ℝ)
    (record : ∀ m, LeastPeriodOrInfinity (positiveScrewHalfPeriods
      (physicalNormalPositions (family.normal m))) (halfPeriod m))
    (compact : IsCompact {m : I | (η : WithTop ℝ)≤halfPeriod m})
    (smooth : ContinuousFellOn family.normal {m : I | (η : WithTop ℝ)≤halfPeriod m})
    (slab : ∀ m (k : ℝ), η≤k → halfPeriod m=(k : WithTop ℝ) →
      (∀ b : ℝ, physicalNormalPositions (family.normal m)≠range (axisRuledHelicoid Complex.I 1 b)) →
      ∃ P : PeriodicSlabNormalMember (family.normal m), P.halfPeriod=k) :
    HasSubsequentialSmoothGeneratingCurves positiveUnitPitchFamily ∧
    (∃ ε : ℝ, 0<ε ∧ (∀ W∈embeddedPitchFamily, ε≤W.t) ∧
      ∀ s : OriginalHelicoidRepresentative, ∃ W∈positiveUnitPitchFamily, ε≤W.t ∧ (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalHelicoidRepresentative => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite := by
  have classes : {m : I | (η : WithTop ℝ)≤halfPeriod m}=
      {m : I | HasNoScrewBelow η (physicalNormalPositions (family.normal m))} :=
    Set.ext fun m => measured_screw_cutoff_iff (record m) η
  rw [classes] at compact smooth
  apply original_graph_appendix_B_from_one_fixed_cutoff η eta
  apply fixed_class_fell_compactness_gives_handle_limit diskTop η family compact smooth
  intro m cut positivePeriod
  obtain ⟨r,rp,sym⟩ := positivePeriod
  obtain ⟨k,hk,_⟩ := least_period_finite_of_mem (record m) ⟨r,rp,sym⟩
  have threshold := (measured_screw_cutoff_iff (record m) η).mpr cut
  rw [hk,WithTop.coe_le_coe] at threshold
  obtain ⟨P,_⟩ := slab m k threshold hk
    (positive_cutoff_excludes_reference_helicoid ((half_pos Real.pi_pos).trans eta) cut)
  exact ⟨P⟩

/-- The same single-cutoff flux argument with the half-period read from
the measured position set. No global minimum or omitted point is required. -/
theorem original_appendix_B_from_physical_period_cutoff {I : Type*} [TopologicalSpace I]
    (diskTop : TorusDiskComplementHandleProperty) (η : ℝ) (eta : Real.pi/2<η) (family : FixedAxisHelicoidNormalClass I)
    (compact : IsCompact {m : I | (η : WithTop ℝ)≤physicalScrewHalfPeriod (physicalNormalPositions (family.normal m))})
    (smooth : ContinuousFellOn family.normal {m : I | (η : WithTop ℝ)≤physicalScrewHalfPeriod (physicalNormalPositions (family.normal m))})
    (slab : ∀ m (k : ℝ), η≤k → physicalScrewHalfPeriod (physicalNormalPositions (family.normal m))=(k : WithTop ℝ) →
      (∀ b : ℝ, physicalNormalPositions (family.normal m)≠range (axisRuledHelicoid Complex.I 1 b)) →
      ∃ P : PeriodicSlabNormalMember (family.normal m), P.halfPeriod=k) :
    HasSubsequentialSmoothGeneratingCurves positiveUnitPitchFamily ∧
    (∃ ε : ℝ, 0<ε ∧ (∀ W∈embeddedPitchFamily, ε≤W.t) ∧
      ∀ s : OriginalHelicoidRepresentative, ∃ W∈positiveUnitPitchFamily, ε≤W.t ∧ (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalHelicoidRepresentative => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite := by
  have classes : {m : I | (η : WithTop ℝ)≤physicalScrewHalfPeriod (physicalNormalPositions (family.normal m))}=
      {m : I | HasNoScrewBelow η (physicalNormalPositions (family.normal m))} :=
    Set.ext fun m => measured_physical_screw_infimum_cutoff _ η
  rw [classes] at compact smooth
  apply original_graph_appendix_B_from_one_fixed_cutoff η eta
  apply fixed_class_fell_compactness_gives_handle_limit diskTop η family compact smooth
  intro m cut present
  have pos := (half_pos Real.pi_pos).trans eta
  obtain ⟨k,threshold,measured,_⟩ := positive_cutoff_attains_measured_screw_period pos cut present
  obtain ⟨P,_⟩ := slab m k threshold measured (positive_cutoff_excludes_reference_helicoid pos cut)
  exact ⟨P⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.cutoff_member_has_closed_normals
#print axioms TwoAxisHelicoid.fixed_class_fell_compactness_gives_handle_limit
#print axioms TwoAxisHelicoid.original_appendix_B_from_fell_compact_class

#print axioms TwoAxisHelicoid.original_appendix_B_from_physical_period_cutoff
