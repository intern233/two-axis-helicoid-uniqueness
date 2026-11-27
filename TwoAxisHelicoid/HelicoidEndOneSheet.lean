import TwoAxisHelicoid.HelicoidEndProperness
import TwoAxisHelicoid.PuncturedCurveEndCover
import TwoAxisHelicoid.PuncturedCurveNoncompact

namespace TwoAxisHelicoid
open Set Filter Bornology
open scoped Topology
set_option maxHeartbeats 1000000

theorem helicoidEndProjection_compact_control {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (hX : Continuous X)
    {K : Set M} {B : Set (ℝ × ℝ)}
    (hTube : ∀ q ∉ K, X q ∈ helicoidTubeEquiv.target)
    {L : Set M} (hL : IsCompact L) :
    IsBounded (((Subtype.val : B → ℝ × ℝ) ∘ helicoidEndProjection X K B) ''
      (Subtype.val ⁻¹' L)) := by
  obtain ⟨C,hC⟩ := (hL.image hX).isBounded.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨2*C+1,?_⟩
  rintro z ⟨q,hq,rfl⟩
  change ‖helicoidBaseCoordinates (X q.1)‖ ≤ 2*C+1
  exact (helicoidBaseCoordinates_norm_bound (hTube q.1 q.2.1)).trans (by
    linarith [hC (X q.1) ⟨q.1,hq,rfl⟩])

theorem helicoidEndHeight_continuous {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (hX : Continuous X)
    {K : Set M} {B : Set (ℝ × ℝ)}
    (hTube : ∀ q ∉ K, X q ∈ helicoidTubeEquiv.target) :
    Continuous (fun q : helicoidProjectedEnd X K B => helicoidSignedDistance (X q.1)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  exact ((helicoidSignedDistance_contDiffAt (hTube q.1 q.2.1)).continuousAt.comp
    hX.continuousAt).comp continuous_subtype_val.continuousAt

theorem helicoidEnd_fiber_height_separates {M : Type*}
    {X : M → HelicoidTubeCoordinates} {K : Set M} {B : Set (ℝ × ℝ)}
    (hX : InjOn X Kᶜ)
    (hTube : ∀ q ∉ K, X q ∈ helicoidTubeEquiv.target)
    (d e : helicoidProjectedEnd X K B)
    (hb : helicoidEndProjection X K B d = helicoidEndProjection X K B e)
    (hh : helicoidSignedDistance (X d.1) = helicoidSignedDistance (X e.1)) : d = e := by
  apply Subtype.ext
  apply hX d.2.1 e.2.1
  have hbase : helicoidBaseCoordinates (X d.1) = helicoidBaseCoordinates (X e.1) :=
    congrArg Subtype.val hb
  rw [← helicoid_normal_coordinates_reconstruct (hTube d.1 d.2.1),
    ← helicoid_normal_coordinates_reconstruct (hTube e.1 e.2.1),hbase,hh]

/-- The global one-sheet normal-graph step on an actual once-punctured
compact complex curve. The spatial map is proper and injective, the actual
projection is locally invertible, and the base is chosen beyond the core.
End connectedness, relative projection properness and the height function
are all derived. Smoothness and asymptotic gradient control are separate. -/
theorem helicoid_punctured_curve_end_single_graph
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [CompactSpace M] [T2Space M]
    (p : M) {X : {q : M // q ≠ p} → HelicoidTubeCoordinates}
    (hp : IsProperMap X) {K : Set {q : M // q ≠ p}}
    (hX : InjOn X Kᶜ) (hK : IsCompact K)
    {B : Set (ℝ × ℝ)} [PreconnectedSpace B] (hB : IsOpen B)
    (hBc : IsCompact Bᶜ) (hBun : ¬ IsBounded B)
    {r C R : ℝ} (hr : r < 1)
    (hTube : ∀ q ∉ K, X q ∈ helicoidTubeEquiv.target)
    (hheight : ∀ q ∉ K, |helicoidSignedDistance (X q)| ≤ r)
    (hC : ∀ q ∈ K, ‖X q‖ ≤ C) (hR : 2*C+1 ≤ R)
    (hfar : B ⊆ {q | R < ‖q‖})
    (hl : IsLocalHomeomorph (helicoidEndProjection X K B)) :
    ∃ e : helicoidProjectedEnd X K B ≃ₜ B,
      (e : helicoidProjectedEnd X K B → B) = helicoidEndProjection X K B ∧
      ∃ u : B → ℝ, Continuous u ∧ ∀ q,
        |u q| ≤ r ∧ X (e.symm q).1 = helicoidTubeMap ((u q,q.1.1),q.1.2) := by
  have hSopen := helicoidProjectedEnd_isOpen hp.continuous hK.isClosed hB hTube
  have hSc := helicoidProjectedEnd_complement_isCompact hp hK hB hBc hTube hheight
  have hsep := helicoidHeightBlock_avoids_core hr hC hR hfar
  have hproper := helicoidEndProjection_isProperMap hp hr hTube hheight hsep
  have hhc := helicoidEndHeight_continuous (B := B) hp.continuous hTube
  have hunbounded : ¬ IsBounded (range (Subtype.val : B → ℝ × ℝ)) := by
    simpa only [Subtype.range_coe] using hBun
  have hinj := punctured_curve_ordered_end_projection_injective p hSopen hSc
    hproper hhc hl (helicoidEnd_fiber_height_separates hX hTube) hunbounded
    (fun _ hL => helicoidEndProjection_compact_control hp.continuous hTube hL)
  obtain ⟨q,hq⟩ := cofinite_punctured_curve_nonempty p hSc
  let : Nonempty (helicoidProjectedEnd X K B) := ⟨⟨q,hq⟩⟩
  have hsurj := proper_local_homeomorph_surjective hproper hl
  let e := hl.toHomeomorphOfBijective ⟨hinj,hsurj⟩
  refine ⟨e,rfl,(fun q => helicoidSignedDistance (X (e.symm q).1)),
    hhc.comp e.symm.continuous,?_⟩
  intro b
  refine ⟨hheight _ (e.symm b).2.1,?_⟩
  have hb : helicoidBaseCoordinates (X (e.symm b).1) = b.1 :=
    congrArg Subtype.val (e.apply_symm_apply b)
  simpa only [hb] using (helicoid_normal_coordinates_reconstruct
    (hTube _ (e.symm b).2.1)).symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoid_punctured_curve_end_single_graph
