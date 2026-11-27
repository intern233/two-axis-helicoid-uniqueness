import TwoAxisHelicoid.HelicoidLocalGraph
import TwoAxisHelicoid.OrderedProperCover
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

namespace TwoAxisHelicoid
open Set

/-- Exact reconstruction in the globally injective helicoid tube. -/
theorem helicoid_normal_coordinates_reconstruct {y : HelicoidTubeCoordinates}
    (hy : y ∈ helicoidTubeEquiv.target) :
    helicoidTubeMap ((helicoidSignedDistance y,(helicoidBaseCoordinates y).1),
      (helicoidBaseCoordinates y).2) = y :=
  helicoidTubeEquiv.right_inv hy

/-- Bounded normal height makes the actual projection proper whenever the
ambient surface map is proper. This proves compactness of preimages from
compact tube blocks, rather than postulating properness of the projection. -/
theorem helicoid_projection_isProperMap {E : Type*} [TopologicalSpace E]
    {X : E → HelicoidTubeCoordinates} (hp : IsProperMap X)
    (hTube : ∀ e, X e ∈ helicoidTubeEquiv.target) {r : ℝ}
    (hheight : ∀ e, |helicoidSignedDistance (X e)| ≤ r) :
    IsProperMap (fun e => helicoidBaseCoordinates (X e)) := by
  have hc : Continuous (fun e => helicoidBaseCoordinates (X e)) :=
    continuous_iff_continuousAt.mpr (fun e =>
      (helicoidBaseCoordinates_contDiffAt (hTube e)).continuousAt.comp hp.continuous.continuousAt)
  refine isProperMap_iff_isCompact_preimage.mpr ⟨hc,?_⟩
  intro K hK
  let block : Set (ℝ × (ℝ × ℝ)) := Icc (-r) r ×ˢ K
  let T : (ℝ × (ℝ × ℝ)) → HelicoidTubeCoordinates :=
    fun q => helicoidTubeMap ((q.1,q.2.1),q.2.2)
  have hT : Continuous T := helicoidTubeMap_contDiff.continuous.comp (by fun_prop)
  have hb : IsCompact block := isCompact_Icc.prod hK
  apply (hp.isCompact_preimage (hb.image hT)).of_isClosed_subset (hK.isClosed.preimage hc)
  intro e he
  refine ⟨(helicoidSignedDistance (X e),helicoidBaseCoordinates (X e)),?_,?_⟩
  · exact ⟨abs_le.mp (hheight e),he⟩
  · exact helicoid_normal_coordinates_reconstruct (hTube e)

/-- A connected embedded surface contained in the tube, with bounded height,
proper ambient map and locally invertible actual projection has one sheet.
All hypotheses concern actual maps; the ordering argument is already proved. -/
theorem helicoid_connected_proper_tube_embedding_one_sheet
    {E : Type*} [TopologicalSpace E] [PreconnectedSpace E] [Nonempty E]
    {X : E → HelicoidTubeCoordinates} (hp : IsProperMap X)
    (hX : Function.Injective X) (hTube : ∀ e, X e ∈ helicoidTubeEquiv.target)
    {r : ℝ} (hheight : ∀ e, |helicoidSignedDistance (X e)| ≤ r)
    (hl : IsLocalHomeomorph (fun e => helicoidBaseCoordinates (X e))) :
    ∃ e : E ≃ₜ (ℝ × ℝ), (e : E → ℝ × ℝ) = (fun q => helicoidBaseCoordinates (X q)) ∧
      ∃ s : (ℝ × ℝ) → ℝ, Continuous s ∧ ∀ q,
        |s q| ≤ r ∧ X (e.symm q) = helicoidTubeMap ((s q,q.1),q.2) := by
  have hpB := helicoid_projection_isProperMap hp hTube hheight
  have hs : Continuous (fun e => helicoidSignedDistance (X e)) :=
    continuous_iff_continuousAt.mpr (fun e =>
      (helicoidSignedDistance_contDiffAt (hTube e)).continuousAt.comp hp.continuous.continuousAt)
  have hsep : ∀ d e, helicoidBaseCoordinates (X d) = helicoidBaseCoordinates (X e) →
      helicoidSignedDistance (X d) = helicoidSignedDistance (X e) → d = e := by
    intro d e hb hh
    apply hX
    rw [← helicoid_normal_coordinates_reconstruct (hTube d),
      ← helicoid_normal_coordinates_reconstruct (hTube e),hb,hh]
  have hi := connected_ordered_proper_local_homeomorph_injective hpB hs hl hsep
  have hu := proper_local_homeomorph_surjective hpB hl
  let e := hl.toHomeomorphOfBijective ⟨hi,hu⟩
  refine ⟨e,rfl,(fun q => helicoidSignedDistance (X (e.symm q))),hs.comp e.symm.continuous,?_⟩
  intro q
  refine ⟨hheight _,?_⟩
  have hb : helicoidBaseCoordinates (X (e.symm q)) = q := e.apply_symm_apply q
  rw [← helicoid_normal_coordinates_reconstruct (hTube (e.symm q)),hb]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoid_connected_proper_tube_embedding_one_sheet
