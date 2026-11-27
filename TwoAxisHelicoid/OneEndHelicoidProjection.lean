import TwoAxisHelicoid.HelicoidExteriorGraph

namespace TwoAxisHelicoid
open Set Filter Bornology
open scoped Topology

/-- The ordered finite covering on an arbitrary one-ended source has one sheet.
A connected tail contains a whole far fiber because its complement is compact. -/
theorem helicoid_one_end_projection
    {M : Type*} [TopologicalSpace M] [T2Space M]
    (tail : ∀ K : Set M, IsCompact K → ∃ U : Set M, IsConnected U ∧ IsCompact Uᶜ ∧ Disjoint U K) {X : M → HelicoidTubeCoordinates}
    (hp : IsProperMap X) {K : Set M}
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
  obtain ⟨U,hU,hUc,hUS⟩ := tail _ hSc
  have hsub : U ⊆ helicoidProjectedEnd X K B := by
    intro x hx
    by_contra hn
    exact Set.disjoint_left.mp hUS hx hn
  have conn : IsPreconnected (Subtype.val ⁻¹' U : Set (helicoidProjectedEnd X K B)) :=
    hU.isPreconnected.preimage_of_isOpenMap Subtype.val_injective hSopen.isOpenMap_subtype_val
      (fun x hx => ⟨⟨x,hsub hx⟩,rfl⟩)
  have hinj := ordered_proper_local_homeomorph_injective_of_bounded_complement hproper hhc hl
    (helicoidEnd_fiber_height_separates hX hTube) conn hunbounded
    (helicoidEndProjection_compact_control hp.continuous hTube hUc)
  obtain ⟨q,hq⟩ := hU.nonempty
  let : Nonempty (helicoidProjectedEnd X K B) := ⟨⟨q,hsub hq⟩⟩
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

/-- Choose an exterior base disjoint from the compact core. -/
theorem helicoid_one_end_exterior_graph
    {M : Type*} [TopologicalSpace M] [T2Space M]
    (tail : ∀ K : Set M, IsCompact K → ∃ U : Set M, IsConnected U ∧ IsCompact Uᶜ ∧ Disjoint U K) {X : M → HelicoidTubeCoordinates}
    (hp : IsProperMap X) {K : Set M}
    (hX : InjOn X Kᶜ) (hK : IsCompact K)
    {r : ℝ} (hr : r < 1)
    (hTube : ∀ q ∉ K, X q ∈ helicoidTubeEquiv.target)
    (hheight : ∀ q ∉ K, |helicoidSignedDistance (X q)| ≤ r)
    (hl : IsLocalHomeomorphOn (fun q => helicoidBaseCoordinates (X q)) Kᶜ) :
    ∃ R : ℝ, 0 < R ∧ IsCompact (helicoidProjectedEnd X K (exteriorPlaneBase R))ᶜ ∧
      ∃ e : helicoidProjectedEnd X K (exteriorPlaneBase R) ≃ₜ exteriorPlaneBase R,
        (e : helicoidProjectedEnd X K (exteriorPlaneBase R) → exteriorPlaneBase R) =
          helicoidEndProjection X K (exteriorPlaneBase R) ∧
        ∃ u : exteriorPlaneBase R → ℝ, Continuous u ∧ ∀ q,
          |u q| ≤ r ∧ X (e.symm q).1 = helicoidTubeMap ((u q,q.1.1),q.1.2) := by
  obtain ⟨C,hC0,hC⟩ := (hK.image hp.continuous).isBounded.exists_pos_norm_le
  let R := 2*C+2
  have hR : 0 < R := by dsimp [R]; positivity
  let : PreconnectedSpace (exteriorPlaneBase R) :=
    isPreconnected_iff_preconnectedSpace.mp (exteriorPlaneBase_isPreconnected hR.le)
  have hB := exteriorPlaneBase_isOpen R
  have hBc := exteriorPlaneBase_complement_isCompact R
  refine ⟨R,hR,helicoidProjectedEnd_complement_isCompact hp hK hB hBc hTube hheight,?_⟩
  apply helicoid_one_end_projection tail hp hX hK hB hBc
    (exteriorPlaneBase_unbounded R) hr hTube hheight
    (fun q hq => hC (X q) ⟨q,hq,rfl⟩) (show 2*C+1 ≤ R by dsimp [R]; linarith) subset_rfl
  exact helicoidEndProjection_isLocalHomeomorph hp.continuous hK.isClosed hB hTube hl

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.helicoid_one_end_exterior_graph
