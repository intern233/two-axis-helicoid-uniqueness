import TwoAxisHelicoid.HelicoidEndDomain

namespace TwoAxisHelicoid
open Set Filter Bornology
open scoped Topology

/-- Moving the base beyond the compact core separates every bounded-height
normal block from the core. The separation follows from the actual norm
estimate for the normal projection. -/
theorem helicoidHeightBlock_avoids_core {M : Type*} {X : M → HelicoidTubeCoordinates}
    {K : Set M} {B : Set (ℝ × ℝ)} {r C R : ℝ} (hr : r < 1)
    (hC : ∀ q ∈ K, ‖X q‖ ≤ C) (hR : 2*C+1 ≤ R)
    (hB : B ⊆ {p | R < ‖p‖}) :
    Disjoint K (X ⁻¹' helicoidHeightBlock r B) := by
  apply Set.disjoint_left.mpr
  intro q hqK hqB
  obtain ⟨ht,hb,_hh⟩ := helicoidHeightBlock_coordinates hr hqB
  have hfar := hB hb
  have hbound := helicoidBaseCoordinates_norm_bound ht
  have hcore := hC q hqK
  change R < ‖helicoidBaseCoordinates (X q)‖ at hfar
  linarith

/-- Properness of the projection to an open exterior base is proved
relative to that base. Compact blocks avoid the omitted compact core, so
no properness of the spatial map restricted to an open end is assumed. -/
theorem helicoidEndProjection_isProperMap {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (hp : IsProperMap X)
    {K : Set M} {B : Set (ℝ × ℝ)} {r : ℝ} (hr : r < 1)
    (hTube : ∀ q ∉ K, X q ∈ helicoidTubeEquiv.target)
    (hheight : ∀ q ∉ K, |helicoidSignedDistance (X q)| ≤ r)
    (hsep : Disjoint K (X ⁻¹' helicoidHeightBlock r B)) :
    IsProperMap (helicoidEndProjection X K B) := by
  refine isProperMap_iff_isCompact_preimage.mpr
    ⟨helicoidEndProjection_continuous hp.continuous hTube,?_⟩
  intro L hL
  let A : Set (ℝ × ℝ) := Subtype.val '' L
  have hA : IsCompact A := hL.image continuous_subtype_val
  have hAB : A ⊆ B := by rintro p ⟨q,_hq,rfl⟩; exact q.2
  rw [Subtype.isCompact_iff]
  have heq : Subtype.val '' (helicoidEndProjection X K B ⁻¹' L) =
      X ⁻¹' helicoidHeightBlock r A := by
    ext q
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact mem_helicoidHeightBlock (hTube z.1 z.2.1) (hheight z.1 z.2.1)
        ⟨helicoidEndProjection X K B z,hz,rfl⟩
    · intro hq
      obtain ⟨_ht,hqA,_hh⟩ := helicoidHeightBlock_coordinates hr hq
      have hqK : q ∉ K := fun h => (Set.disjoint_left.mp hsep) h
        (helicoidHeightBlock_mono r hAB hq)
      have hqS : q ∈ helicoidProjectedEnd X K B := ⟨hqK,hAB hqA⟩
      obtain ⟨b,hb,hbq⟩ := hqA
      refine ⟨⟨q,hqS⟩,?_,rfl⟩
      have hproj : helicoidEndProjection X K B ⟨q,hqS⟩ = b := Subtype.ext hbq.symm
      change helicoidEndProjection X K B ⟨q,hqS⟩ ∈ L
      rw [hproj]
      exact hb
  rw [heq]
  exact hp.isCompact_preimage (helicoidHeightBlock_isCompact r hA)

/-- The exterior projection domain omits only a compact part of the
original surface. This compactness is in the original parameter surface,
not in the open subend. -/
theorem helicoidProjectedEnd_complement_isCompact {M : Type*} [TopologicalSpace M] [T2Space M]
    {X : M → HelicoidTubeCoordinates} (hp : IsProperMap X)
    {K : Set M} (hK : IsCompact K) {B : Set (ℝ × ℝ)} (hB : IsOpen B)
    (hBc : IsCompact Bᶜ) {r : ℝ}
    (hTube : ∀ q ∉ K, X q ∈ helicoidTubeEquiv.target)
    (hheight : ∀ q ∉ K, |helicoidSignedDistance (X q)| ≤ r) :
    IsCompact (helicoidProjectedEnd X K B)ᶜ := by
  have hc := hK.union (hp.isCompact_preimage (helicoidHeightBlock_isCompact r hBc))
  apply hc.of_isClosed_subset
    (helicoidProjectedEnd_isOpen hp.continuous hK.isClosed hB hTube).isClosed_compl
  intro q hq
  by_cases hqK : q ∈ K
  · exact Or.inl hqK
  · right
    apply mem_helicoidHeightBlock (hTube q hqK) (hheight q hqK)
    intro hqB
    exact hq ⟨hqK,hqB⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidEndProjection_isProperMap
#print axioms TwoAxisHelicoid.helicoidProjectedEnd_complement_isCompact
