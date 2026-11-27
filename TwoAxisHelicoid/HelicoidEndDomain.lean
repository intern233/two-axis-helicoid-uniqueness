import TwoAxisHelicoid.HelicoidProjectionBound

namespace TwoAxisHelicoid
open Set Filter Bornology
open scoped Topology

def helicoidProjectedEnd {M : Type*} (X : M → HelicoidTubeCoordinates)
    (K : Set M) (B : Set (ℝ × ℝ)) : Set M :=
  {q | q ∉ K ∧ helicoidBaseCoordinates (X q) ∈ B}

noncomputable def helicoidEndProjection {M : Type*} (X : M → HelicoidTubeCoordinates)
    (K : Set M) (B : Set (ℝ × ℝ)) : helicoidProjectedEnd X K B → B :=
  fun q => ⟨helicoidBaseCoordinates (X q.1),q.2.2⟩

theorem helicoidProjectedEnd_isOpen {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (hX : Continuous X)
    {K : Set M} (hK : IsClosed K) {B : Set (ℝ × ℝ)} (hB : IsOpen B)
    (hTube : ∀ q ∉ K, X q ∈ helicoidTubeEquiv.target) :
    IsOpen (helicoidProjectedEnd X K B) := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  have hc : ContinuousAt (fun z => helicoidBaseCoordinates (X z)) q :=
    (helicoidBaseCoordinates_contDiffAt (hTube q hq.1)).continuousAt.comp hX.continuousAt
  filter_upwards [hK.isOpen_compl.mem_nhds hq.1,hc.eventually (hB.mem_nhds hq.2)] with z hzK hzB
  exact ⟨hzK,hzB⟩

theorem helicoidEndProjection_continuous {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (hX : Continuous X)
    {K : Set M} {B : Set (ℝ × ℝ)}
    (hTube : ∀ q ∉ K, X q ∈ helicoidTubeEquiv.target) :
    Continuous (helicoidEndProjection X K B) := by
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro q
  exact ((helicoidBaseCoordinates_contDiffAt (hTube q.1 q.2.1)).continuousAt.comp
    hX.continuousAt).comp continuous_subtype_val.continuousAt

def helicoidHeightBlock (r : ℝ) (A : Set (ℝ × ℝ)) : Set HelicoidTubeCoordinates :=
  (fun q : ℝ × (ℝ × ℝ) => helicoidTubeMap ((q.1,q.2.1),q.2.2)) '' (Icc (-r) r ×ˢ A)

theorem helicoidHeightBlock_isCompact (r : ℝ) {A : Set (ℝ × ℝ)} (hA : IsCompact A) :
    IsCompact (helicoidHeightBlock r A) :=
  (isCompact_Icc.prod hA).image
    (helicoidTubeMap_contDiff.continuous.comp (by fun_prop))

theorem helicoidHeightBlock_mono (r : ℝ) {A B : Set (ℝ × ℝ)} (hAB : A ⊆ B) :
    helicoidHeightBlock r A ⊆ helicoidHeightBlock r B :=
  image_mono (prod_mono subset_rfl hAB)

theorem mem_helicoidHeightBlock {r : ℝ} {A : Set (ℝ × ℝ)} {y : HelicoidTubeCoordinates}
    (hy : y ∈ helicoidTubeEquiv.target) (hs : |helicoidSignedDistance y| ≤ r)
    (hA : helicoidBaseCoordinates y ∈ A) : y ∈ helicoidHeightBlock r A :=
  ⟨(helicoidSignedDistance y,helicoidBaseCoordinates y),⟨abs_le.mp hs,hA⟩,
    helicoid_normal_coordinates_reconstruct hy⟩

theorem helicoidHeightBlock_coordinates {r : ℝ} (hr : r < 1)
    {A : Set (ℝ × ℝ)} {y : HelicoidTubeCoordinates} (hy : y ∈ helicoidHeightBlock r A) :
    y ∈ helicoidTubeEquiv.target ∧ helicoidBaseCoordinates y ∈ A ∧
      |helicoidSignedDistance y| ≤ r := by
  rcases hy with ⟨⟨s,p⟩,⟨hs,hp⟩,rfl⟩
  have hs' : |s| ≤ r := abs_le.mpr hs
  have hstrip : ((s,p.1),p.2) ∈ helicoidTubeEquiv.source := hs'.trans_lt hr
  have hi : helicoidTubeEquiv.symm (helicoidTubeMap ((s,p.1),p.2)) = ((s,p.1),p.2) :=
    helicoidTubeEquiv.left_inv hstrip
  refine ⟨helicoidTubeEquiv.map_source hstrip,?_,?_⟩
  · simpa only [helicoidBaseCoordinates,hi] using hp
  · simpa only [helicoidSignedDistance,hi] using hs'

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidHeightBlock_coordinates
