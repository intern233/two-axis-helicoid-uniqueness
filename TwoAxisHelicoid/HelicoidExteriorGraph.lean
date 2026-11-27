import TwoAxisHelicoid.HelicoidEndOneSheet
import TwoAxisHelicoid.ExteriorPlaneBase

namespace TwoAxisHelicoid
open Set Filter Bornology
open scoped Topology
set_option maxHeartbeats 1000000

theorem helicoidEndProjection_isLocalHomeomorph {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (hX : Continuous X)
    {K : Set M} (hK : IsClosed K) {B : Set (ℝ × ℝ)} (hB : IsOpen B)
    (hTube : ∀ q ∉ K, X q ∈ helicoidTubeEquiv.target)
    (hl : IsLocalHomeomorphOn (fun q => helicoidBaseCoordinates (X q)) Kᶜ) :
    IsLocalHomeomorph (helicoidEndProjection X K B) := by
  have hS := helicoidProjectedEnd_isOpen hX hK hB hTube
  have hi := hS.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hc : IsLocalHomeomorph (fun q : helicoidProjectedEnd X K B => helicoidBaseCoordinates (X q.1)) :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
      (hl.comp (hi.isLocalHomeomorphOn (s := univ)) (fun q _hq => q.2.1))
  exact hc.of_comp hB.isOpenEmbedding_subtypeVal.isLocalHomeomorph
    (helicoidEndProjection_continuous hX hTube)

/-- A large exterior base and a global single graph are selected from the
actual spatial map. The only local input is invertibility of its actual
normal projection outside a compact core. -/
theorem helicoid_punctured_curve_exterior_normal_graph
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [CompactSpace M] [T2Space M]
    (p : M) {X : {q : M // q ≠ p} → HelicoidTubeCoordinates}
    (hp : IsProperMap X) {K : Set {q : M // q ≠ p}}
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
  apply helicoid_punctured_curve_end_single_graph p hp hX hK hB hBc
    (exteriorPlaneBase_unbounded R) hr hTube hheight
    (fun q hq => hC (X q) ⟨q,hq,rfl⟩) (show 2*C+1 ≤ R by dsimp [R]; linarith) subset_rfl
  exact helicoidEndProjection_isLocalHomeomorph hp.continuous hK.isClosed hB hTube hl

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoid_punctured_curve_exterior_normal_graph
