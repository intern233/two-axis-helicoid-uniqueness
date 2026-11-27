import TwoAxisHelicoid.HelicoidGraphSmoothness
import TwoAxisHelicoid.ChartThinProjection

namespace TwoAxisHelicoid
open Real Set Filter
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

/-- A smooth global normal graph derived from proper embeddedness of a
punctured compact curve and controlled actual tangent curves. -/
theorem controlled_thin_punctured_curve_smooth_normal_graph
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [CompactSpace M] [T2Space M]
    (p : M) {X : {q : M // q ≠ p} → HelicoidTubeCoordinates}
    (hp : IsProperMap X) {K : Set {q : M // q ≠ p}}
    (hX : InjOn X Kᶜ) (hK : IsCompact K)
    (c : {q : M // q ≠ p} → OpenPartialHomeomorph {q : M // q ≠ p} (ℝ × ℝ))
    (hmem : ∀ q ∉ K, q ∈ (c q).source)
    (hsm : ∀ q ∉ K, ContDiffAt ℝ (∞ : WithTop ℕ∞) (X ∘ (c q).symm) (c q q))
    (hD : ∀ q ∉ K, Function.Injective (fderiv ℝ (X ∘ (c q).symm) (c q q)))
    {ε A : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1/2) (hA : 0 ≤ A)
    (hsmall : (3+A/2)*sqrt ε < 1)
    (hTube : ∀ q ∉ K, X q ∈ helicoidTubeEquiv.target)
    (hheight : ∀ q ∉ K, |helicoidSignedDistance (X q)| ≤ ε)
    (hcurves : ∀ q ∉ K, HasControlledUnitTangentCurves (X q)
      (fderiv ℝ (X ∘ (c q).symm) (c q q)) ε A) :
    ∃ R : ℝ, 0 < R ∧ IsCompact (helicoidProjectedEnd X K (exteriorPlaneBase R))ᶜ ∧
      ∃ e : helicoidProjectedEnd X K (exteriorPlaneBase R) ≃ₜ exteriorPlaneBase R,
        (e : helicoidProjectedEnd X K (exteriorPlaneBase R) → exteriorPlaneBase R) =
          helicoidEndProjection X K (exteriorPlaneBase R) ∧
        ∃ u : exteriorPlaneBase R → ℝ,
          ContDiffOn ℝ (∞ : WithTop ℕ∞) (extendOpenScalar u) (exteriorPlaneBase R) ∧
          ∀ b, |u b| ≤ ε ∧ X (e.symm b).1 = helicoidTubeMap ((u b,b.1.1),b.1.2) := by
  have hl := thin_charts_projection_isLocalHomeomorphOn (S := Kᶜ) c hmem hsm hTube hD
    hε0 hε hA hsmall hcurves
  obtain ⟨R,hR,hSc,e,he,u,_hu,hgraph⟩ := helicoid_punctured_curve_exterior_normal_graph p
    hp hX hK (hε.trans_lt (by norm_num)) hTube hheight hl
  refine ⟨R,hR,hSc,e,he,u,?_,hgraph⟩
  have heval (q : helicoidProjectedEnd X K (exteriorPlaneBase R)) :
      (e q).1 = helicoidBaseCoordinates (X q.1) := by rw [he]; rfl
  have huval (b : exteriorPlaneBase R) :
      u b = helicoidSignedDistance (X (e.symm b).1) := by
    rw [(hgraph b).2]
    exact (helicoidSignedDistance_on_normal
      (show ((u b,b.1.1),b.1.2) ∈ helicoidTubeStrip from
        (hgraph b).1.trans_lt (hε.trans_lt (by norm_num)))).symm
  apply contDiffOn_extendOpenScalar_of_smooth_germs (exteriorPlaneBase_isOpen R)
  apply helicoid_graph_height_has_smooth_germs e heval huval
    (fun q => hTube q.1 q.2.1)
  intro q
  obtain ⟨φ,hφ,hmap,hXs⟩ := thin_chart_projection_local_inverse (c q.1) (hmem q.1 q.2.1)
    (hsm q.1 q.2.1) (hTube q.1 q.2.1) (hD q.1 q.2.1) hε0 hε hA hsmall (hcurves q.1 q.2.1)
  exact ⟨φ,hφ,hmap,by simpa only [heval] using hXs⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.controlled_thin_punctured_curve_smooth_normal_graph
