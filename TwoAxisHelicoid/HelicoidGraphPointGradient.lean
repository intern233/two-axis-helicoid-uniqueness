import TwoAxisHelicoid.HelicoidGraphGerm
import TwoAxisHelicoid.ChartProjectionTangent

namespace TwoAxisHelicoid
open Real Set Filter
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

theorem helicoid_global_graph_gradient_le_of_chart_angle
    {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} {S : Set M} {B : Set (ℝ × ℝ)} (hB : IsOpen B)
    (e : S ≃ₜ B) (he : ∀ q : S, (e q).1 = helicoidBaseCoordinates (X q.1))
    {u : B → ℝ} (hgraph : ∀ b, X (e.symm b).1 = helicoidTubeMap ((u b,b.1.1),b.1.2))
    (b : B) (hu : DifferentiableAt ℝ (extendOpenScalar u) b.1) (hs : |u b| ≤ 1/2)
    (c : OpenPartialHomeomorph M (ℝ × ℝ)) (hq : (e.symm b).1 ∈ c.source)
    (hX : ContDiffAt ℝ (∞ : WithTop ℕ∞) (X ∘ c.symm) (c (e.symm b).1))
    (hTube : X (e.symm b).1 ∈ helicoidTubeEquiv.target)
    (hD : Function.Injective (fderiv ℝ (X ∘ c.symm) (c (e.symm b).1)))
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1/2)
    (hangle : ∀ v : ℝ × ℝ,
      (∑ i, helicoidNormalField (X (e.symm b).1) i*
        tubeCartesian (fderiv ℝ (X ∘ c.symm) (c (e.symm b).1) v) i)^2 ≤
      κ^2*(∑ i, (tubeCartesian (fderiv ℝ (X ∘ c.symm) (c (e.symm b).1) v) i)^2)) :
    helicoidGraphGradientNorm (extendOpenScalar u) b.1 ≤ 2*κ := by
  have hb : helicoidBaseCoordinates (X (e.symm b).1) = b.1 := by
    rw [← he,e.apply_symm_apply]
  obtain ⟨φ,hφ,hmap,_hsmooth,hnew⟩ := chart_projection_local_inverse_angle c hq hX hTube hD
    hκ0 (hκ.trans_lt (by norm_num)) hangle
  rw [hb] at hnew
  have hgerm := helicoid_graphMap_eventuallyEq_local_inverse hB e he hgraph b φ hφ hmap
  have hv : helicoidGraphMap (extendOpenScalar u) b.1 = X (e.symm b).1 := by
    rw [hgraph b]
    simp only [helicoidGraphMap,extendOpenScalar,dite_eq_left b.2]
  apply helicoidGraphGradientNorm_le_of_angle hu
    (by simpa only [extendOpenScalar,dite_eq_left b.2] using hs) hκ0 hκ
  intro v
  rw [hv,hgerm.fderiv_eq]
  exact hnew v

/-- Controlled curves in the original surface chart bound the gradient of
the already constructed global graph. No tangent-plane identification is
an extra assumption. -/
theorem helicoid_global_graph_gradient_le_of_controlled_curves
    {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} {S : Set M} {B : Set (ℝ × ℝ)} (hB : IsOpen B)
    (e : S ≃ₜ B) (he : ∀ q : S, (e q).1 = helicoidBaseCoordinates (X q.1))
    {u : B → ℝ} (hgraph : ∀ b, X (e.symm b).1 = helicoidTubeMap ((u b,b.1.1),b.1.2))
    (b : B) (hu : DifferentiableAt ℝ (extendOpenScalar u) b.1) (hs : |u b| ≤ 1/2)
    (c : OpenPartialHomeomorph M (ℝ × ℝ)) (hq : (e.symm b).1 ∈ c.source)
    (hX : ContDiffAt ℝ (∞ : WithTop ℕ∞) (X ∘ c.symm) (c (e.symm b).1))
    (hTube : X (e.symm b).1 ∈ helicoidTubeEquiv.target)
    (hD : Function.Injective (fderiv ℝ (X ∘ c.symm) (c (e.symm b).1)))
    {ε A : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1/2) (hA : 0 ≤ A)
    (hsmall : (3+A/2)*sqrt ε ≤ 1/2)
    (hcurves : HasControlledUnitTangentCurves (X (e.symm b).1)
      (fderiv ℝ (X ∘ c.symm) (c (e.symm b).1)) ε A) :
    helicoidGraphGradientNorm (extendOpenScalar u) b.1 ≤ 2*((3+A/2)*sqrt ε) :=
  helicoid_global_graph_gradient_le_of_chart_angle hB e he hgraph b hu hs c hq hX hTube hD
    (by positivity) hsmall (controlled_tangent_curves_normal_angle_bound hε0 hε hA hcurves)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoid_global_graph_gradient_le_of_controlled_curves
