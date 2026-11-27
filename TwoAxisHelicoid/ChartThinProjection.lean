import TwoAxisHelicoid.ThinCurveProjection
import Mathlib.Topology.IsLocalHomeomorph

namespace TwoAxisHelicoid
open Real Set
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

/-- The inverse function theorem in an actual surface chart gives both a
local normal projection and a smooth actual spatial inverse. -/
theorem thin_chart_projection_local_inverse {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} {q : M}
    (c : OpenPartialHomeomorph M (ℝ × ℝ)) (hq : q ∈ c.source)
    (hX : ContDiffAt ℝ (∞ : WithTop ℕ∞) (X ∘ c.symm) (c q))
    (hTube : X q ∈ helicoidTubeEquiv.target)
    (hD : Function.Injective (fderiv ℝ (X ∘ c.symm) (c q)))
    {ε A : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1/2) (hA : 0 ≤ A)
    (hsmall : (3+A/2)*sqrt ε < 1)
    (hcurves : HasControlledUnitTangentCurves (X q) (fderiv ℝ (X ∘ c.symm) (c q)) ε A) :
    ∃ e : OpenPartialHomeomorph M (ℝ × ℝ), q ∈ e.source ∧
      EqOn (fun x => helicoidBaseCoordinates (X x)) e e.source ∧
      ContDiffAt ℝ (∞ : WithTop ℕ∞) (X ∘ e.symm) (helicoidBaseCoordinates (X q)) := by
  have hc : (X ∘ c.symm) (c q) = X q := by rw [Function.comp_apply,c.left_inv hq]
  obtain ⟨f,hf,hfmap,hfinv⟩ := thin_curves_surface_projection_local_diffeomorph hX
    (by rwa [hc]) hD hε0 hε hA hsmall (by rwa [hc])
  rw [hc] at hfinv
  have hval : f (c q) = helicoidBaseCoordinates (X q) := by
    rw [hfmap]
    exact congrArg helicoidBaseCoordinates hc
  have hback : f.symm (helicoidBaseCoordinates (X q)) = c q := by
    rw [← hval]
    exact f.left_inv hf
  refine ⟨c.trans f,⟨hq,hf⟩,?_,?_⟩
  · intro x hx
    change helicoidBaseCoordinates (X x) = f (c x)
    rw [hfmap]
    change helicoidBaseCoordinates (X x) = helicoidBaseCoordinates (X (c.symm (c x)))
    rw [c.left_inv hx.1]
  · change ContDiffAt ℝ (∞ : WithTop ℕ∞) ((X ∘ c.symm) ∘ f.symm)
      (helicoidBaseCoordinates (X q))
    apply ContDiffAt.comp _ _ hfinv
    simpa only [hback] using hX

/-- Actual surface charts and controlled tangent curves derive local
invertibility on the whole chosen end region. -/
theorem thin_charts_projection_isLocalHomeomorphOn {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} {S : Set M}
    (c : M → OpenPartialHomeomorph M (ℝ × ℝ))
    (hmem : ∀ q ∈ S, q ∈ (c q).source)
    (hX : ∀ q ∈ S, ContDiffAt ℝ (∞ : WithTop ℕ∞) (X ∘ (c q).symm) (c q q))
    (hTube : ∀ q ∈ S, X q ∈ helicoidTubeEquiv.target)
    (hD : ∀ q ∈ S, Function.Injective (fderiv ℝ (X ∘ (c q).symm) (c q q)))
    {ε A : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1/2) (hA : 0 ≤ A)
    (hsmall : (3+A/2)*sqrt ε < 1)
    (hcurves : ∀ q ∈ S, HasControlledUnitTangentCurves (X q)
      (fderiv ℝ (X ∘ (c q).symm) (c q q)) ε A) :
    IsLocalHomeomorphOn (fun q => helicoidBaseCoordinates (X q)) S := by
  apply IsLocalHomeomorphOn.mk
  intro q hq
  obtain ⟨e,he,heq,_hs⟩ := thin_chart_projection_local_inverse (c q) (hmem q hq)
    (hX q hq) (hTube q hq) (hD q hq) hε0 hε hA hsmall (hcurves q hq)
  exact ⟨e,he,heq⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thin_charts_projection_isLocalHomeomorphOn
