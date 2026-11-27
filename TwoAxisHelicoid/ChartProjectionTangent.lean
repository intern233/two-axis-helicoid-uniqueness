import TwoAxisHelicoid.ChartThinProjection
import TwoAxisHelicoid.ThinCurveAngle

namespace TwoAxisHelicoid
open Real Set
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

/-- The local spatial inverse has its actual derivative in the original
tangent plane. Thus the angle estimate is preserved by this change of
surface coordinates. -/
theorem chart_projection_local_inverse_angle {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} {q : M}
    (c : OpenPartialHomeomorph M (ℝ × ℝ)) (hq : q ∈ c.source)
    (hX : ContDiffAt ℝ (∞ : WithTop ℕ∞) (X ∘ c.symm) (c q))
    (hTube : X q ∈ helicoidTubeEquiv.target)
    (hD : Function.Injective (fderiv ℝ (X ∘ c.symm) (c q)))
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ < 1)
    (hangle : ∀ v : ℝ × ℝ,
      (∑ i, helicoidNormalField (X q) i*tubeCartesian (fderiv ℝ (X ∘ c.symm) (c q) v) i)^2 ≤
        κ^2*(∑ i, (tubeCartesian (fderiv ℝ (X ∘ c.symm) (c q) v) i)^2)) :
    ∃ e : OpenPartialHomeomorph M (ℝ × ℝ), q ∈ e.source ∧
      EqOn (fun x => helicoidBaseCoordinates (X x)) e e.source ∧
      ContDiffAt ℝ (∞ : WithTop ℕ∞) (X ∘ e.symm) (helicoidBaseCoordinates (X q)) ∧
      ∀ v : ℝ × ℝ,
        (∑ i, helicoidNormalField (X q) i*
          tubeCartesian (fderiv ℝ (X ∘ e.symm) (helicoidBaseCoordinates (X q)) v) i)^2 ≤
        κ^2*(∑ i, (tubeCartesian
          (fderiv ℝ (X ∘ e.symm) (helicoidBaseCoordinates (X q)) v) i)^2) := by
  have hc : (X ∘ c.symm) (c q) = X q := by rw [Function.comp_apply,c.left_inv hq]
  obtain ⟨f,hf,hfmap,hfinv⟩ := helicoid_surface_projection_local_diffeomorph hX
    (by rwa [hc]) hD hκ0 hκ (by rwa [hc])
  rw [hc] at hfinv
  have hval : f (c q) = helicoidBaseCoordinates (X q) := by
    rw [hfmap]
    exact congrArg helicoidBaseCoordinates hc
  have hback : f.symm (helicoidBaseCoordinates (X q)) = c q := by
    rw [← hval]
    exact f.left_inv hf
  have hXd : DifferentiableAt ℝ (X ∘ c.symm) (f.symm (helicoidBaseCoordinates (X q))) := by
    rw [hback]
    exact hX.differentiableAt (by simp)
  refine ⟨c.trans f,⟨hq,hf⟩,?_,?_,?_⟩
  · intro x hx
    change helicoidBaseCoordinates (X x) = f (c x)
    rw [hfmap]
    change helicoidBaseCoordinates (X x) = helicoidBaseCoordinates (X (c.symm (c x)))
    rw [c.left_inv hx.1]
  · change ContDiffAt ℝ (∞ : WithTop ℕ∞) ((X ∘ c.symm) ∘ f.symm)
      (helicoidBaseCoordinates (X q))
    apply ContDiffAt.comp _ _ hfinv
    simpa only [hback] using hX
  · intro v
    change (∑ i, helicoidNormalField (X q) i*tubeCartesian
      (fderiv ℝ ((X ∘ c.symm) ∘ f.symm) (helicoidBaseCoordinates (X q)) v) i)^2 ≤
      κ^2*(∑ i, (tubeCartesian
        (fderiv ℝ ((X ∘ c.symm) ∘ f.symm) (helicoidBaseCoordinates (X q)) v) i)^2)
    rw [fderiv_comp _ hXd (hfinv.differentiableAt (by simp)),hback,
      ContinuousLinearMap.comp_apply]
    exact hangle _

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.chart_projection_local_inverse_angle
