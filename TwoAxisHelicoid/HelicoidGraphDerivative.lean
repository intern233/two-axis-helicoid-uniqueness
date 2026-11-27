import TwoAxisHelicoid.HelicoidGraphGradientBound
import TwoAxisHelicoid.ThinCurveAngle

namespace TwoAxisHelicoid
open Real Set
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

noncomputable def helicoidGraphMap (u : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) :
    HelicoidTubeCoordinates := helicoidTubeMap ((u q,q.1),q.2)

theorem helicoidGraphMap_differentiableAt {u : (ℝ × ℝ) → ℝ} {q : ℝ × ℝ}
    (hu : DifferentiableAt ℝ u q) : DifferentiableAt ℝ (helicoidGraphMap u) q :=
  (helicoidTubeMap_contDiff.differentiable (by simp)).differentiableAt.comp q
    ((hu.prodMk differentiableAt_fst).prodMk differentiableAt_snd)

/-- The actual derivative of a normal graph in the helicoid frame. -/
theorem helicoidGraphMap_fderiv {u : (ℝ × ℝ) → ℝ} {q : ℝ × ℝ}
    (hu : DifferentiableAt ℝ u q) (a b : ℝ) :
    tubeCartesian (fderiv ℝ (helicoidGraphMap u) q (a,b)) =
      fun i => a*helicoidTubeR q.1 q.2 (u q) i+
        b*helicoidTubeTheta q.1 q.2 (u q) i+
        (fderiv ℝ u q (a,b))*standardHelicoidNormal q.1 q.2 i := by
  let z : ℝ → ℝ × ℝ := fun t => (q.1+t*a,q.2+t*b)
  have hr : HasDerivAt (fun t : ℝ => q.1+t*a) a 0 := by
    simpa only [zero_add,one_mul,Pi.add_apply,id_eq] using!
      (hasDerivAt_const (0 : ℝ) q.1).add ((hasDerivAt_id (0 : ℝ)).mul_const a)
  have ht : HasDerivAt (fun t : ℝ => q.2+t*b) b 0 := by
    simpa only [zero_add,one_mul,Pi.add_apply,id_eq] using!
      (hasDerivAt_const (0 : ℝ) q.2).add ((hasDerivAt_id (0 : ℝ)).mul_const b)
  have hz : HasDerivAt z (a,b) 0 := hr.prodMk ht
  have hz0 : z 0 = q := by simp [z]
  have hs : HasDerivAt (u ∘ z) (fderiv ℝ u q (a,b)) 0 := by
    apply HasFDerivAt.comp_hasDerivAt 0 _ hz
    simpa only [hz0] using hu.hasFDerivAt
  have hg : HasDerivAt ((helicoidGraphMap u) ∘ z)
      (fderiv ℝ (helicoidGraphMap u) q (a,b)) 0 := by
    apply HasFDerivAt.comp_hasDerivAt 0 _ hz
    simpa only [hz0] using (helicoidGraphMap_differentiableAt hu).hasFDerivAt
  have hframe := helicoidTube_curve_hasDerivAt hr ht hs
  have hcart := tubeCartesian_hasDerivAt hg
  have hh := hcart.unique hframe
  simpa only [Function.comp_apply,hz0,zero_mul,add_zero] using hh

theorem helicoidNormalField_graph {u : (ℝ × ℝ) → ℝ} {q : ℝ × ℝ}
    (hu : |u q| < 1) : helicoidNormalField (helicoidGraphMap u q) =
      standardHelicoidNormal q.1 q.2 := by
  have h : ((u q,q.1),q.2) ∈ helicoidTubeEquiv.source := hu
  have he := helicoidTubeEquiv.left_inv h
  change standardHelicoidNormal
    (helicoidTubeEquiv.symm (helicoidTubeEquiv ((u q,q.1),q.2))).1.2
    (helicoidTubeEquiv.symm (helicoidTubeEquiv ((u q,q.1),q.2))).2 = _
  rw [he]

noncomputable def helicoidGraphGradientNorm (u : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) : ℝ :=
  sqrt ((fderiv ℝ u q (1,0))^2+(fderiv ℝ u q (0,1))^2/(helicoidQ q.1)^2)

/-- A bound on the actual tangent planes yields a bound on the actual
height derivative in the induced metric of the base helicoid. -/
theorem helicoidGraphGradientNorm_le_of_angle {u : (ℝ × ℝ) → ℝ} {q : ℝ × ℝ}
    (hu : DifferentiableAt ℝ u q) (hs : |u q| ≤ 1/2)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1/2)
    (hangle : ∀ v : ℝ × ℝ,
      (∑ i, helicoidNormalField (helicoidGraphMap u q) i*
        tubeCartesian (fderiv ℝ (helicoidGraphMap u) q v) i)^2 ≤
      κ^2*(∑ i, (tubeCartesian (fderiv ℝ (helicoidGraphMap u) q v) i)^2)) :
    helicoidGraphGradientNorm u q ≤ 2*κ := by
  have hnorm : |κ| ≤ 1/2 := by rwa [abs_of_nonneg hκ0]
  have hS := helicoid_height_gradient_sq_bound (fderiv ℝ u q) q.1 κ (by
    intro a b
    have h := hangle (a,b)
    rw [helicoidGraphMap_fderiv hu,helicoidNormalField_graph (hs.trans_lt (by norm_num)),
      helicoidTube_vector_dot_normal,helicoidTube_vector_metric] at h
    exact helicoid_graph_height_linear_bound hs hnorm a b _ h)
  have hnonneg : 0 ≤ (fderiv ℝ u q (1,0))^2+
      (fderiv ℝ u q (0,1))^2/(helicoidQ q.1)^2 := by positivity
  have he := sq_sqrt hnonneg
  have hpos := sqrt_nonneg ((fderiv ℝ u q (1,0))^2+
      (fderiv ℝ u q (0,1))^2/(helicoidQ q.1)^2)
  dsimp [helicoidGraphGradientNorm]
  nlinarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidGraphGradientNorm_le_of_angle
