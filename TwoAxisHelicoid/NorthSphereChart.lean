import TwoAxisHelicoid.PlaneCapSphericalTail
import TwoAxisHelicoid.EmbeddedParametrizationChart

namespace TwoAxisHelicoid
open Real Set
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

noncomputable def northSphereParam (H : ℝ) (p : ℝ × ℝ) : HelicoidTubeCoordinates :=
  let q := p.1^2+p.2^2
  ((H/(1+q)*p.1,H/(1+q)),H/(1+q)*p.2)

noncomputable def northSphereProjection (y : HelicoidTubeCoordinates) : ℝ × ℝ :=
  (y.1.1/y.1.2,y.2/y.1.2)

theorem northSphereParam_contDiff (H : ℝ) : ContDiff ℝ ∞ (northSphereParam H) := by
  have hd : ∀ p : ℝ × ℝ, 1+(p.1^2+p.2^2) ≠ 0 := fun p => by positivity
  change ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
    ((H/(1+(p.1^2+p.2^2))*p.1,H/(1+(p.1^2+p.2^2))),H/(1+(p.1^2+p.2^2))*p.2))
  fun_prop

theorem northSphereProjection_contDiffAt {y : HelicoidTubeCoordinates} (hy : y.1.2 ≠ 0) :
    ContDiffAt ℝ ∞ northSphereProjection y := by
  unfold northSphereProjection
  fun_prop

theorem northSphereParam_north (H : ℝ) : northSphereParam H 0 = planeCapNorth H := by
  simp [northSphereParam,planeCapNorth]

theorem northSphereParam_mem_sphere (H : ℝ) (p : ℝ × ℝ) :
    northSphereParam H p ∈ planeCapSphere H := by
  have hd : 1+(p.1^2+p.2^2) ≠ 0 := by positivity
  dsimp [northSphereParam,planeCapSphere]
  field_simp
  ring

theorem northSphereProjection_param {H : ℝ} (hH : 0 < H) (p : ℝ × ℝ) :
    northSphereProjection (northSphereParam H p) = p := by
  have hd : 1+(p.1^2+p.2^2) ≠ 0 := by positivity
  dsimp [northSphereProjection,northSphereParam]
  apply Prod.ext <;> field_simp

theorem northSphereParam_projection {H : ℝ} {y : HelicoidTubeCoordinates}
    (hy : y ∈ planeCapSphere H) (hyp : 0 < y.1.2) :
    northSphereParam H (northSphereProjection y) = y := by
  have hden : y.1.2 ≠ 0 := hyp.ne'
  have hs : y.1.1^2+y.2^2 = y.1.2*(H-y.1.2) := by
    dsimp [planeCapSphere] at hy
    nlinarith
  have hH : H ≠ 0 := by
    intro h
    rw [h] at hs
    nlinarith [sq_nonneg y.1.1,sq_nonneg y.2]
  have hq : (y.1.1/y.1.2)^2+(y.2/y.1.2)^2 = (H-y.1.2)/y.1.2 := by
    field_simp
    nlinarith [hs]
  have he : 1+(H-y.1.2)/y.1.2 = H/y.1.2 := by field_simp; ring
  dsimp [northSphereParam,northSphereProjection]
  rw [hq,he]
  apply Prod.ext
  · apply Prod.ext <;> field_simp
  · field_simp

theorem northSphereParam_fderiv_injective {H : ℝ} (hH : 0 < H) (p : ℝ × ℝ) :
    Function.Injective (fderiv ℝ (northSphereParam H) p) := by
  have hc := (northSphereParam_contDiff H).differentiable (by simp) p
  have hn : (northSphereParam H p).1.2 ≠ 0 := by
    dsimp [northSphereParam]
    positivity
  have hp := (northSphereProjection_contDiffAt hn).differentiableAt (by simp)
  have hd := fderiv_comp p hp hc
  have he : northSphereProjection ∘ northSphereParam H = id :=
    funext (northSphereProjection_param hH)
  rw [he,fderiv_id] at hd
  intro v w hvw
  have h := congrArg (fderiv ℝ northSphereProjection (northSphereParam H p)) hvw
  change ((fderiv ℝ northSphereProjection (northSphereParam H p)).comp
    (fderiv ℝ (northSphereParam H) p)) v =
    ((fderiv ℝ northSphereProjection (northSphereParam H p)).comp
      (fderiv ℝ (northSphereParam H) p)) w at h
  rw [← hd] at h
  exact h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.northSphereParam_fderiv_injective

