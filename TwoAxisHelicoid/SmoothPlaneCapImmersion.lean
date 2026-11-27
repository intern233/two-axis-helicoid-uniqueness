import TwoAxisHelicoid.PlaneCapScalarDerivative

namespace TwoAxisHelicoid
open Real Set
set_option maxHeartbeats 1000000

noncomputable def planeSquaredRadiusDerivative (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (2*p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ+(2*p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem planeSquaredRadius_hasFDerivAt (p : ℝ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => q.1^2+q.2^2) (planeSquaredRadiusDerivative p) p := by
  have hx : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hz : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  simpa [planeSquaredRadiusDerivative] using! (hx.pow 2).add (hz.pow 2)

noncomputable def smoothPlaneCapDerivative (A H : ℝ) (p : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] HelicoidTubeCoordinates :=
  let q := p.1^2+p.2^2
  let D := planeSquaredRadiusDerivative p
  let a := planeCapScale A H q
  let da := deriv (planeCapScale A H) q
  let db := deriv (planeCapHeight A H) q
  (((p.1*da) • D+a • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (db • D)).prod
    ((p.2*da) • D+a • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem smoothPlaneCap_hasFDerivAt (A H : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (smoothPlaneCap A H) (smoothPlaneCapDerivative A H p) p := by
  have hq0 : 0 ≤ p.1^2+p.2^2 := by positivity
  have hx : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hz : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have ha := (planeCapScale_hasDerivAt (A := A) (H := H) hq0).differentiableAt.hasDerivAt.hasFDerivAt.comp
    p (planeSquaredRadius_hasFDerivAt p)
  have hb := (planeCapHeight_hasDerivAt (A := A) (H := H) hq0).differentiableAt.hasDerivAt.hasFDerivAt.comp
    p (planeSquaredRadius_hasFDerivAt p)
  convert! ((ha.mul hx).prodMk hb).prodMk (ha.mul hz) using 1
  ext <;> simp [smoothPlaneCapDerivative,mul_assoc,mul_comm,add_comm]

theorem smoothPlaneCapDerivative_injective {A H : ℝ} (hA : 0 ≤ A) (hH : 0 < H) (p : ℝ × ℝ) :
    Function.Injective (smoothPlaneCapDerivative A H p) := by
  suffices hker : ∀ v, smoothPlaneCapDerivative A H p v = 0 → v = 0 by
    intro v w hvw
    apply sub_eq_zero.mp
    apply hker (v-w)
    rw [map_sub,hvw,sub_self]
  intro v hv
  let q := p.1^2+p.2^2
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hx := congrArg (fun y : HelicoidTubeCoordinates => y.1.1) hv
  have hy := congrArg (fun y : HelicoidTubeCoordinates => y.1.2) hv
  have hz := congrArg (fun y : HelicoidTubeCoordinates => y.2) hv
  change (p.1*deriv (planeCapScale A H) q)*planeSquaredRadiusDerivative p v+
    planeCapScale A H q*v.1 = 0 at hx
  change deriv (planeCapHeight A H) q*planeSquaredRadiusDerivative p v = 0 at hy
  change (p.2*deriv (planeCapScale A H) q)*planeSquaredRadiusDerivative p v+
    planeCapScale A H q*v.2 = 0 at hz
  by_cases hq : q ≤ A
  · rw [planeCapScale_deriv_zero hq0 hq,planeCapScale_of_le hq] at hx hz
    simpa using Prod.ext (by simpa using hx : v.1 = 0) (by simpa using hz : v.2 = 0)
  · have hb := (planeCapHeight_deriv_pos hA hH (lt_of_not_ge hq)).ne'
    have hD : planeSquaredRadiusDerivative p v = 0 := (mul_eq_zero.mp hy).resolve_left hb
    have ha := (planeCapScale_pos (A := A) hH hq0).ne'
    rw [hD,mul_zero,zero_add] at hx hz
    exact Prod.ext ((mul_eq_zero.mp hx).resolve_left ha) ((mul_eq_zero.mp hz).resolve_left ha)

/-- The explicit smooth cap has no singular point, including the flat
joining circle and the annulus where its radial coordinate turns back. -/
theorem smoothPlaneCap_fderiv_injective {A H : ℝ} (hA : 0 ≤ A) (hH : 0 < H) (p : ℝ × ℝ) :
    Function.Injective (fderiv ℝ (smoothPlaneCap A H) p) := by
  rw [(smoothPlaneCap_hasFDerivAt A H p).fderiv]
  exact smoothPlaneCapDerivative_injective hA hH p

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.smoothPlaneCap_fderiv_injective
