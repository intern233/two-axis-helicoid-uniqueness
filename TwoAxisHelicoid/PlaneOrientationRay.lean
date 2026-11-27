import TwoAxisHelicoid.PlaneOrientationCircleHomotopy

namespace TwoAxisHelicoid
open Complex Filter Set Topology
open scoped Topology ComplexConjugate

noncomputable def orientationCircleHomeomorph : OrientationCircle ≃ₜ Circle :=
  AddCircle.homeomorphCircle (one_ne_zero : (1:ℝ) ≠ 0)

noncomputable def orientationRay (a : OrientationCircle) : ℂ := (orientationCircleHomeomorph a : Circle)

theorem orientationRay_continuous : Continuous orientationRay :=
  continuous_subtype_val.comp orientationCircleHomeomorph.continuous

@[simp] theorem orientationRay_norm (a : OrientationCircle) : ‖orientationRay a‖ = 1 := Circle.norm_coe _

theorem orientationRay_ne_zero (a : OrientationCircle) : orientationRay a ≠ 0 := (orientationCircleHomeomorph a).coe_ne_zero

theorem orientationRay_neg (a : OrientationCircle) : orientationRay (-a) = conj (orientationRay a) := by
  simp only [orientationRay,orientationCircleHomeomorph,AddCircle.homeomorphCircle_apply,AddCircle.toCircle_neg,
    Circle.coe_inv_eq_conj]

noncomputable def orientationCircleUnit (z : ℂ) : Circle := by
  classical
  exact if hz : z = 0 then 1 else ⟨(‖z‖⁻¹ : ℝ) • z,by
    change dist _ 0 = 1
    rw [dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩

theorem orientationCircleUnit_coe {z : ℂ} (hz : z ≠ 0) :
    (orientationCircleUnit z : ℂ) = (‖z‖⁻¹ : ℝ) • z := by
  classical
  simp [orientationCircleUnit,hz]

theorem orientationCircleUnit_continuousAt {z : ℂ} (hz : z ≠ 0) : ContinuousAt orientationCircleUnit z := by
  apply IsInducing.subtypeVal.continuousAt_iff.mpr
  have hreg : ContinuousAt (fun w : ℂ => (‖w‖⁻¹ : ℝ) • w) z :=
    (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hz)).smul continuousAt_id
  apply hreg.congr_of_eventuallyEq
  filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
  exact orientationCircleUnit_coe hw

noncomputable def planeOrientationDirection (z : ℂ) : OrientationCircle :=
  orientationCircleHomeomorph.symm (orientationCircleUnit z)

theorem planeOrientationDirection_continuousAt {z : ℂ} (hz : z ≠ 0) : ContinuousAt planeOrientationDirection z :=
  orientationCircleHomeomorph.symm.continuous.continuousAt.comp (orientationCircleUnit_continuousAt hz)

theorem orientationRay_direction {z : ℂ} (hz : z ≠ 0) :
    orientationRay (planeOrientationDirection z) = (‖z‖⁻¹ : ℝ) • z := by
  change ((orientationCircleHomeomorph (orientationCircleHomeomorph.symm _)):ℂ) = _
  rw [orientationCircleHomeomorph.apply_symm_apply,orientationCircleUnit_coe hz]

theorem planeOrientationDirection_scaled_ray {r : ℝ} (hr : 0 < r) (a : OrientationCircle) :
    planeOrientationDirection (r • orientationRay a) = a := by
  apply orientationCircleHomeomorph.injective
  apply Subtype.ext
  change orientationRay (planeOrientationDirection (r • orientationRay a)) = orientationRay a
  rw [orientationRay_direction (smul_ne_zero hr.ne' (orientationRay_ne_zero _)),norm_smul,orientationRay_norm,
    Real.norm_of_nonneg hr.le,mul_one,smul_smul,inv_mul_cancel₀ hr.ne',one_smul]

theorem planeOrientationDirection_reconstruct {z : ℂ} (hz : z ≠ 0) :
    ‖z‖ • orientationRay (planeOrientationDirection z) = z := by
  rw [orientationRay_direction hz,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz),one_smul]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.planeOrientationDirection_scaled_ray
