import TwoAxisHelicoid.ThinCurveProjection

namespace TwoAxisHelicoid
open Real Set
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

theorem controlled_tangent_curve_unit_normal_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : HelicoidTubeCoordinates} {D : E →L[ℝ] HelicoidTubeCoordinates}
    {ε A : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1/2) (hA : 0 ≤ A)
    (hcurves : HasControlledUnitTangentCurves y D ε A)
    (v : E) (hv : (∑ i, (tubeCartesian (D v) i)^2) = 1) :
    |∑ i, helicoidNormalField y i*tubeCartesian (D v) i| ≤ (3+A/2)*sqrt ε := by
  obtain ⟨x,w,a,hx0,hw0,hx,hw,htube,hheight,hspeed,hacc⟩ := hcurves v hv
  have h := helicoid_distance_thin_curve_sqrt_bound hε0 hε hA hx hw htube hheight hspeed hacc
  simpa only [helicoidDistanceVelocity,hx0,hw0] using h

/-- The controlled-curve Taylor estimate controls every tangent direction,
not only possible vectors in the kernel of the projection. -/
theorem controlled_tangent_curves_normal_angle_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : HelicoidTubeCoordinates} {D : E →L[ℝ] HelicoidTubeCoordinates}
    {ε A : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1/2) (hA : 0 ≤ A)
    (hcurves : HasControlledUnitTangentCurves y D ε A) (v : E) :
    (∑ i, helicoidNormalField y i*tubeCartesian (D v) i)^2 ≤
      ((3+A/2)*sqrt ε)^2*(∑ i, (tubeCartesian (D v) i)^2) := by
  let S := ∑ i, (tubeCartesian (D v) i)^2
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  by_cases hS : S = 0
  · have hz : ∀ i, tubeCartesian (D v) i = 0 := by
      intro i
      have hh := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ Finset.univ) => sq_nonneg (tubeCartesian (D v) j))).mp hS i (Finset.mem_univ i)
      nlinarith
    simp only [hz,mul_zero,Finset.sum_const_zero,zero_pow (by decide : 2 ≠ 0),le_refl]
  · let l := sqrt S
    have hl : 0 < l := sqrt_pos.mpr (lt_of_le_of_ne hS0 (Ne.symm hS))
    have hlsq : l^2 = S := sq_sqrt hS0
    have hunit : (∑ i, (tubeCartesian (D (l⁻¹ • v)) i)^2) = 1 := by
      simp only [map_smul,tubeCartesian_smul,Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
      change (l⁻¹)^2*S = 1
      rw [← hlsq]
      field_simp
    have hbound := controlled_tangent_curve_unit_normal_bound hε0 hε hA hcurves (l⁻¹ • v) hunit
    have hscale : (∑ i, helicoidNormalField y i*tubeCartesian (D (l⁻¹ • v)) i) =
        l⁻¹*(∑ i, helicoidNormalField y i*tubeCartesian (D v) i) := by
      simp only [map_smul,tubeCartesian_smul,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hscale,abs_mul,abs_inv,abs_of_pos hl] at hbound
    have hm := mul_le_mul_of_nonneg_left hbound hl.le
    simp only [← mul_assoc,mul_inv_cancel₀ hl.ne',one_mul] at hm
    have hκ : 0 ≤ (3+A/2)*sqrt ε := by positivity
    have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hl.le hκ)).mpr
      (by simpa only [mul_assoc] using hm)
    rw [sq_abs,mul_pow,hlsq] at hsq
    simpa only [mul_comm] using hsq

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.controlled_tangent_curves_normal_angle_bound
