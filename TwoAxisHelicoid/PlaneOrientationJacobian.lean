import TwoAxisHelicoid.PlaneOrientationLocalConstancy
import TwoAxisHelicoid.IsothermalComplexAtlas

namespace TwoAxisHelicoid
open Complex Filter Set Topology
open scoped Topology ComplexConjugate

theorem orientationRay_add (a b : OrientationCircle) :
    orientationRay (a+b) = orientationRay a * orientationRay b := by
  simp only [orientationRay,orientationCircleHomeomorph,AddCircle.homeomorphCircle_apply,AddCircle.toCircle_add,
    Circle.coe_mul]

theorem planeOrientationDirection_mul_ray {z : ℂ} (hz : z ≠ 0) (a : OrientationCircle) :
    planeOrientationDirection (z*orientationRay a) = planeOrientationDirection z + a := by
  have he : z*orientationRay a = ‖z‖ • orientationRay (planeOrientationDirection z+a) := by
    rw [orientationRay_add,← smul_mul_assoc,planeOrientationDirection_reconstruct hz]
  rw [he,planeOrientationDirection_scaled_ray (norm_pos_iff.mpr hz)]

theorem orientationCircle_degree_addLeft (c : OrientationCircle) :
    HasOrientationCircleDegree (fun x => c+x) 1 := by
  obtain ⟨a,ha⟩ := (Quotient.mk_surjective : Function.Surjective ((↑) : ℝ → OrientationCircle)) c
  have h : (a : OrientationCircle)=c := ha
  subst c
  exact ⟨fun x => a+x,continuous_const.add continuous_id,
    fun x => AddCircle.coe_add 1 a x,fun x => by push_cast; ring⟩

/-- Straight-line perturbations of a nonzero loop preserve its signed
degree if their pointwise norm is less than that of the reference loop. -/
theorem circle_degree_small_perturbation {v D : OrientationCircle → ℂ} (hv : Continuous v) (hD : Continuous D)
    {n : ℤ} (hdeg : HasOrientationCircleDegree (fun a => planeOrientationDirection (D a)) n)
    (hclose : ∀ a, ‖v a-D a‖ < ‖D a‖) :
    HasOrientationCircleDegree (fun a => planeOrientationDirection (v a)) n := by
  let Z := fun x : ℝ × OrientationCircle => D x.2+orientationBlend x.1 • (v x.2-D x.2)
  have hZ : Continuous Z := (hD.comp continuous_snd).add
    ((orientationBlend_continuous.comp continuous_fst).smul ((hv.comp continuous_snd).sub (hD.comp continuous_snd)))
  have hn (x : ℝ × OrientationCircle) : Z x ≠ 0 := by
    intro hh
    have he := congrArg norm (eq_neg_of_add_eq_zero_left hh)
    have hbound := ((mul_le_mul_of_nonneg_right (orientationBlend_mem x.1).2 (norm_nonneg (v x.2-D x.2))).trans_eq
      (one_mul _)).trans_lt (hclose x.2)
    simp only [norm_neg,norm_smul,Real.norm_of_nonneg (orientationBlend_mem x.1).1] at he
    exact hbound.ne he.symm
  let K := fun x : ℝ × OrientationCircle => planeOrientationDirection (Z x)
  have hK : Continuous K := continuous_iff_continuousAt.mpr (fun x => (planeOrientationDirection_continuousAt (hn x)).comp hZ.continuousAt)
  have h0 : HasOrientationCircleDegree (fun a => K (0,a)) n := by simpa only [K,Z,orientationBlend_zero,zero_smul,add_zero] using hdeg
  simpa only [K,Z,orientationBlend_one,one_smul,add_sub_cancel] using h0.family (t := 1) hK

theorem orientationCircle_scaled_ray_degree {c : ℂ} (hc : c ≠ 0) :
    HasOrientationCircleDegree (fun a => planeOrientationDirection (c*orientationRay a)) 1 := by
  simpa only [planeOrientationDirection_mul_ray hc] using orientationCircle_degree_addLeft (planeOrientationDirection c)

theorem orientationCircle_scaled_conj_ray_degree {c : ℂ} (hc : c ≠ 0) :
    HasOrientationCircleDegree (fun a => planeOrientationDirection (c*conj (orientationRay a))) (-1) := by
  simpa only [← orientationRay_neg,Function.comp_def,one_mul] using
    (orientationCircle_scaled_ray_degree hc).comp orientationCircle_degree_neg

noncomputable def realLinearDirect (L : ℂ →L[ℝ] ℂ) : ℂ := (L 1-I*L I)/2
noncomputable def realLinearOpposite (L : ℂ →L[ℝ] ℂ) : ℂ := (L 1+I*L I)/2

theorem realLinear_direct_opposite (L : ℂ →L[ℝ] ℂ) (z : ℂ) :
    L z = realLinearDirect L*z+realLinearOpposite L*conj z := by
  rw [real_linear_complex_expansion L z]
  apply Complex.ext <;> simp [realLinearDirect,realLinearOpposite,Complex.mul_re,Complex.mul_im] <;> ring

theorem realLinear_orientation_norms (L : ℂ →L[ℝ] ℂ) :
    ‖realLinearDirect L‖^2-‖realLinearOpposite L‖^2 = planeRealJacobian L := by
  rw [Complex.sq_norm,Complex.sq_norm]
  simp [realLinearDirect,realLinearOpposite,Complex.normSq_apply,planeRealJacobian,Complex.mul_re,Complex.mul_im]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.circle_degree_small_perturbation
#print axioms TwoAxisHelicoid.realLinear_orientation_norms
