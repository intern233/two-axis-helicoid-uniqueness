import TwoAxisHelicoid.PlaneOrientationJacobian

namespace TwoAxisHelicoid
open Complex Filter Set Topology Metric
open scoped Topology ComplexConjugate

/-- When one of the two real-linear complex components strictly dominates
the other, the true differentiable map has the degree of its dominant
component. The differentiability estimate is uniform over the small circle. -/
theorem plane_orientation_of_dominant_derivative {f : ℂ → ℂ} {p : ℂ} {L : ℂ →L[ℝ] ℂ}
    (hf : HasFDerivAt f L p) (hcont : ∀ᶠ q in 𝓝 p, ContinuousAt f q)
    (A B : ℂ) (hdom : ‖B‖ < ‖A‖) (v w : OrientationCircle → ℂ) (hv : Continuous v)
    (hv' : ∀ a, ‖v a‖ = 1) (hw' : ∀ a, ‖w a‖ = 1)
    (hL : ∀ (r : ℝ) (a : OrientationCircle), L (r • orientationRay a) = (A*r)*v a+(B*r)*w a)
    {d : ℤ} (hdeg : ∀ c : ℂ, c ≠ 0 → HasOrientationCircleDegree (fun a => planeOrientationDirection (c*v a)) d) :
    HasPlaneOrientationAt f p d := by
  let η := (‖A‖-‖B‖)/2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨R,hR,hU⟩ := Metric.mem_nhds_iff.mp ((hf.isLittleO.def hη).and hcont)
  refine ⟨R,hR,fun r hr => ?_⟩
  let T := fun a => p+r • orientationRay a
  have hT : Continuous T := (continuous_const (y := p)).add ((continuous_const (y := r)).smul orientationRay_continuous)
  have ht (a : OrientationCircle) : T a ∈ ball p R := orientation_probe_point_mem_ball hr a
  have hfc : Continuous (fun a => f (T a)-f p) := ((continuous_iff_continuousAt.mpr
    (fun a => (hU (ht a)).2.comp hT.continuousAt))).sub continuous_const
  have hA : A ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hdom)
  apply circle_degree_small_perturbation hfc (continuous_const.mul hv) (hdeg (A*r) (mul_ne_zero hA (ofReal_ne_zero.mpr hr.1.ne')))
  intro a
  let z := r • orientationRay a
  have hz : ‖z‖ = r := by rw [norm_smul,Real.norm_of_nonneg hr.1.le,orientationRay_norm,mul_one]
  have hrem : ‖f (T a)-f p-L z‖ ≤ η*r := by
    have h := (hU (ht a)).1
    change ‖f (p+z)-f p-L (p+z-p)‖ ≤ η*‖p+z-p‖ at h
    simpa only [add_sub_cancel_left,hz] using h
  have he : f (T a)-f p-(A*r)*v a = (f (T a)-f p-L z)+(B*r)*w a := by
    rw [show L z = (A*r)*v a+(B*r)*w a from hL r a]
    ring
  have hsmall : η*r+‖B‖*r < ‖A‖*r :=
    (by have h' : η+‖B‖ < ‖A‖ := by dsimp [η]; linarith
        simpa only [add_mul] using mul_lt_mul_of_pos_right h' hr.1)
  change ‖f (T a)-f p-(A*r)*v a‖ < ‖(A*r)*v a‖
  rw [he]
  apply (norm_add_le _ _).trans_lt
  simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg hr.1.le,hw',hv',mul_one]
  exact (add_le_add hrem (le_refl _)).trans_lt hsmall

theorem hasFDerivAt_positive_local_orientation {f : ℂ → ℂ} {p : ℂ} {L : ℂ →L[ℝ] ℂ}
    (hf : HasFDerivAt f L p) (hcont : ∀ᶠ q in 𝓝 p, ContinuousAt f q) (hd : 0 < planeRealJacobian L) :
    HasPlaneOrientationAt f p 1 := by
  have hn := realLinear_orientation_norms L
  have hdom : ‖realLinearOpposite L‖ < ‖realLinearDirect L‖ := by
    nlinarith [norm_nonneg (realLinearDirect L),norm_nonneg (realLinearOpposite L)]
  apply plane_orientation_of_dominant_derivative hf hcont _ _ hdom orientationRay (conj ∘ orientationRay)
    orientationRay_continuous orientationRay_norm (fun a => by simp) _ (fun _ => orientationCircle_scaled_ray_degree)
  intro r a
  rw [realLinear_direct_opposite L]
  simp only [real_smul,Function.comp_apply,map_mul,conj_ofReal]
  ring

theorem hasFDerivAt_negative_local_orientation {f : ℂ → ℂ} {p : ℂ} {L : ℂ →L[ℝ] ℂ}
    (hf : HasFDerivAt f L p) (hcont : ∀ᶠ q in 𝓝 p, ContinuousAt f q) (hd : planeRealJacobian L < 0) :
    HasPlaneOrientationAt f p (-1) := by
  have hn := realLinear_orientation_norms L
  have hdom : ‖realLinearDirect L‖ < ‖realLinearOpposite L‖ := by
    nlinarith [norm_nonneg (realLinearDirect L),norm_nonneg (realLinearOpposite L)]
  apply plane_orientation_of_dominant_derivative hf hcont _ _ hdom (conj ∘ orientationRay) orientationRay
    (continuous_conj.comp orientationRay_continuous) (fun a => by simp) orientationRay_norm _
    (fun _ => orientationCircle_scaled_conj_ray_degree)
  intro r a
  rw [realLinear_direct_opposite L]
  simp only [real_smul,Function.comp_apply,map_mul,conj_ofReal]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.hasFDerivAt_positive_local_orientation
#print axioms TwoAxisHelicoid.hasFDerivAt_negative_local_orientation
