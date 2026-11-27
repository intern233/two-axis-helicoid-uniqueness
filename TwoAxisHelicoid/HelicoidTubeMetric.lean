import TwoAxisHelicoid.HelicoidNormalGeometry

namespace TwoAxisHelicoid
open Real

theorem sum_sq_three_vectors {ι : Type*} [Fintype ι] (u v w : ι → ℝ) (a b c : ℝ) :
    (∑ i, (a*u i+b*v i+c*w i)^2) =
      a^2*(∑ i, (u i)^2)+b^2*(∑ i, (v i)^2)+c^2*(∑ i, (w i)^2)+
      2*a*b*(∑ i, u i*v i)+2*a*c*(∑ i, u i*w i)+2*b*c*(∑ i, v i*w i) := by
  calc
    _ = ∑ i, (a^2*(u i)^2+b^2*(v i)^2+c^2*(w i)^2+
      (2*a*b)*(u i*v i)+(2*a*c)*(u i*w i)+(2*b*c)*(v i*w i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum]

theorem standardHelicoid_frame_metric (r θ a b c : ℝ) :
    (∑ i, (a*standardHelicoidR θ i+b*standardHelicoidTheta r θ i+
      c*standardHelicoidNormal r θ i)^2) = a^2+(helicoidQ r)^2*b^2+c^2 := by
  rw [sum_sq_three_vectors]
  obtain ⟨hR,hRT,hT⟩ := standardHelicoid_metric r θ
  obtain ⟨hN,hRN,hTN⟩ := standardHelicoid_unit_normal r θ
  rw [hR,hRT,hT,hN,hRN,hTN]
  ring

noncomputable def helicoidTubeR (r θ s : ℝ) : Fin 3 → ℝ :=
  standardHelicoidR θ+(s/(helicoidQ r)^3) • standardHelicoidTheta r θ

noncomputable def helicoidTubeTheta (r θ s : ℝ) : Fin 3 → ℝ :=
  standardHelicoidTheta r θ+(s/helicoidQ r) • standardHelicoidR θ

theorem helicoidTube_vector_metric (r θ s a b c : ℝ) :
    (∑ i, (a*helicoidTubeR r θ s i+b*helicoidTubeTheta r θ s i+
      c*standardHelicoidNormal r θ i)^2) =
      (a+s*b/helicoidQ r)^2+(helicoidQ r)^2*(b+s*a/(helicoidQ r)^3)^2+c^2 := by
  have he : (fun i => a*helicoidTubeR r θ s i+b*helicoidTubeTheta r θ s i+
      c*standardHelicoidNormal r θ i) =
      fun i => (a+s*b/helicoidQ r)*standardHelicoidR θ i+
        (b+s*a/(helicoidQ r)^3)*standardHelicoidTheta r θ i+
        c*standardHelicoidNormal r θ i := by
    funext i
    dsimp [helicoidTubeR,helicoidTubeTheta]
    ring
  simp_rw [congrFun he]
  exact standardHelicoid_frame_metric r θ _ _ c

theorem symmetric_two_coordinate_lower_bound {k : ℝ} (hk : |k| ≤ 1/2) (a b : ℝ) :
    a^2+b^2 ≤ 4*((a+k*b)^2+(b+k*a)^2) := by
  have hab := abs_le.mp hk
  have hp : 0 ≤ (1+k)^2-1/4 := by nlinarith
  have hm : 0 ≤ (1-k)^2-1/4 := by nlinarith
  have h1 := mul_nonneg hp (sq_nonneg (a+b))
  have h2 := mul_nonneg hm (sq_nonneg (a-b))
  nlinarith

/-- The actual differential of the helicoid normal, expressed in the
coordinates of its normal tube, has Euclidean operator norm at most two
throughout the half-width tube. This is the algebraic parallel-surface bound
used by the signed-distance Hessian estimate. -/
theorem helicoid_half_tube_normal_differential_bound {r θ s : ℝ}
    (hs : |s| ≤ 1/2) (a b c : ℝ) :
    (∑ i, (a/(helicoidQ r)^3*standardHelicoidTheta r θ i+
      b/helicoidQ r*standardHelicoidR θ i)^2) ≤
      4*(∑ i, (a*helicoidTubeR r θ s i+b*helicoidTubeTheta r θ s i+
        c*standardHelicoidNormal r θ i)^2) := by
  rw [standardHelicoid_normal_differential_metric,helicoidTube_vector_metric]
  have hq := helicoidQ_pos r
  have hq1 := helicoidQ_ge_one r
  have hq2 : (1 : ℝ) ≤ (helicoidQ r)^2 := one_le_pow₀ hq1
  have hq4 : (1 : ℝ) ≤ (helicoidQ r)^4 := one_le_pow₀ hq1
  have hk : |s/(helicoidQ r)^2| ≤ 1/2 := by
    rw [abs_div,abs_of_pos (pow_pos hq 2)]
    apply (div_le_iff₀ (pow_pos hq 2)).mpr
    linarith
  have h := symmetric_two_coordinate_lower_bound hk a (helicoidQ r*b)
  have h1 : a+(s/(helicoidQ r)^2)*(helicoidQ r*b) = a+s*b/helicoidQ r := by
    field_simp
  have h2 : helicoidQ r*b+(s/(helicoidQ r)^2)*a =
      helicoidQ r*(b+s*a/(helicoidQ r)^3) := by
    field_simp
  rw [h1,h2,mul_pow,mul_pow] at h
  have hdiv : (a^2+(helicoidQ r)^2*b^2)/(helicoidQ r)^4 ≤
      a^2+(helicoidQ r)^2*b^2 := by
    exact div_le_self (by positivity) hq4
  exact hdiv.trans (h.trans (by nlinarith [sq_nonneg c]))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoid_half_tube_normal_differential_bound
