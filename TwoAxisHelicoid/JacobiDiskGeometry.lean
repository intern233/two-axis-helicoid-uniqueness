import TwoAxisHelicoid.JacobiPhysicalCoordinates

namespace TwoAxisHelicoid
open Complex Metric Set
set_option maxHeartbeats 800000
attribute [local irreducible] thetaA thetaJet

theorem rhombic_nonintegral_real_strip {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : |z.re| < 1) (hz0 : z.re ≠ 0) : z ∉ (rhombicPeriodPair t ht).lattice := by
  intro h
  obtain ⟨m,n,hr,_⟩ := (rhombic_mem_lattice_iff ht z).mp h
  have hint : |((2*m+n : ℤ) : ℝ)| < 1 := by push_cast; rwa [← hr]
  have hint' : |2*m+n| < (1 : ℤ) := by exact_mod_cast hint
  have he : 2*m+n = 0 := by
    have h := abs_lt.mp hint'
    omega
  apply hz0
  calc
    z.re = ((2*m+n : ℤ) : ℝ) := by simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat] using hr
    _ = 0 := by rw [he, Int.cast_zero]

/-- A disk may avoid the lattice by its imaginary part or by its real part.
The second case permits large disks far from the pole when the height is small. -/
def JacobiDiskGuard (tlo x R : ℚ) : Prop :=
  R < tlo/2 ∨ (R < |x| ∧ |x|+R < 1)

instance (tlo x R : ℚ) : Decidable (JacobiDiskGuard tlo x R) := by
  unfold JacobiDiskGuard
  infer_instance

theorem jacobiDiskGuard_not_mem {tlo x R : ℚ} {t : ℝ} (ht : 0 < t)
    (htl : (tlo : ℝ) ≤ t) (hg : JacobiDiskGuard tlo x R) {z : ℂ}
    (hz : z ∈ closedBall (x : ℂ) (R : ℝ)) :
    z+I*((t/2 : ℝ) : ℂ) ∉ (rhombicPeriodPair t ht).lattice := by
  have hnorm := mem_closedBall_iff_norm.mp hz
  have him : |z.im| ≤ (R : ℝ) := by
    have h := (Complex.abs_im_le_norm (z-(x : ℂ))).trans hnorm
    simpa only [Complex.sub_im, Complex.ratCast_im, sub_zero] using h
  have hre : |z.re-(x : ℝ)| ≤ (R : ℝ) := by
    have h := (Complex.abs_re_le_norm (z-(x : ℂ))).trans hnorm
    simpa only [Complex.sub_re, Complex.ratCast_re] using h
  rcases hg with hi | ⟨hr,hu⟩
  · have hi' : (R : ℝ) < (tlo : ℝ)/2 := by exact_mod_cast hi
    exact shifted_horizontal_strip_not_mem ht (lt_of_le_of_lt him (by linarith))
  · have hr' : (R : ℝ) < |(x : ℝ)| := by exact_mod_cast hr
    have hu' : |(x : ℝ)|+(R : ℝ) < 1 := by exact_mod_cast hu
    have h0 : z.re ≠ 0 := by
      intro he
      rw [he, zero_sub, abs_neg] at hre
      linarith
    have h1 : |z.re| < 1 := by
      have h := abs_add_le (z.re-(x : ℝ)) (x : ℝ)
      rw [sub_add_cancel] at h
      linarith
    apply rhombic_nonintegral_real_strip ht
    · simpa only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_self, add_zero] using h1
    · simpa only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_self, add_zero] using h0

theorem centeredThetaA_disk_analytic {tlo x R : ℚ} {t : ℝ} (ht : 0 < t)
    (htl : (tlo : ℝ) ≤ t) (hg : JacobiDiskGuard tlo x R) (a : ℝ) :
    DiffContOnCl ℂ (fun z : ℂ => thetaA t a (z+I*((t/2 : ℝ) : ℂ)))
      (ball (x : ℂ) (R : ℝ)) := by
  have hd : DifferentiableOn ℂ (fun z : ℂ => thetaA t a (z+I*((t/2 : ℝ) : ℂ)))
      {z : ℂ | z+I*((t/2 : ℝ) : ℂ) ∉ (rhombicPeriodPair t ht).lattice} := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hreg := mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht _).mp hz
    exact (thetaA_differentiableAt ht a hreg).comp z (by fun_prop)
  exact hd.diffContOnCl_ball (fun z hz => jacobiDiskGuard_not_mem ht htl hg hz)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.centeredThetaA_disk_analytic
