import TwoAxisHelicoid.PlanarRadialBarrier

namespace TwoAxisHelicoid
open Complex Set Metric Topology InnerProductSpace Laplacian
open scoped Topology InnerProductSpace

/-- For any radius and any bound on the drift and scalar terms, the
explicit exponential barrier has strictly positive elliptic defect
throughout the outer half of the disk. -/
theorem exists_strict_planar_radial_barrier (c : ℂ) {K r : ℝ} (hK : 0 ≤ K) (hr : 0 < r) :
    ∃ k : ℝ, 0 < k ∧ ∀ z : ℂ, r/2 ≤ dist z c → dist z c ≤ r →
      K*(|planePartial 1 (planarRadialBarrier c k r) z|+
        |planePartial I (planarRadialBarrier c k r) z|+planarRadialBarrier c k r z) <
        (Δ (planarRadialBarrier c k r)) z := by
  let k := max 1 ((5+4*K*r+K)/r^2)
  have hk1 : 1 ≤ k := le_max_left _ _
  have hk : 0 < k := zero_lt_one.trans_le hk1
  have ks : 4+4*K*r+K < k*r^2 := by
    have h := (div_le_iff₀ (sq_pos_of_pos hr)).mp (le_max_right 1 ((5+4*K*r+K)/r^2))
    linarith
  refine ⟨k,hk,?_⟩
  intro z hlo hhi
  let e := Real.exp (-k*dist z c^2)
  have he : 0 < e := Real.exp_pos _
  have x : |z.re-c.re| ≤ r := (Complex.abs_re_le_norm (z-c)).trans (by rwa [← dist_eq_norm])
  have y : |z.im-c.im| ≤ r := (Complex.abs_im_le_norm (z-c)).trans (by rwa [← dist_eq_norm])
  have first : |planePartial 1 (planarRadialBarrier c k r) z|=2*k*|z.re-c.re| * e := by
    rw [planarRadialBarrier_partial]
    simp [e,abs_mul,abs_of_pos hk]
  have second : |planePartial I (planarRadialBarrier c k r) z|=2*k*|z.im-c.im| * e := by
    rw [planarRadialBarrier_partial]
    simp [e,abs_mul,abs_of_pos hk]
  have bound : planarRadialBarrier c k r z ≤ e := by rw [planarRadialBarrier_value]; exact sub_le_self _ (Real.exp_pos _).le
  have grad : |planePartial 1 (planarRadialBarrier c k r) z|+
      |planePartial I (planarRadialBarrier c k r) z|+planarRadialBarrier c k r z ≤ (4*k*r+1)*e := by
    rw [first,second]
    have hx := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left x (by positivity : 0 ≤ 2*k)) he.le
    have hy := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left y (by positivity : 0 ≤ 2*k)) he.le
    linarith
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left grad hK)
  rw [planarRadialBarrier_laplacian]
  change K*((4*k*r+1)*e) < (4*k^2*dist z c^2-4*k)*e
  rw [← mul_assoc]
  apply mul_lt_mul_of_pos_right _ he
  have rad : r^2 ≤ (2*dist z c)^2 := by gcongr; linarith
  have quad := mul_le_mul_of_nonneg_left rad (sq_nonneg k)
  have drift := mul_lt_mul_of_pos_left ks hk
  have constant := mul_le_mul_of_nonneg_right hk1 hK
  nlinarith only [quad,drift,constant]

/-- At the outer sphere the barrier vanishes and its derivative toward
the center is strictly positive. -/
theorem planar_radial_barrier_inward {c y : ℂ} {r k : ℝ} (hr : 0 < r) (hk : 0 < k) (hy : dist y c=r) :
    planarRadialBarrier c k r y=0 ∧ 0 < planePartial (c-y) (planarRadialBarrier c k r) y := by
  refine ⟨by simp [planarRadialBarrier_value,hy],?_⟩
  have sq : (y.re-c.re)^2+(y.im-c.im)^2 = r^2 := by
    rw [← hy,dist_eq_norm,← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,pow_two]
  rw [planarRadialBarrier_partial,Complex.sub_re,Complex.sub_im,hy]
  have e : (y.re-c.re)*(c.re-y.re)+(y.im-c.im)*(c.im-y.im) = -r^2 := by linear_combination -sq
  rw [e,show -2*k*(-r^2)=2*k*r^2 by ring]
  positivity

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exists_strict_planar_radial_barrier
