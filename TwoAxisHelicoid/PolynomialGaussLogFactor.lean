import TwoAxisHelicoid.PuncturedGaussLogFactorization

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology

/-- Polynomial growth of the real logarithmic modulus rules out an
essential singularity of the remaining single-valued logarithm. This
keeps the winding integer and makes no symmetry assumption. -/
theorem punctured_unit_meromorphic_log_factor {g : ℂ → ℂ} {B : ℝ} (hB : 0<B) (N : ℕ)
    (regular : ∀ᶠ z in 𝓝[≠] (0:ℂ), AnalyticAt ℂ g z ∧ g z≠0)
    (bound : ∀ᶠ z in 𝓝[≠] (0:ℂ), |Real.log ‖g z‖|≤B/‖z‖^(N+1)) :
    ∃ (n : ℤ) (F : ℂ → ℂ), MeromorphicAt F 0 ∧ MeromorphicAt (logDeriv g) 0 ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt F (logDeriv g z-(n:ℂ)/z) z ∧ g z=z^n*exp (F z) := by
  obtain ⟨r,hr,h⟩ := Metric.mem_nhdsWithin_iff.mp regular
  obtain ⟨n,F,fac⟩ := punctured_holomorphic_unit_factor (g := g) hr (fun z nz s => h (show z∈ball (0:ℂ) r ∩ {0}ᶜ from
    ⟨by rwa [mem_ball,dist_zero_right],norm_pos_iff.mp nz⟩))
  have ev : ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt F (logDeriv g z-(n:ℂ)/z) z ∧ g z=z^n*exp (F z) := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) hr)] with z n s
    exact fac z (norm_pos_iff.mpr n) (by simpa only [mem_ball,dist_zero_right] using s)
  have realBound : ∀ᶠ z in 𝓝[≠] (0:ℂ), |(F z).re|≤(B+|(n:ℝ)|)/‖z‖^(N+1) := by
    filter_upwards [ev,bound,self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) zero_lt_one)] with z fact up nz sm
    let s := ‖z‖
    have hs : 0<s := norm_pos_iff.mpr nz
    have small : s<1 := by simpa only [mem_ball,dist_zero_right] using sm
    have logEq : Real.log ‖g z‖=(n:ℝ)*Real.log s+(F z).re := by
      rw [fact.2,norm_mul,norm_zpow,Complex.norm_exp,Real.log_mul (zpow_ne_zero _ hs.ne') (Real.exp_pos _).ne',
        Real.log_zpow,Real.log_exp]
    have logs : |Real.log s|≤1/s^(N+1) := by
      rw [abs_of_nonpos (Real.log_nonpos hs.le small.le)]
      apply (neg_le_neg (Real.neg_inv_le_log hs.le)).trans
      rw [neg_neg,one_div]
      apply inv_anti₀ (pow_pos hs _)
      rw [pow_succ]
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hs.le small.le) hs.le).trans_eq (one_mul s)
    calc
      |(F z).re| = |Real.log ‖g z‖-(n:ℝ)*Real.log s| := by rw [logEq]; ring_nf
      _ ≤ |Real.log ‖g z‖|+|(n:ℝ)| * |Real.log s| := by rw [← abs_mul]; simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (Real.log ‖g z‖) (-((n:ℝ)*Real.log s))
      _ ≤ B/s^(N+1)+|(n:ℝ)| * (1/s^(N+1)) := add_le_add up (mul_le_mul_of_nonneg_left logs (abs_nonneg _))
      _ = _ := by dsimp [s]; ring
  obtain ⟨R,hR,inR⟩ := Metric.mem_nhdsWithin_iff.mp (ev.and realBound)
  have get (z : ℂ) (nz : 0<‖z‖) (small : ‖z‖<R) := inR (show z∈ball (0:ℂ) R ∩ {0}ᶜ from
    ⟨by rwa [mem_ball,dist_zero_right],norm_pos_iff.mp nz⟩)
  have mer := meromorphic_of_polynomial_real_height hR (show 0<B+|(n:ℝ)| by positivity) (N+1)
    (fun z nz s => (get z nz s).1.1.differentiableAt) (fun z nz s => (get z nz s).2)
  have cogerm : (fun z => deriv F z+(n:ℂ)/z)=ᶠ[𝓝[≠] (0:ℂ)] logDeriv g := by
    filter_upwards [ev] with z hz
    rw [hz.1.deriv,sub_add_cancel]
  exact ⟨n,F,mer,(mer.deriv.add ((MeromorphicAt.const (n:ℂ) 0).div analyticAt_id.meromorphicAt)).congr cogerm,ev⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_unit_meromorphic_log_factor
