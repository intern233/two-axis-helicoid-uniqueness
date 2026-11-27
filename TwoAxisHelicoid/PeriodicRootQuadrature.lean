import TwoAxisHelicoid.PeriodicRootMean

namespace TwoAxisHelicoid
open Complex MeasureTheory Set

noncomputable def periodicSampleAverage (N : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (N:ℂ)⁻¹*∑ k∈Finset.range N, f ((z+k)/N)

private theorem sample_periodic {N : ℕ} (hn : 0<N) {f : ℂ → ℂ}
    (per : Function.Periodic f 1) : Function.Periodic (periodicSampleAverage N f) 1 := by
  intro z
  let g := fun k : ℕ => f ((z+k)/N)
  have last : g N=g 0 := by
    have h : (z+(N:ℂ))/N=z/N+1 := by field_simp [show (N:ℂ)≠0 by exact_mod_cast hn.ne']
    simpa only [g,h,Nat.cast_zero,add_zero] using per (z/(N:ℂ))
  have eq := (Finset.sum_range_succ g N).symm.trans (Finset.sum_range_succ' g N)
  rw [last] at eq
  have shifted : (∑ k∈Finset.range N, g (k+1))=∑ k∈Finset.range N,g k := by
    exact (add_right_cancel eq).symm
  unfold periodicSampleAverage
  congr 1
  calc
    (∑ k∈Finset.range N, f ((z+1+(k:ℂ))/N))=∑ k∈Finset.range N, g (k+1) := by
      apply Finset.sum_congr rfl
      intro k _
      apply congrArg f
      simp only [Nat.cast_add_one]
      ring
    _=∑ k∈Finset.range N, g k := shifted

private theorem sample_integral {N : ℕ} (hn : 0<N) {f : ℂ → ℂ}
    (cont : Continuous (fun x : ℝ => f (x:ℂ))) :
    (∫ x : ℝ in 0..1,periodicSampleAverage N f (x:ℂ))=∫ x : ℝ in 0..1,f (x:ℂ) := by
  let g := fun x : ℝ => f (x:ℂ)
  let bd := fun k : ℕ => (k:ℝ)/N
  have hnR : (N:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hnC : (N:ℂ)≠0 := by exact_mod_cast hn.ne'
  have arg (x : ℝ) (k : ℕ) : ((x:ℂ)+k)/N=(((x+k)/N:ℝ):ℂ) := by simp only [Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_natCast]
  have ic (k : ℕ) : IntervalIntegrable (fun x : ℝ => f (((x:ℂ)+k)/N)) volume 0 1 := by
    simp_rw [arg]
    exact (cont.comp ((continuous_id.add_const (k:ℝ)).div_const _)).intervalIntegrable _ _
  have each (k : ℕ) : (∫ x : ℝ in 0..1,f (((x:ℂ)+k)/N))=(N:ℂ)*(∫ x : ℝ in bd k..bd (k+1),g x) := by
    simp_rw [arg]
    change (∫ x : ℝ in 0..1,(fun b : ℝ => g (b/N)) (x+k))=_
    have translate := intervalIntegral.integral_comp_add_right (fun b : ℝ => g (b/N)) (k:ℝ) (a:=0) (b:=1)
    have scale := intervalIntegral.integral_comp_div g hnR (a:=0+(k:ℝ)) (b:=1+(k:ℝ))
    apply translate.trans
    simpa only [zero_add,bd,Nat.cast_add_one,add_comm (1:ℝ) (k:ℝ),Complex.real_smul,Complex.ofReal_natCast] using scale
  have sum := intervalIntegral.sum_integral_adjacent_intervals (n:=N) (a:=bd) (μ:=volume) (f:=g)
    (fun k _ => cont.intervalIntegrable (bd k) (bd (k+1)))
  simp only [periodicSampleAverage,intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum (fun k _ => ic k)]
  simp_rw [each]
  rw [← Finset.mul_sum,← mul_assoc,inv_mul_cancel₀ hnC,one_mul,sum]
  simp [bd,hnR,g]

/-- Quantitative trapezoidal rule for a complete unit period. Shifting
the average gives a strip N times as wide, with the same boundary bound. -/
theorem periodic_strip_trapezoidal_error {N : ℕ} (hn : 0<N) {f : ℂ → ℂ}
    (per : Function.Periodic f 1) {s M : ℝ} (hs : 0<s)
    (hol : ∀ z : ℂ, |z.im|≤s → DifferentiableAt ℂ f z)
    (bound : ∀ z : ℂ, |z.im|=s → ‖f z‖≤M) :
    let r := Real.exp (-(2*Real.pi*((N:ℝ)*s)))
    ‖periodicSampleAverage N f 0-(∫ x : ℝ in 0..1,f (x:ℂ))‖≤2*(M*r/(1-r)) := by
  have hp : 0<(N:ℝ) := by exact_mod_cast hn
  have hN : 0<(N:ℝ)*s := mul_pos hp hs
  have im (z : ℂ) (k : ℕ) : |((z+k)/N).im|=|z.im|/(N:ℝ) := by
    rw [show (N:ℂ)=((N:ℝ):ℂ) by simp,Complex.div_ofReal_im,Complex.add_im,Complex.natCast_im,add_zero,
      abs_div,abs_of_pos hp]
  have hd (z : ℂ) (hz : |z.im|≤(N:ℝ)*s) : DifferentiableAt ℂ (periodicSampleAverage N f) z := by
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.fun_sum
    intro k _
    apply (hol _ ?_).comp z ((differentiableAt_id.add_const (k:ℂ)).div_const _)
    rw [im,div_le_iff₀ hp,mul_comm];exact hz
  have hb (z : ℂ) (hz : |z.im|=(N:ℝ)*s) : ‖periodicSampleAverage N f z‖≤M := by
    have each (k : ℕ) : ‖f ((z+k)/N)‖≤M := bound _ (by rw [im,hz,mul_comm,mul_div_cancel_right₀ _ hp.ne'])
    rw [periodicSampleAverage,norm_mul,norm_inv,Complex.norm_natCast]
    apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hp.le)).trans
    apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => each k)) (inv_nonneg.mpr hp.le)).trans
    simp [nsmul_eq_mul,hp.ne']
  have cont : Continuous (fun x : ℝ => f (x:ℂ)) := continuous_iff_continuousAt.mpr fun x =>
    (hol _ (by simpa only [Complex.ofReal_im,abs_zero] using hs.le)).continuousAt.comp Complex.continuous_ofReal.continuousAt
  have result := periodic_strip_mean_error (sample_periodic hn per) hN hd
    (fun x => hb _ (by simp [abs_of_pos hN])) (fun x => hb _ (by simp [abs_of_pos hN]))
  simpa only [sample_integral hn cont] using result

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.periodic_strip_trapezoidal_error
