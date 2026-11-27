import TwoAxisHelicoid.RectangularProductQuasiperiod
import TwoAxisHelicoid.ThetaConvergence
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

namespace TwoAxisHelicoid
open Complex Set Filter Topology

noncomputable def rectangularFourierTerm (t : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  (rectangularProductNome t)^(n+1)/(1-(rectangularProductNome t)^(n+1))*
    Complex.sin (((n+1:ℕ):ℂ)*Real.pi*z)

theorem rectangular_nome_exponential_norm (t : ℝ) :
    ‖rectangularProductNome t‖=Real.exp (-2*Real.pi*t) := by
  rw [rectangular_product_nome_actual,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem rectangular_fourier_inner_strip_bound {t h : ℝ} (ht : 0<t) (hh : h<2*t) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n (z : ℂ), |z.im|≤h → ‖rectangularFourierTerm t n z‖≤u n := by
  let Q := rectangularProductNome t
  let B := ‖Q‖*Real.exp (Real.pi*h)
  have q : ‖Q‖<1 := rectangular_product_nome_norm ht
  have bp : 0≤B := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have b1 : B<1 := by
    dsimp only [B,Q]
    rw [rectangular_nome_exponential_norm,← Real.exp_add,Real.exp_lt_one_iff]
    nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hh)]
  have s : Summable (fun n : ℕ => B^(n+1)) := (summable_nat_add_iff 1).mpr
    (summable_geometric_of_lt_one bp b1)
  refine ⟨fun n => B^(n+1)/(1-‖Q‖),s.div_const _,?_⟩
  intro n z hz
  let k := n+1
  have nz : k≠0 := Nat.succ_ne_zero n
  have den : 1-‖Q‖≤‖1-Q^k‖ := by
    have tr := norm_sub_norm_le (1:ℂ) (Q^k)
    rw [norm_one,norm_pow] at tr
    linarith [pow_le_of_le_one (norm_nonneg Q) q.le nz]
  have imag : |(((k:ℂ)*Real.pi)*z).im|≤(k:ℝ)*Real.pi*h := by
    have F : ((k:ℂ)*Real.pi)=(((k:ℝ)*Real.pi:ℝ):ℂ) := by push_cast;rfl
    rw [F,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,zero_mul,add_zero,abs_mul,
      abs_of_nonneg (show 0≤(k:ℝ)*Real.pi by positivity)]
    exact mul_le_mul_of_nonneg_left hz (by positivity)
  have sinBound : ‖Complex.sin ((k:ℂ)*Real.pi*z)‖≤(Real.exp (Real.pi*h))^k := by
    rw [← sineJet_zero,← Real.exp_nat_mul]
    exact (sineJet_norm_le 0 _).trans (Real.exp_le_exp.mpr (by linear_combination imag))
  change ‖Q^k/(1-Q^k)*Complex.sin ((k:ℂ)*Real.pi*z)‖≤B^k/(1-‖Q‖)
  rw [norm_mul,norm_div,norm_pow]
  calc _ ≤ (‖Q‖^k/(1-‖Q‖))*(Real.exp (Real.pi*h))^k := by
         exact mul_le_mul (div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr q) den) sinBound
           (norm_nonneg _) (div_nonneg (by positivity) (sub_pos.mpr q).le)
       _=B^k/(1-‖Q‖) := by dsimp only [B]; rw [mul_pow]; ring

/-- Uniform convergence on any closed interior strip. -/
theorem rectangular_fourier_uniform_on_strip {t h : ℝ} (ht : 0<t) (hh : h<2*t) :
    HasSumUniformlyOn (rectangularFourierTerm t) (fun z => ∑' n, rectangularFourierTerm t n z)
      {z : ℂ | |z.im|≤h} := by
  obtain ⟨u,converges,bound⟩ := rectangular_fourier_inner_strip_bound ht hh
  exact HasSumUniformlyOn.of_norm_le_summable converges bound

/-- Holomorphy and termwise differentiation hold on the full open
strip of the manuscript. The differentiated series converges to the
actual complex derivative at every point there. -/
theorem rectangular_fourier_termwise_derivative {t : ℝ} (ht : 0<t) {z : ℂ} (hz : |z.im|<2*t) :
    let S := fun w => ∑' n : ℕ, rectangularFourierTerm t n w
    DifferentiableAt ℂ S z ∧ HasSum (fun n : ℕ =>
      (rectangularProductNome t)^(n+1)/(1-(rectangularProductNome t)^(n+1))*
      (Complex.cos (((n+1:ℕ):ℂ)*Real.pi*z)*(((n+1:ℕ):ℂ)*Real.pi))) (deriv S z) := by
  obtain ⟨h,zh,htop⟩ := exists_between hz
  let U := {w : ℂ | |w.im|<h}
  have op : IsOpen U := isOpen_lt Complex.continuous_im.abs continuous_const
  obtain ⟨u,converges,bound⟩ := rectangular_fourier_inner_strip_bound ht htop
  have ud (n : ℕ) : DifferentiableOn ℂ (rectangularFourierTerm t n) U := by
    unfold rectangularFourierTerm
    fun_prop
  have b (n : ℕ) (w : ℂ) (hw : w∈U) := bound n w (show |w.im|<h from hw).le
  have hol := Complex.differentiableOn_tsum_of_summable_norm converges ud op b
  have d := Complex.hasSum_deriv_of_summable_norm converges ud op b (show z∈U from zh)
  refine ⟨hol.differentiableAt (op.mem_nhds zh),d.congr_fun ?_⟩
  intro n
  let k : ℂ := (n+1:ℕ)
  have dz := (((hasDerivAt_id' z).const_mul (k*Real.pi)).csin).const_mul
    ((rectangularProductNome t)^(n+1)/(1-(rectangularProductNome t)^(n+1)))
  unfold rectangularFourierTerm
  simpa only [k,mul_one] using dz.deriv.symm

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rectangular_fourier_uniform_on_strip
#print axioms TwoAxisHelicoid.rectangular_fourier_termwise_derivative

