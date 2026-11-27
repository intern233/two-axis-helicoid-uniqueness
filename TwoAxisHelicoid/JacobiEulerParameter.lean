import TwoAxisHelicoid.JacobiProductBasic
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology
set_option maxHeartbeats 800000

noncomputable def jacobiEulerProduct (q : ℂ) : ℂ := ∏' n : ℕ, (1-q^(n+1))

theorem jacobiEulerProduct_eq_factor (q : ℂ) :
    jacobiEulerProduct q = jacobiFactorProduct q 1 := by
  simp only [jacobiEulerProduct,jacobiFactorProduct,mul_one]

theorem jacobiEulerProduct_locally_uniform :
    MultipliableLocallyUniformlyOn (fun n : ℕ => fun q : ℂ => 1-q^(n+1)) (ball 0 1) := by
  use jacobiEulerProduct
  simp only [sub_eq_add_neg]
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_ball
  intro K hKsub hK
  rcases K.eq_empty_or_nonempty with he | hne
  · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn,he] using tendstoUniformlyOn_empty
  · obtain ⟨q₀,hq₀,_,hbound⟩ := hK.exists_sSup_image_eq_and_ge hne
      (show ContinuousOn (fun q : ℂ => ‖q‖) K by fun_prop)
    have hq : ‖q₀‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hKsub hq₀
    have hs : Summable (fun n : ℕ => ‖q₀‖^(n+1)) := by
      simpa only [norm_mul,norm_one,mul_one,norm_pow] using jacobi_factor_norm_summable hq (1 : ℂ)
    apply hs.hasProdUniformlyOn_nat_one_add hK (.of_forall fun n q hqK => ?_) (fun _ => by fun_prop)
    simpa only [norm_neg,norm_pow] using pow_le_pow_left₀ (norm_nonneg q) (hbound q hqK) (n+1)

theorem jacobiEulerProduct_analyticAt {q : ℂ} (hq : ‖q‖ < 1) :
    AnalyticAt ℂ jacobiEulerProduct q := by
  have hd := jacobiEulerProduct_locally_uniform.hasProdLocallyUniformlyOn.differentiableOn
    (.of_forall fun _ => by simpa [Finset.prod_fn] using
      DifferentiableOn.finsetProd (fun _ _ => by fun_prop)) isOpen_ball
  exact hd.analyticAt (isOpen_ball.mem_nhds (by simpa only [mem_ball,dist_zero_right] using hq))

theorem jacobiEulerProduct_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : jacobiEulerProduct q ≠ 0 := by
  rw [jacobiEulerProduct_eq_factor]
  exact jacobiFactorProduct_ne_zero_of_norm hq (by simpa using hq)

@[simp] theorem jacobiEulerProduct_zero : jacobiEulerProduct 0 = 1 := by
  simp [jacobiEulerProduct]

theorem jacobiEulerProduct_logDeriv {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    logDeriv jacobiEulerProduct q =
      ∑' n : ℕ, -(n+1 : ℂ)*q^n/(1-q^(n+1)) := by
  have hn (n : ℕ) : 1-q^(n+1) ≠ 0 := by
    have hp : ‖q^(n+1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
    exact sub_ne_zero.mpr (by intro he; rw [← he,norm_one] at hp; exact hp.false)
  have hs := ((summable_norm_pow_mul_geometric_div_one_sub 1 hq).comp_injective
    (show Function.Injective (fun n : ℕ => n+1) from Nat.succ_injective)).mul_right (-q⁻¹)
  have hs' : Summable (fun n : ℕ => -(n+1 : ℂ)*q^n/(1-q^(n+1))) := by
    apply hs.congr
    intro n
    simp only [Function.comp_apply,Nat.cast_add,Nat.cast_one,pow_succ]
    field_simp
  have hf (n : ℕ) : logDeriv (fun w : ℂ => 1-w^(n+1)) q =
      -(n+1 : ℂ)*q^n/(1-q^(n+1)) := by
    have hd := ((hasDerivAt_id q).pow (n+1)).const_sub 1
    simp only [Pi.pow_apply,id_eq] at hd
    rw [logDeriv_apply,hd.deriv]
    norm_num only [Nat.add_sub_cancel,mul_one,Nat.cast_add,Nat.cast_one]
    ring
  have he := logDeriv_tprod_eq_tsum isOpen_ball
    (show q ∈ ball (0 : ℂ) 1 by simpa only [mem_ball,dist_zero_right] using hq)
    hn (fun _ => by fun_prop) (hs'.congr (fun n => (hf n).symm))
    jacobiEulerProduct_locally_uniform (jacobiEulerProduct_ne_zero hq)
  simpa only [hf,jacobiEulerProduct] using! he

theorem jacobiEulerProduct_logDeriv_mul {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    logDeriv jacobiEulerProduct q*q =
      -(∑' n : ℕ, (n+1 : ℂ)*q^(n+1)/(1-q^(n+1))) := by
  rw [jacobiEulerProduct_logDeriv hq hq0,← tsum_mul_right,← tsum_neg]
  apply tsum_congr
  intro n
  rw [pow_succ]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiEulerProduct_analyticAt
#print axioms TwoAxisHelicoid.jacobiEulerProduct_logDeriv_mul
