import TwoAxisHelicoid.LeftProductError

namespace TwoAxisHelicoid
open Complex

/-- The intermediate polynomial majorant in the left-end vertical-root balance. -/
theorem left_vertical_root_balance_chain {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    let q := leftNome t
    let r := leftRootR t
    let b := leftBeta t
    0 ≤ b-r ∧ b-r ≤ 2*b^2+3*r^2+4*q^3 ∧ 2*b^2+3*r^2+4*q^3 ≤ 12*q^2 := by
  let q := leftNome t
  let r := leftRootR t
  let b := leftBeta t
  change 0 ≤ b-r ∧ b-r ≤ 2*b^2+3*r^2+4*q^3 ∧ 2*b^2+3*r^2+4*q^3 ≤ 12*q^2
  have ht4 : t ≤ 1/4 := by linarith
  have hq0 : 0 < q := leftNome_pos t
  have hq : q ≤ 1/100 := (leftNome_lt_one_hundredth ht ht4).le
  have hr : 0 < r := leftRootR_pos t
  have hb : 0 < b := leftBeta_pos t
  obtain ⟨hrl, hru⟩ := leftRootR_bounds ht ht4
  obtain ⟨hbl, hbu⟩ := leftBeta_bounds ht ht4
  change q/2 < r at hrl
  change r < q at hru
  change q ≤ b at hbl
  change b ≤ 2*q at hbu
  have hroot := jacobiRealE_at_verticalA_zero (small_height_mem_vertical_domain ht ht4)
  have hsplit := jacobiRealE_split_root hq0 hq hrl.le hru.le
  rw [hroot] at hsplit
  change 0 = jacobiFraction r-b/(1+b)^2+jacobiRootRemainder q r at hsplit
  have hT := (le_abs_self _).trans (jacobiRootRemainder_abs_lt hq0 hq hrl.le hru.le).le
  have hbeta := jacobi_beta_fraction_error_le hb.le
  have hrr := jacobi_r_fraction_error_le hr.le (hru.le.trans hq)
  refine ⟨sub_nonneg.mpr (hru.le.trans hbl), ?_, ?_⟩
  · linarith only [hsplit, hT, hbeta, hrr]
  · have hb2 := pow_le_pow_left₀ hb.le hbu 2
    have hr2 := pow_le_pow_left₀ hr.le hru.le 2
    have hq3 := mul_le_mul_of_nonneg_left (show q ≤ (1/4 : ℝ) by linarith) (sq_nonneg q)
    nlinarith only [hb2, hr2, hq3]

/-- On the full midline annulus the two families of perturbations remaining
after the first inverse-argument factor is removed have this exact norm sum. -/
theorem left_jacobi_remainder_deviation_sum {t ρ : ℝ} (ht : 0 < t) (htu : t ≤ 1/8)
    (hρl : leftNome t ≤ ρ) (hρu : ρ ≤ (leftNome t)⁻¹) :
    let q := leftNome t
    let r := leftRootR t
    let Q := jacobiNome (1/t)
    let z := (r : ℂ)*(I*(ρ : ℂ))
    (∑' n : ℕ, (‖Q^(n+1)*z‖+‖Q^(n+1)*(Q/z)‖)) =
      (q^2*r*ρ+q^4/(r*ρ))/(1-q^2) ∧
      (q^2*r*ρ+q^4/(r*ρ))/(1-q^2) ≤ 4*q^2 := by
  let q := leftNome t
  let r := leftRootR t
  let Q := jacobiNome (1/t)
  let x := I*(ρ : ℂ)
  let z := (r : ℂ)*x
  change (∑' n : ℕ, (‖Q^(n+1)*z‖+‖Q^(n+1)*(Q/z)‖)) =
    (q^2*r*ρ+q^4/(r*ρ))/(1-q^2) ∧
    (q^2*r*ρ+q^4/(r*ρ))/(1-q^2) ≤ 4*q^2
  have ht4 : t ≤ 1/4 := by linarith
  have hq0 : 0 < q := leftNome_pos t
  have hr0 : 0 < r := leftRootR_pos t
  have hρ0 : 0 < ρ := hq0.trans_le hρl
  have hx : ‖x‖ = ρ := by
    change ‖I * (ρ : ℂ)‖ = ρ
    rw [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
  have hz : ‖z‖ = r*ρ := by
    change ‖(r : ℂ) * x‖ = r*ρ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hx]
  have hQ : ‖Q‖ = q^2 := by
    simp only [Q, q, jacobiNome_inverse_eq_leftNome ht, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_sq]
  have hQ1 : ‖Q‖ < 1 := jacobiNome_norm_lt_one (one_div_pos.mpr ht)
  constructor
  · rw [(jacobi_factor_norm_summable hQ1 z).tsum_add (jacobi_factor_norm_summable hQ1 (Q/z)),
      jacobi_factor_norm_tsum hQ1 z, jacobi_factor_norm_tsum hQ1 (Q/z), norm_div, hQ, hz]
    ring
  · obtain ⟨hrl, hru⟩ := leftRootR_bounds ht ht4
    have hargs := small_remainder_argument_bounds hq0 hrl.le hru.le hQ
      (x := x) (by rwa [hx]) (by rwa [hx])
    change ‖z‖ ≤ 1 ∧ ‖Q/z‖ ≤ 2 at hargs
    rw [norm_div, hQ, hz] at hargs
    have hq : q ≤ 1/100 := (leftNome_lt_one_hundredth ht ht4).le
    have hsq := mul_le_mul_of_nonneg_left hq hq0.le
    have hden : (3/4 : ℝ) ≤ 1-q^2 := by nlinarith only [hq, hsq]
    apply (div_le_iff₀ (by linarith only [hden] : 0 < 1-q^2)).mpr
    calc
      q^2*r*ρ+q^4/(r*ρ) = q^2*(r*ρ+q^2/(r*ρ)) := by ring
      _ ≤ q^2*(1+2) := mul_le_mul_of_nonneg_left (add_le_add hargs.1 hargs.2) (sq_nonneg q)
      _ = 4*q^2*(3/4) := by ring
      _ ≤ 4*q^2*(1-q^2) := mul_le_mul_of_nonneg_left hden (by positivity)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.left_vertical_root_balance_chain
#print axioms TwoAxisHelicoid.left_jacobi_remainder_deviation_sum
