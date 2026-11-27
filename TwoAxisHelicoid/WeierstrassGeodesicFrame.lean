import TwoAxisHelicoid.LogGaussMetricConnection

namespace TwoAxisHelicoid
open Complex Real
set_option maxHeartbeats 1000000

noncomputable def weierstrassExpPrime (z : ℂ) : Fin 3 → ℂ := ![-cosh z,I*sinh z,0]

theorem weierstrass_exp_direction_metric (z v : ℂ) :
    (∑ j, (nullRealDerivative (weierstrassTriple (exp z) 1) v j)^2) =
      (Real.cosh z.re)^2*Complex.normSq v := by
  obtain ⟨hx,hy⟩ := weierstrass_exp_real_tangents z
  have hv : v = v.re • (1 : ℂ)+v.im • I := by apply Complex.ext <;> simp
  have he : nullRealDerivative (weierstrassTriple (exp z) 1) v =
      v.re • logGaussTangentX z.re z.im+v.im • logGaussTangentY z.re z.im := by
    conv_lhs => rw [hv,map_add,map_smul,map_smul,hx,hy]
  rw [he]
  have h := sum_sq_three_vectors (logGaussTangentX z.re z.im) (logGaussTangentY z.re z.im)
    (fun _ => 0) v.re v.im 0
  obtain ⟨hxx,hyy,hxy⟩ := logGaussTangent_conformal z.re z.im
  simp only [zero_mul,mul_zero,add_zero,hxx,hyy,hxy] at h
  change (∑ j, (v.re*logGaussTangentX z.re z.im j+v.im*logGaussTangentY z.re z.im j)^2) = _
  rw [h]
  simp only [Complex.normSq_apply]
  ring

theorem weierstrass_exp_prime_hasDerivAt {W : ℂ → ℂ} {D z : ℂ} (hW : HasDerivAt W D z) :
    HasDerivAt (fun w => weierstrassTriple (exp (W w)) 1) (D • weierstrassExpPrime (W z)) z := by
  simp_rw [weierstrassTriple_exp]
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases j
  · change HasDerivAt (fun w => -sinh (W w)) (D*(-cosh (W z))) z
    convert hW.csinh.neg using 1
    ring
  · change HasDerivAt (fun w => I*cosh (W w)) (D*(I*sinh (W z))) z
    convert hW.ccosh.const_mul I using 1
    ring
  · change HasDerivAt (fun _ : ℂ => (1 : ℂ)) (D*0) z
    simpa only [mul_zero] using hasDerivAt_const z (1 : ℂ)

/-- Subtracting the tangential connection term from the actual complex
second derivative leaves the real Gauss unit normal. -/
theorem weierstrass_exp_geodesic_coefficient (z : ℂ) (j : Fin 3) :
    weierstrassExpPrime z j-(Real.tanh z.re : ℂ)*weierstrassTriple (exp z) 1 j =
      -(logGaussSphere z.re z.im j : ℂ) := by
  rw [weierstrassTriple_exp]
  obtain ⟨hsr,hsi⟩ := complex_sinh_re_im_formula z
  obtain ⟨hcr,hci⟩ := complex_cosh_re_im_formula z
  fin_cases j <;> dsimp [weierstrassExpPrime,logGaussSphere] <;> apply Complex.ext <;>
    simp only [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.neg_re,
      Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      hsr,hsi,hcr,hci,zero_mul,mul_one,one_mul,zero_add,add_zero,sub_zero,zero_sub,
      Real.tanh_eq_sinh_div_cosh]
  all_goals
    field_simp [(Real.cosh_pos z.re).ne']
    nlinarith [congrArg (fun a : ℝ => Real.cos z.im*a) (Real.cosh_sq_sub_sinh_sq z.re),
      congrArg (fun a : ℝ => Real.sin z.im*a) (Real.cosh_sq_sub_sinh_sq z.re)]

theorem weierstrass_geodesic_acceleration_normal (z D v : ℂ) (j : Fin 3) :
    (v^2*(D*weierstrassExpPrime z j)-
      ((Real.tanh z.re : ℂ)*D*v^2)*weierstrassTriple (exp z) 1 j).re =
      -(D*v^2).re*logGaussSphere z.re z.im j := by
  have h : v^2*(D*weierstrassExpPrime z j)-
      ((Real.tanh z.re : ℂ)*D*v^2)*weierstrassTriple (exp z) 1 j =
      (D*v^2)*(weierstrassExpPrime z j-(Real.tanh z.re : ℂ)*weierstrassTriple (exp z) 1 j) := by ring
  rw [h,weierstrass_exp_geodesic_coefficient]
  simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,
    neg_zero,mul_zero,sub_zero]
  ring

theorem weierstrass_geodesic_acceleration_bound (z D v : ℂ) (hv : ‖v‖ ≤ 1) :
    (∑ j, (-(D*v^2).re*logGaussSphere z.re z.im j)^2) ≤ ‖D‖^2 := by
  simp only [mul_pow,← Finset.mul_sum,logGaussSphere_unit,mul_one,neg_sq]
  have hn : ‖D*v^2‖ ≤ ‖D‖ := by
    rw [norm_mul,norm_pow]
    have hs : ‖v‖^2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hv
    nlinarith [norm_nonneg D]
  have hr := (Complex.abs_re_le_norm (D*v^2)).trans hn
  simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg _) hr 2)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.weierstrass_geodesic_acceleration_normal
