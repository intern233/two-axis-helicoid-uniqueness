import TwoAxisHelicoid.LeftParameterLimits

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology
set_option maxHeartbeats 1000000
attribute [local irreducible] verticalA

theorem leftKappa_pow_chordH_pow_tendsto_zero (n m : ℕ) (hm : 0 < m) :
    Tendsto (fun t : ℝ => (leftKappa t)^n*(leftChordH (leftNome t))^m)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlim := (leftKappa_pow_exp_tendsto_zero n hc).mul
    (leftChordH_mul_exp_kappa_tendsto_two.pow m)
  simp only [zero_mul] at hlim
  apply hlim.congr
  intro t
  rw [mul_pow,← Real.exp_nat_mul]
  calc
    _ = (leftKappa t)^n*(leftChordH (leftNome t))^m*
        (Real.exp (-(m : ℝ)*leftKappa t)*Real.exp ((m : ℝ)*leftKappa t)) := by ring
    _ = _ := by rw [← Real.exp_add]; simp only [neg_mul,neg_add_cancel,Real.exp_zero,mul_one]

theorem leftKappa_pow_exp_over_chordH_tendsto_zero (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => (leftKappa t)^n*Real.exp (-leftKappa t)*
      Real.exp (-c*leftKappa t)/leftChordH (leftNome t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hlim := (leftKappa_pow_exp_tendsto_zero n hc).div
    leftChordH_mul_exp_kappa_tendsto_two (by norm_num : (2 : ℝ) ≠ 0)
  simp only [zero_div] at hlim
  apply hlim.congr
  intro t
  simp only [Pi.div_apply,Real.exp_neg]
  ring

noncomputable def leftChordAsymptoticRemainder (κ h : ℝ) : ℝ :=
  4/κ+10*κ^3*h^2+(κ+1)*Real.exp (-κ)+2*κ^2*(1+2*κ)*h^4+
    (4*κ^2+2*κ^3)*Real.exp (-κ)+
    2*κ^2*Real.exp (-κ)*Real.exp (-κ/2)/h+4*κ^3*Real.exp (-κ)*Real.exp (-κ/2)

theorem leftChordAsymptoticRemainder_eq_scaled {κ h : ℝ} (hκ : κ ≠ 0) (hh : h ≠ 0) :
    leftChordAsymptoticRemainder κ h = (2*κ^2*Real.exp (-κ))*
      (2*Real.exp κ/κ^3+5*κ*h^2*Real.exp κ+(κ+1)/(2*κ^2)+
        Real.exp κ*(1+2*κ)*h^4+(2+κ+Real.exp (-κ/2)*(1/h+2*κ))) := by
  unfold leftChordAsymptoticRemainder
  simp only [Real.exp_neg]
  field_simp [hκ,hh,Real.exp_ne_zero κ]
  ring

theorem leftChordAsymptoticRemainder_tendsto_zero :
    Tendsto (fun t : ℝ => leftChordAsymptoticRemainder (leftKappa t) (leftChordH (leftNome t)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => 4/leftKappa t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp leftKappa_tendsto_atTop).const_mul 4
  have h1 : Tendsto (fun t : ℝ => 10*(leftKappa t)^3*(leftChordH (leftNome t))^2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero,mul_assoc] using
      (leftKappa_pow_chordH_pow_tendsto_zero 3 2 (by decide)).const_mul 10
  have he (n : ℕ) : Tendsto (fun t : ℝ => (leftKappa t)^n*Real.exp (-leftKappa t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [neg_one_mul] using leftKappa_pow_exp_tendsto_zero n (by norm_num : (0 : ℝ) < 1)
  have h2 : Tendsto (fun t : ℝ => (leftKappa t+1)*Real.exp (-leftKappa t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (he 1).add (he 0)
    simp only [add_zero] at h
    apply h.congr
    intro t
    ring
  have h3 : Tendsto (fun t : ℝ => 2*(leftKappa t)^2*(1+2*leftKappa t)*
      (leftChordH (leftNome t))^4) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := ((leftKappa_pow_chordH_pow_tendsto_zero 2 4 (by decide)).const_mul 2).add
      ((leftKappa_pow_chordH_pow_tendsto_zero 3 4 (by decide)).const_mul 4)
    simp only [mul_zero,add_zero] at h
    apply h.congr
    intro t
    ring
  have h4 : Tendsto (fun t : ℝ => (4*(leftKappa t)^2+2*(leftKappa t)^3)*Real.exp (-leftKappa t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := ((he 2).const_mul 4).add ((he 3).const_mul 2)
    simp only [mul_zero,add_zero] at h
    apply h.congr
    intro t
    ring
  have h5 : Tendsto (fun t : ℝ => 2*(leftKappa t)^2*Real.exp (-leftKappa t)*
      Real.exp (-leftKappa t/2)/leftChordH (leftNome t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (leftKappa_pow_exp_over_chordH_tendsto_zero 2 (by norm_num : (0 : ℝ) < 1/2)).const_mul 2
    simp only [mul_zero] at h
    apply h.congr
    intro t
    rw [show -(1/2 : ℝ)*leftKappa t = -leftKappa t/2 by ring]
    ring
  have h6 : Tendsto (fun t : ℝ => 4*(leftKappa t)^3*Real.exp (-leftKappa t)*Real.exp (-leftKappa t/2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (leftKappa_pow_exp_tendsto_zero 3 (by norm_num : (0 : ℝ) < 3/2)).const_mul 4
    simp only [mul_zero] at h
    apply h.congr
    intro t
    rw [show -(3/2 : ℝ)*leftKappa t = -leftKappa t+(-leftKappa t/2) by ring,Real.exp_add]
    ring
  simpa only [leftChordAsymptoticRemainder,add_zero] using
    (((((h0.add h1).add h2).add h3).add h4).add h5).add h6

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftChordAsymptoticRemainder_tendsto_zero
