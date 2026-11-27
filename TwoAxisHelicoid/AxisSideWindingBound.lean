import TwoAxisHelicoid.AxisWindingRestriction

namespace TwoAxisHelicoid
open Set

/-- On an interval on which a continuous phase starts from zero and its
sine has one weak sign, the phase always stays between −2π and 2π.
The sign need only be known on the open interval. -/
theorem phase_bound_of_sine_one_sign {l u c : ℝ} (hlu : l < u) {f : ℝ → ℝ}
    (hf : Continuous f) (hc : c ∈ Icc l u) (hfc : f c = 0)
    (hs : (∀ x ∈ Ioo l u, 0 ≤ Real.sin (f x)) ∨ (∀ x ∈ Ioo l u, Real.sin (f x) ≤ 0)) :
    MapsTo f (Icc l u) (Icc (-2*Real.pi) (2*Real.pi)) := by
  have hcont : Continuous (fun x => Real.sin (f x)) := Real.continuous_sin.comp hf
  have hsign (x y : ℝ) (hx : x ∈ Icc l u) (hy : y ∈ Icc l u) :
      0 ≤ Real.sin (f x)*Real.sin (f y) := by
    rcases hs with h | h
    · have hcl := closure_minimal h (isClosed_Ici.preimage hcont)
      rw [closure_Ioo hlu.ne] at hcl
      exact mul_nonneg (hcl hx) (hcl hy)
    · have hcl := closure_minimal h (isClosed_Iic.preimage hcont)
      rw [closure_Ioo hlu.ne] at hcl
      exact mul_nonneg_of_nonpos_of_nonpos (hcl hx) (hcl hy)
  intro x hx
  have hbetween {z : ℝ} (h : z ∈ Icc (f x) 0 ∨ z ∈ Icc 0 (f x)) :
      ∃ y ∈ Icc l u, f y = z := by
    rcases h with h | h
    · exact isPreconnected_Icc.intermediate_value₂ hx hc hf.continuousOn
        (continuousOn_const (c := z)) h.1 (hfc ▸ h.2)
    · exact isPreconnected_Icc.intermediate_value₂ hc hx hf.continuousOn
        (continuousOn_const (c := z)) (hfc ▸ h.1) h.2
  have hsin : Real.sin (3*Real.pi/2) = -1 := by
    rw [show 3*Real.pi/2 = Real.pi/2+Real.pi by ring,Real.sin_add_pi,Real.sin_pi_div_two]
  constructor
  · by_contra! h
    obtain ⟨y,hy,hey⟩ := hbetween (z := -(Real.pi/2))
      (Or.inl ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩)
    obtain ⟨w,hw,hew⟩ := hbetween (z := -(3*Real.pi/2))
      (Or.inl ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩)
    have hh := hsign y w hy hw
    rw [hey,hew,Real.sin_neg,Real.sin_neg,Real.sin_pi_div_two,hsin] at hh
    norm_num at hh
  · by_contra! h
    obtain ⟨y,hy,hey⟩ := hbetween (z := Real.pi/2)
      (Or.inr ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩)
    obtain ⟨w,hw,hew⟩ := hbetween (z := 3*Real.pi/2)
      (Or.inr ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩)
    have hh := hsign y w hy hw
    rw [hey,hew,Real.sin_pi_div_two,hsin] at hh
    norm_num at hh

/-- The two open half-axes may lie on different sides. Each sign
separately suffices for the integer restriction; tangent coincidences
need not be excluded pointwise. -/
theorem integerAxisPhase_parameter_of_half_axis_signs {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ)
    (hl : (∀ y ∈ Ioo 0 t, 0 ≤ Real.sin (integerAxisPhase t a m y)) ∨
      (∀ y ∈ Ioo 0 t, Real.sin (integerAxisPhase t a m y) ≤ 0))
    (hr : (∀ y ∈ Ioo t (2*t), 0 ≤ Real.sin (integerAxisPhase t a m y)) ∨
      (∀ y ∈ Ioo t (2*t), Real.sin (integerAxisPhase t a m y) ≤ 0)) :
    m = 0 ∨ m = 1 := by
  have hf := integerAxisPhase_continuous ht ha m
  have hf0 := integerAxisPhase_midpoint t a m
  have h0 := phase_bound_of_sine_one_sign ht hf (right_mem_Icc.mpr ht.le) hf0 hl
    (left_mem_Icc.mpr ht.le)
  have hlr : t < 2*t := by linarith
  have h2 := phase_bound_of_sine_one_sign hlr hf (left_mem_Icc.mpr hlr.le) hf0 hr
    (right_mem_Icc.mpr hlr.le)
  have he := integerAxisPhase_total_increment ht ha m
  have hp : 0 < 4*Real.pi := by positivity
  have hmlo : (-1 : ℝ) < m := (lt_of_mul_lt_mul_left (a := 4*Real.pi) (by
    nlinarith [h2.1,h0.2,Real.pi_pos] : 4*Real.pi*(-1) < 4*Real.pi*m) hp.le)
  have hmhi : (m : ℝ) < 2 := (lt_of_mul_lt_mul_left (a := 4*Real.pi) (by
    nlinarith [h2.2,h0.1,Real.pi_pos] : 4*Real.pi*m < 4*Real.pi*2) hp.le)
  have h0Z : (-1 : ℤ) < m := by exact_mod_cast hmlo
  have h2Z : m < (2 : ℤ) := by exact_mod_cast hmhi
  omega

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.integerAxisPhase_parameter_of_half_axis_signs
