import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

theorem equal_logarithmic_derivatives_constant_ratio {s : Set ℂ}
    (hs : IsOpen s) (hc : IsConnected s) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ s, DifferentiableAt ℂ f z)
    (hg : ∀ z ∈ s, DifferentiableAt ℂ g z)
    (hfn : ∀ z ∈ s, f z ≠ 0) (hgn : ∀ z ∈ s, g z ≠ 0)
    (hlog : ∀ z ∈ s, deriv g z/g z = deriv f z/f z) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z ∈ s, g z = c*f z := by
  have hd (z : ℂ) (hz : z ∈ s) : HasDerivAt (fun w => g w/f w) 0 z := by
    have he := (div_eq_div_iff (hgn z hz) (hfn z hz)).mp (hlog z hz)
    convert (hg z hz).hasDerivAt.div (hf z hz).hasDerivAt (hfn z hz) using 1
    rw [mul_comm (g z),he,sub_self,zero_div]
  obtain ⟨c,hc'⟩ := hs.exists_is_const_of_deriv_eq_zero hc.2
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv)
  have he (z : ℂ) (hz : z ∈ s) : g z = c*f z :=
    (div_eq_iff (hfn z hz)).mp (hc' z hz)
  refine ⟨c,?_,he⟩
  obtain ⟨z,hz⟩ := hc.1
  intro h
  exact hgn z hz (by simpa [h] using he z hz)

/-- The two real horizontal closing equations are exactly the conjugate
relation between the periods of `g dh` and `g⁻¹ dh`. -/
theorem horizontal_period_closure_iff (A B : ℂ) :
    (((B-A)/2).re = 0 ∧ (I*(B+A)/2).re = 0) ↔ B = conj A := by
  constructor
  · intro h
    apply Complex.ext
    · norm_num [Complex.div_re,Complex.normSq_apply] at h ⊢
      linarith [h.1]
    · norm_num [Complex.div_re,Complex.normSq_apply,Complex.mul_re] at h ⊢
      linarith [h.2]
  · rintro rfl
    constructor <;> simp [Complex.mul_re]

theorem horizontal_closed_flux (A B : ℂ) (h : B = conj A) :
    (((B-A)/2).im,(I*(B+A)/2).im) = (-A.im,A.re) := by
  subst B
  ext <;> simp [Complex.mul_im]
  ring

/-- One nonzero horizontal period rules out every non-unit amplitude in
the Lopez--Ros multiplication. The nonzero-period hypothesis is explicit. -/
theorem multiplier_norm_one_of_closed_period {A B c : ℂ}
    (hA : A ≠ 0) (hc : c ≠ 0) (hfirst : B = conj A)
    (hsecond : c⁻¹*B = conj (c*A)) : ‖c‖ = 1 := by
  have hB : B ≠ 0 := by simpa [hfirst] using hA
  have he : B = (c*conj c)*B := by
    have h := congrArg (fun z : ℂ => c*z) hsecond
    rw [map_mul,← hfirst] at h
    simpa only [← mul_assoc,mul_inv_cancel₀ hc,one_mul] using h
  have hcc : c*conj c = 1 := by
    apply mul_right_cancel₀ hB
    simpa only [one_mul] using he.symm
  have hn := congrArg (fun z : ℂ => ‖z‖) hcc
  rw [norm_mul,Complex.norm_conj,norm_one] at hn
  nlinarith [norm_nonneg c]

theorem multiplier_is_phase_of_closed_period {A B c : ℂ}
    (hA : A ≠ 0) (hc : c ≠ 0) (hfirst : B = conj A)
    (hsecond : c⁻¹*B = conj (c*A)) :
    ∃ θ : ℝ, c = Complex.exp ((θ : ℂ)*I) := by
  refine ⟨Complex.arg c,?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I c
  rw [multiplier_norm_one_of_closed_period hA hc hfirst hsecond,
    Complex.ofReal_one,one_mul] at h
  exact h.symm

theorem equal_logarithmic_derivatives_closed_multiplier {s : Set ℂ}
    (hs : IsOpen s) (hsC : IsConnected s) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ s, DifferentiableAt ℂ f z)
    (hg : ∀ z ∈ s, DifferentiableAt ℂ g z)
    (hfn : ∀ z ∈ s, f z ≠ 0) (hgn : ∀ z ∈ s, g z ≠ 0)
    (hlog : ∀ z ∈ s, deriv g z/g z = deriv f z/f z)
    {A B : ℂ} (hA : A ≠ 0) (hfirst : B = conj A)
    (hsecond : ∀ c : ℂ, (∀ z ∈ s, g z = c*f z) → c⁻¹*B = conj (c*A)) :
    ∃ θ : ℝ, ∀ z ∈ s, g z = Complex.exp ((θ : ℂ)*I)*f z := by
  obtain ⟨c,hc,he⟩ := equal_logarithmic_derivatives_constant_ratio hs hsC hf hg hfn hgn hlog
  obtain ⟨θ,hθ⟩ := multiplier_is_phase_of_closed_period hA hc hfirst (hsecond c he)
  exact ⟨θ,fun z hz => hθ ▸ he z hz⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.equal_logarithmic_derivatives_constant_ratio
#print axioms TwoAxisHelicoid.equal_logarithmic_derivatives_closed_multiplier
