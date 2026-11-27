import TwoAxisHelicoid.PuncturePrimitiveResidue
import TwoAxisHelicoid.PolynomialHeightMeromorphic
import Mathlib.Analysis.Calculus.LogDeriv

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology

/-- A nowhere vanishing holomorphic function on a punctured disk is
a single integer power times the exponential of a single-valued
holomorphic function. The integer follows from the actual period on
the logarithmic cover. -/
theorem punctured_holomorphic_unit_factor {g : ℂ → ℂ} {r : ℝ} (hr : 0<r)
    (reg : ∀ z : ℂ, 0<‖z‖ → ‖z‖<r → AnalyticAt ℂ g z ∧ g z≠0) :
    ∃ (n : ℤ) (F : ℂ → ℂ), ∀ z : ℂ, 0<‖z‖ → ‖z‖<r →
      HasDerivAt F (logDeriv g z-(n:ℂ)/z) z ∧ g z=z^n*exp (F z) := by
  obtain ⟨c,H,dH⟩ := puncture_primitive_modulo_log (f := logDeriv g) hr (fun z n s =>
    ((reg _ n s).1.deriv.differentiableAt.div (reg _ n s).1.differentiableAt (reg _ n s).2))
  let V := {w : ℂ | w.re<Real.log r}
  have op : IsOpen V := isOpen_lt continuous_re continuous_const
  have conn : IsPreconnected V := (convex_halfSpace_re_lt (Real.log r)).isPreconnected
  have sz (w : ℂ) (hw : w∈V) : ‖exp w‖<r := by rw [norm_exp,← Real.exp_log hr]; exact Real.exp_lt_exp.mpr hw
  have nz (w : ℂ) : 0<‖exp w‖ := norm_pos_iff.mpr (exp_ne_zero _)
  let A := fun w : ℂ => g (exp w)*exp (-H (exp w)-c*w)
  have D (w : ℂ) (hw : w∈V) : HasDerivAt A 0 w := by
    have he := Complex.hasDerivAt_exp w
    have g' := (reg _ (nz w) (sz w hw)).1.differentiableAt.hasDerivAt.comp w he
    have h' := (dH _ (nz w) (sz w hw)).comp w he
    have v := g'.mul ((h'.neg.sub ((hasDerivAt_id w).const_mul c)).cexp)
    convert v using 1
    · rfl
    · change 0=deriv g (exp w)*exp w*exp (-H (exp w)-c*w)+g (exp w)*
        (exp (-H (exp w)-c*w)*(-((logDeriv g (exp w)-c/exp w)*exp w)-c*1))
      rw [logDeriv_apply]
      field_simp [(reg _ (nz w) (sz w hw)).2,exp_ne_zero w]
      ring
  let b : ℂ := ((Real.log r-1:ℝ):ℂ)
  have base : b∈V := by change Real.log r-1<Real.log r; linarith
  have eq (w : ℂ) (hw : w∈V) : A w=A b :=
    op.is_const_of_deriv_eq_zero (𝕜 := ℂ) conn (fun z hz => (D z hz).differentiableAt.differentiableWithinAt) (fun z hz => (D z hz).deriv) hw base
  let T : ℂ := 2*Real.pi*I
  have nT : T≠0 := mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have add : b+T∈V := by simpa [V,T,Complex.mul_re,Complex.mul_im] using base
  have per := eq _ add
  change g (exp (b+T))*exp (-H (exp (b+T))-c*(b+T))=g (exp b)*exp (-H (exp b)-c*b) at per
  rw [show exp (b+T)=exp b from exp_periodic _,show -H (exp b)-c*(b+T)= -H (exp b)-c*b+ -(c*T) by ring,exp_add,← mul_assoc] at per
  have unit : exp (-(c*T))=1 := (mul_eq_left₀ (mul_ne_zero (reg _ (nz b) (sz b base)).2 (exp_ne_zero _))).mp per
  obtain ⟨m,hm⟩ := Complex.exp_eq_one_iff.mp unit
  have cv : c=((-m:ℤ):ℂ) := by
    apply mul_right_cancel₀ nT
    push_cast
    change -(c*T)=(m:ℂ)*T at hm
    linear_combination -hm
  let C := A b
  have nc : C≠0 := mul_ne_zero (reg _ (nz b) (sz b base)).2 (exp_ne_zero _)
  refine ⟨-m,fun z => H z+log C,?_⟩
  intro z n s
  refine ⟨cv ▸ (dH z n s).add_const _,?_⟩
  have ne := norm_pos_iff.mp n
  have point : log z∈V := by change (log z).re<Real.log r; rw [log_re]; exact Real.log_lt_log n s
  have val := eq (log z) point
  change g (exp (log z))*exp (-H (exp (log z))-c*log z)=C at val
  rw [exp_log ne] at val
  calc
    g z = C*exp (H z+c*log z) := by
      rw [← val,mul_assoc,← exp_add,show -H z-c*log z+(H z+c*log z)=0 by ring,exp_zero,mul_one]
    _ = z^(-m)*exp (H z+log C) := by
      rw [exp_add,cv,exp_int_mul,exp_log ne,exp_add,exp_log nc]
      ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_holomorphic_unit_factor
