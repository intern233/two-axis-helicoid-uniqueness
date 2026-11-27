import TwoAxisHelicoid.HelicoidAxisRadialTangent
import TwoAxisHelicoid.GaussMultiplierContinuation

namespace TwoAxisHelicoid
open Complex Set Matrix
open scoped ComplexConjugate Topology

theorem null_gauss_normal_annihilates {p : Fin 3 → ℂ} (hp : ComplexNull p) (hn : p 2≠0) (w : ℂ) :
    let g := nullGauss p
    (2*g.re)*nullRealDerivative p w 0+(2*g.im)*nullRealDerivative p w 1+
      (‖g‖^2-1)*nullRealDerivative p w 2=0 := by
  let g := nullGauss p
  have nz : g≠0 := nullGauss_ne_zero_of_height hp hn
  obtain ⟨plus,minus⟩ := nullGauss_mul_height hp hn
  change g*p 2= -(p 0+I*p 1) at plus
  change g⁻¹*p 2=p 0-I*p 1 at minus
  have realpart : 2*(g.re:ℂ)=g+conj g := by apply Complex.ext <;> simp; ring
  have imagpart : 2*(g.im:ℂ)=(g-conj g)*(-I) := by apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]; ring
  have eq : (2*(g.re:ℂ))*p 0+(2*(g.im:ℂ))*p 1+((‖g‖^2:ℝ)-1:ℂ)*p 2=0 := by
    rw [realpart,imagpart,← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
    calc
      _ = conj g*(p 0+I*p 1)+g*(p 0-I*p 1)+(conj g*g-1)*p 2 := by ring
      _ = 0 := by rw [show p 0+I*p 1= -(g*p 2) by linear_combination plus,← minus]; field_simp [nz]; ring
  have e := congrArg (fun a : ℂ => (w*a).re) eq
  change (2*g.re)*(w*p 0).re+(2*g.im)*(w*p 1).re+(‖g‖^2-1)*(w*p 2).re=0
  simp only [mul_add,Complex.add_re,mul_zero,Complex.zero_re] at e
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.sub_re,Complex.sub_im,
    Complex.one_re,Complex.one_im] at e ⊢
  norm_num at e
  linear_combination e

/-- Along the center line of the normal graph its radial and angular
tangents, evaluated against the true Gauss normal, force avoidance of
the radial meridian and a two-sided bound on the Gauss modulus. -/
theorem center_ruling_gauss_phase_and_modulus {g : ℂ} (ng : g≠0) {s u v θ : ℝ}
    (height : |s|≤1/2) (radialSlope : |u|≤1) (angularSlope : |v|≤1)
    (radial : 2*(g.re*Real.cos θ+g.im*Real.sin θ)+u*(2*(g.re*Real.sin θ-g.im*Real.cos θ))+s*(‖g‖^2-1)=0)
    (angular : s*(2*(g.re*Real.cos θ+g.im*Real.sin θ))+v*(2*(g.re*Real.sin θ-g.im*Real.cos θ))+(‖g‖^2-1)=0) :
    (∀ a : ℝ, g≠(a:ℂ)*Complex.exp ((θ:ℂ)*I)) ∧ 1/10≤‖g‖ ∧ ‖g‖≤10 := by
  let b := 2*(g.re*Real.sin θ-g.im*Real.cos θ)
  have proj : (1-s^2)*(‖g‖^2-1)=(s*u-v)*b := by dsimp [b]; linear_combination angular-s*radial
  have square : s^2≤(1/2:ℝ)^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg s) (by norm_num : (0:ℝ)≤1/2)).mpr height
  have low : 3/4≤1-s^2 := by linarith
  have phase (a : ℝ) (bad : g=(a:ℂ)*exp ((θ:ℂ)*I)) : False := by
    have re : g.re=a*Real.cos θ := by rw [bad,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.exp_ofReal_mul_I_re]; ring
    have im : g.im=a*Real.sin θ := by rw [bad,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.exp_ofReal_mul_I_im]; ring
    have bz : b=0 := by dsimp [b]; rw [re,im]; ring
    rw [bz,mul_zero] at proj
    have vertical := (mul_eq_zero.mp proj).resolve_left (by linarith)
    rw [re,im,vertical] at radial
    have zero : a=0 := by nlinarith [Real.sin_sq_add_cos_sq θ,congrArg (a*·) (Real.sin_sq_add_cos_sq θ)]
    exact ng (by rw [bad,zero,Complex.ofReal_zero,zero_mul])
  have tangent : |b|≤4*‖g‖ := by
    calc
      |b| = 2*|g.re*Real.sin θ-g.im*Real.cos θ| := by dsimp [b]; rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      _ ≤ 2*(|g.re*Real.sin θ|+|g.im*Real.cos θ|) := mul_le_mul_of_nonneg_left (by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (g.re*Real.sin θ) (-(g.im*Real.cos θ))) (by norm_num)
      _ ≤ 4*‖g‖ := by
        rw [abs_mul,abs_mul]
        have x := mul_le_mul (Complex.abs_re_le_norm g) (Real.abs_sin_le_one θ) (abs_nonneg _) (norm_nonneg g)
        have y := mul_le_mul (Complex.abs_im_le_norm g) (Real.abs_cos_le_one θ) (abs_nonneg _) (norm_nonneg g)
        linarith
  have scale : |s*u-v|≤3/2 := by
    apply (show |s*u-v|≤|s*u|+|v| by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (s*u) (-v)).trans
    rw [abs_mul]
    linarith [mul_le_mul height radialSlope (abs_nonneg u) (by norm_num : (0:ℝ)≤1/2)]
  have normEq := congrArg abs proj
  rw [abs_mul,abs_mul,abs_of_pos (show 0<1-s^2 by linarith)] at normEq
  have estimate : |‖g‖^2-1|≤8*‖g‖ := by
    nlinarith [mul_le_mul_of_nonneg_right low (abs_nonneg (‖g‖^2-1)),mul_le_mul scale tangent (abs_nonneg _) (by norm_num : (0:ℝ)≤3/2)]
  obtain ⟨lo,hi⟩ := abs_le.mp estimate
  refine ⟨phase,?_,?_⟩
  · by_contra! bad
    nlinarith [mul_le_mul_of_nonneg_left bad.le (norm_nonneg g)]
  · by_contra! bad
    nlinarith [mul_pos (show 0<‖g‖-10 by linarith) (show 0<‖g‖+1 by positivity)]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.null_gauss_normal_annihilates
#print axioms TwoAxisHelicoid.center_ruling_gauss_phase_and_modulus
