import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex MeasureTheory Set
open scoped Interval

/-- Moving one complete horizontal period within a holomorphic strip
does not change its complex integral. Both vertical edges cancel. -/
theorem periodic_horizontal_integral_shift {f : ℂ → ℂ} (per : Function.Periodic f 1)
    (y : ℝ) (hol : ∀ z : ℂ, z.im∈uIcc 0 y → DifferentiableAt ℂ f z) :
    (∫ x : ℝ in 0..1,f (x:ℂ))=∫ x : ℝ in 0..1,f ((x:ℂ)+(y:ℂ)*I) := by
  let endpt : ℂ := ⟨1,y⟩
  have rectangle := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f 0 endpt
    (fun z hz => (hol z (by simpa only [Set.mem_preimage,Complex.zero_im,endpt] using hz.2)).differentiableWithinAt)
  have vert (b : ℝ) : f (1+(b:ℂ)*I)=f ((b:ℂ)*I) := by
    rw [add_comm 1]
    exact per _
  simp only [Complex.zero_re,Complex.zero_im,endpt,Complex.ofReal_zero,zero_mul,
    add_zero,Complex.ofReal_one,zero_add,vert] at rectangle
  linear_combination rectangle

/-- The integral defining a unit-period Fourier coefficient, written in
the complex coordinate so a contour displacement can be certified. -/
noncomputable def stripFourierCoefficient (f : ℂ → ℂ) (n : ℤ) : ℂ :=
  ∫ x : ℝ in 0..1,Complex.exp ((-(n:ℂ))*(2*Real.pi*I)*(x:ℂ))*f (x:ℂ)

theorem stripFourierCoefficient_displaced_bound {f : ℂ → ℂ} (per : Function.Periodic f 1)
    (n : ℤ) (y M : ℝ) (hol : ∀ z : ℂ, z.im∈uIcc 0 y → DifferentiableAt ℂ f z)
    (bound : ∀ x : ℝ, ‖f ((x:ℂ)+(y:ℂ)*I)‖≤M) :
    ‖stripFourierCoefficient f n‖≤Real.exp ((n:ℝ)*(2*Real.pi)*y)*M := by
  let c : ℂ := -(n:ℂ)*(2*Real.pi*I)
  let g := fun z : ℂ => Complex.exp (c*z)*f z
  have ec : Complex.exp c=1 := by
    simpa only [c,Int.cast_neg] using Complex.exp_int_mul_two_pi_mul_I (-n)
  have gp : Function.Periodic g 1 := by
    intro z
    dsimp only [g]
    rw [mul_add,mul_one,Complex.exp_add,ec,mul_one,per]
  have shift := periodic_horizontal_integral_shift gp y
    (fun z h => (((differentiableAt_const c).mul differentiableAt_id).cexp.mul (hol z h)))
  change ‖∫ x : ℝ in 0..1,g (x:ℂ)‖≤_
  rw [shift]
  have point (x : ℝ) : ‖g ((x:ℂ)+(y:ℂ)*I)‖≤Real.exp ((n:ℝ)*(2*Real.pi)*y)*M := by
    dsimp only [g]
    rw [norm_mul,Complex.norm_exp]
    have realEq : (c*((x:ℂ)+(y:ℂ)*I)).re=(n:ℝ)*(2*Real.pi)*y := by
      simp [c,Complex.mul_re,Complex.mul_im]
    rw [realEq]
    exact mul_le_mul_of_nonneg_left (bound x) (Real.exp_pos _).le
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=1) (fun x _ => point x)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.periodic_horizontal_integral_shift
#print axioms TwoAxisHelicoid.stripFourierCoefficient_displaced_bound
