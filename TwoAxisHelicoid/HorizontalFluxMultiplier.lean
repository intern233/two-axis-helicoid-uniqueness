import TwoAxisHelicoid.GaussMultiplierRigidity
import TwoAxisHelicoid.NullGaussAlgebra
import TwoAxisHelicoid.PiecewiseComplexPeriods

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped ComplexConjugate

/-- The integral of a complex linear combination of coefficients on a
piecewise C¹ curve, proved with the actual velocities of all pieces. -/
theorem PiecewiseComplexPath.integral_linear {U : Set ℂ} {x y : ℂ}
    (γ : PiecewiseComplexPath U x y) (k l : ℂ) {f g h : ℂ → ℂ}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (he : ∀ z ∈ U, h z = k*f z + l*g z) :
    γ.integral h = k*γ.integral f + l*γ.integral g := by
  induction γ with
  | refl => simp [PiecewiseComplexPath.integral]
  | trans p q ih₁ ih₂ => simp only [PiecewiseComplexPath.integral,ih₁,ih₂]; ring
  | arc a =>
    change a.integral h = k*a.integral f + l*a.integral g
    have hF : ContinuousOn (fun s => a.velocity s*f (a.curve s)) (Icc a.left a.right) := a.continuous_velocity.mul (hf.comp a.continuous_curve a.stays)
    have hG : ContinuousOn (fun s => a.velocity s*g (a.curve s)) (Icc a.left a.right) := a.continuous_velocity.mul (hg.comp a.continuous_curve a.stays)
    unfold ComplexPeriodArc.integral
    calc
      _ = ∫ s in a.left..a.right, k*(a.velocity s*f (a.curve s))+l*(a.velocity s*g (a.curve s)) := by
        apply intervalIntegral.integral_congr
        intro s hs
        dsimp only
        rw [he _ (a.stays (by simpa only [uIcc_of_le a.ordered] using hs))]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add ((hF.const_mul k).intervalIntegrable_of_Icc a.ordered)
          ((hG.const_mul l).intervalIntegrable_of_Icc a.ordered),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]

private theorem horizontal_closed_pair {x y : ℂ} (hx : x.re = 0) (hy : y.re = 0) :
    x-I*y = conj (-(x+I*y)) := by
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,hx,hy]

private theorem positive_component_nonzero {x y : ℂ} (hx : x.re = 0) (hy : y.re = 0)
    (h : x.im ≠ 0 ∨ y.im ≠ 0) : -(x+I*y) ≠ 0 := by
  intro e
  have h₁ := congrArg Complex.re e
  have h₂ := congrArg Complex.im e
  simp [Complex.mul_re,Complex.mul_im,hx,hy] at h₁ h₂
  exact h.elim (fun h => h h₂) (fun h => h h₁)

/-- A single nonvertical flux of the actual spatial immersion forces the
global Gauss multiplier to have norm one. The loop may pass through any
ordinary zero or pole of the Gauss map because its coordinate forms are
regular there. -/
theorem unit_multiplier_of_horizontal_flux {U : Set ℂ} {x y : ℂ} (γ : PiecewiseComplexPath U x y)
    {p q : ℂ → Fin 3 → ℂ} (hp : ∀ j, ContinuousOn (fun z => p z j) U)
    (hq : ∀ j, ContinuousOn (fun z => q z j) U) {c : ℂ} (hc : c ≠ 0)
    (he : ∀ z ∈ U, nullHorizontalPlus (q z) = c*nullHorizontalPlus (p z) ∧
      nullHorizontalMinus (q z) = c⁻¹*nullHorizontalMinus (p z))
    (hP : ∀ j, (γ.integral (fun z => p z j)).re = 0)
    (hQ : ∀ j, (γ.integral (fun z => q z j)).re = 0)
    (hflux : (γ.integral (fun z => p z 0)).im ≠ 0 ∨ (γ.integral (fun z => p z 1)).im ≠ 0) :
    ‖c‖ = 1 := by
  let P := fun j => γ.integral (fun z => p z j)
  let Q := fun j => γ.integral (fun z => q z j)
  have hplus : Q 0+I*Q 1 = c*(P 0+I*P 1) := by
    have hL := γ.integral_linear 1 I (hq 0) (hq 1) (h := nullHorizontalPlus ∘ q)
      (fun _ _ => by simp [nullHorizontalPlus])
    have hR := γ.integral_linear c (c*I) (hp 0) (hp 1) (h := nullHorizontalPlus ∘ q)
      (fun z hz => by change nullHorizontalPlus (q z) = _; rw [(he z hz).1]; unfold nullHorizontalPlus; ring)
    dsimp [Q,P]
    rw [one_mul] at hL
    linear_combination hL.symm.trans hR
  have hminus : Q 0-I*Q 1 = c⁻¹*(P 0-I*P 1) := by
    have hL := γ.integral_linear 1 (-I) (hq 0) (hq 1) (h := nullHorizontalMinus ∘ q)
      (fun _ _ => by simp [nullHorizontalMinus,sub_eq_add_neg])
    have hR := γ.integral_linear c⁻¹ (-(c⁻¹*I)) (hp 0) (hp 1) (h := nullHorizontalMinus ∘ q)
      (fun z hz => by change nullHorizontalMinus (q z) = _; rw [(he z hz).2]; unfold nullHorizontalMinus; ring)
    dsimp [Q,P]
    linear_combination hL.symm.trans hR
  apply multiplier_norm_one_of_closed_period (positive_component_nonzero (hP 0) (hP 1) hflux) hc
    (horizontal_closed_pair (hP 0) (hP 1))
  rw [← hminus,mul_neg,← hplus]
  exact horizontal_closed_pair (hQ 0) (hQ 1)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.unit_multiplier_of_horizontal_flux
