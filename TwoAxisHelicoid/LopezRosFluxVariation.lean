import TwoAxisHelicoid.HorizontalFluxMultiplier
import Mathlib.Analysis.Calculus.Deriv.Star

namespace TwoAxisHelicoid
open Complex Set

noncomputable def lopezRosAverage (k : ℂ) : ℂ := (k+k⁻¹)/2
noncomputable def lopezRosSkew (k : ℂ) : ℂ := I*(k-k⁻¹)/2
noncomputable def lopezRosHorizontal (k x y : ℂ) : Fin 2 → ℂ :=
  ![lopezRosAverage k*x+lopezRosSkew k*y,lopezRosAverage k*y-lopezRosSkew k*x]

/-- This smooth-at-the-vertical-points coordinate formula is the López–Ros
Gauss multiplier: the positive and negative horizontal coefficients scale
by reciprocal factors. -/
theorem lopezRosHorizontal_characteristic (k x y : ℂ) :
    lopezRosHorizontal k x y 0 + I*lopezRosHorizontal k x y 1 = k*(x+I*y) ∧
    lopezRosHorizontal k x y 0 - I*lopezRosHorizontal k x y 1 = k⁻¹*(x-I*y) := by
  constructor <;> simp [lopezRosHorizontal,lopezRosAverage,lopezRosSkew] <;>
    ring_nf <;> simp only [I_sq] <;> ring

theorem PiecewiseComplexPath.integral_lopezRosHorizontal {U : Set ℂ} {u v : ℂ}
    (γ : PiecewiseComplexPath U u v) {p : ℂ → Fin 3 → ℂ}
    (h₀ : ContinuousOn (fun z => p z 0) U) (h₁ : ContinuousOn (fun z => p z 1) U)
    (k : ℂ) (j : Fin 2) :
    γ.integral (fun z => lopezRosHorizontal k (p z 0) (p z 1) j) =
      lopezRosHorizontal k (γ.integral (fun z => p z 0)) (γ.integral (fun z => p z 1)) j := by
  fin_cases j
  · exact γ.integral_linear _ _ h₀ h₁ (fun _ _ => rfl)
  · change γ.integral (fun z => lopezRosHorizontal k (p z 0) (p z 1) 1) = lopezRosAverage k * γ.integral (fun z => p z 1) - lopezRosSkew k * γ.integral (fun z => p z 0)
    simpa only [sub_eq_add_neg,neg_mul] using
      γ.integral_linear (lopezRosAverage k) (-lopezRosSkew k) h₁ h₀ (h := fun z => lopezRosHorizontal k (p z 0) (p z 1) 1)
        (fun z _ => by simp [lopezRosHorizontal,sub_eq_add_neg])

/-- For one actual loop, infinitesimal real closure of both horizontal
components forces a pure phase velocity as soon as its original horizontal
flux is nonzero. Closure is only required to first order at the base. -/
theorem lopezRos_horizontal_real_velocity {k : ℝ → ℂ} {d x y : ℂ}
    (hk : HasDerivAt k d 0) (hk0 : k 0 = 1) (hx : x.re = 0) (hy : y.re = 0)
    (hf : x.im ≠ 0 ∨ y.im ≠ 0)
    (hclose : ∀ j : Fin 2, HasDerivAt (fun s => (lopezRosHorizontal (k s) x y j).re) 0 0) : d.re = 0 := by
  have hInv : HasDerivAt (fun s => (k s)⁻¹) (-d) 0 := by
    simpa only [hk0,one_pow,div_one] using! hk.inv (by rw [hk0]; exact one_ne_zero)
  have hA : HasDerivAt (fun s => lopezRosAverage (k s)) 0 0 := by
    simpa only [lopezRosAverage,add_neg_cancel,zero_div] using! (hk.add hInv).div_const 2
  have hB : HasDerivAt (fun s => lopezRosSkew (k s)) (I*d) 0 := by
    convert ((hk.sub hInv).const_mul I).div_const 2 using 1
    · rfl
    · ring
  have h₀ := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 ((hA.mul_const x).add (hB.mul_const y))
  have h₁ := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 ((hA.mul_const y).sub (hB.mul_const x))
  have h₀' := h₀.unique (hclose 0)
  have h₁' := h₁.unique (hclose 1)
  simp [Complex.mul_re,Complex.mul_im,hx,hy] at h₀' h₁'
  rcases hf with h | h
  · exact h₁'.resolve_right h
  · exact h₀'.resolve_right h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lopezRos_horizontal_real_velocity
