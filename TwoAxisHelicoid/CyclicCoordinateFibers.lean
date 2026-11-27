import Mathlib.Analysis.Complex.Periodic
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex Set Function

/-- A coordinate translating under one generator translates under each
integer winding, with the sign fixed by the generator. -/
theorem complex_coordinate_integer_translations {H : ℂ → ℂ} {t c : ℂ} (ht : t≠0)
    (step : ∀ z, H (z+t)=H z+c) (z : ℂ) (n : ℤ) :
    H (z+(n:ℂ)*t)=H z+(n:ℂ)*c := by
  let k := c/t
  have kt : k*t=c := div_mul_cancel₀ _ ht
  let A := fun w => H w-k*w
  have per : Periodic A t := fun w => by dsimp [A]; rw [step,mul_add,kt]; ring
  have h := per.int_mul n z
  change H (z+(n:ℂ)*t)-k*(z+(n:ℂ)*t)=H z-k*z at h
  calc
    H (z+(n:ℂ)*t) = H z+(n:ℂ)*(k*t) := by linear_combination h
    _ = _ := by rw [kt]

/-- Passing an injective developing coordinate through the exponential
identifies exactly the original deck translates. -/
theorem cyclic_coordinate_same_fibers {X : Type*} (e : ℂ ≃ X) {t c : ℂ} (ht : t≠0)
    (A : X → ℂ) (inj : Injective A) (step : ∀ z, A (e (z+t))=A (e z)+c)
    (F : ℂ → ℂ) (fibers : ∀ v w, F v=F w ↔ ∃ n : ℤ, v=w+(n:ℂ)*c) (x y : X) :
    F (A x)=F (A y) ↔ ∃ n : ℤ, e.symm x=e.symm y+(n:ℂ)*t := by
  have shift := complex_coordinate_integer_translations (H := A ∘ e) ht step
  rw [fibers]
  constructor
  · rintro ⟨n,h⟩
    refine ⟨n,e.injective (inj ?_)⟩
    rw [e.apply_symm_apply]
    exact h.trans (by simpa only [Function.comp_apply,e.apply_symm_apply] using (shift (e.symm y) n).symm)
  · rintro ⟨n,h⟩
    refine ⟨n,?_⟩
    have a := congrArg (A ∘ e) h
    rw [shift] at a
    simpa only [Function.comp_apply,e.apply_symm_apply] using a

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.cyclic_coordinate_same_fibers
