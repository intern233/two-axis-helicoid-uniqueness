import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Set

theorem exists_second_order_mean {f f₁ f₂ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (f₁ x) x)
    (hdd : ∀ x ∈ Icc a b, HasDerivAt f₁ (f₂ x) x) (hb : f₁ b = 0) :
    ∃ c ∈ Ioo a b, f a - f b = f₂ c / 2 * (a-b)^2 := by
  let R := (f a-f b)/(a-b)^2
  let F := fun x => f x-f b-R*(x-b)^2
  let F₁ := fun x => f₁ x-2*R*(x-b)
  have hn : a-b ≠ 0 := sub_ne_zero.mpr hab.ne
  have hF (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt F (F₁ x) x := by
    have h := ((hd x hx).sub_const (f b)).sub
      ((((hasDerivAt_id x).sub_const b).pow 2).const_mul R)
    convert h using 1
    · rfl
    · dsimp [F₁]
      ring
  have hF₁ (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt F₁ (f₂ x-2*R) x := by
    have h := (hdd x hx).sub (((hasDerivAt_id x).sub_const b).const_mul (2*R))
    convert h using 1
    · rfl
    · simp only [mul_one]
  have he : F a = F b := by
    dsimp [F,R]
    field_simp [hn]
    ring
  obtain ⟨d,hdm,hde⟩ := exists_hasDerivAt_eq_zero hab
    (fun x hx => (hF x hx).continuousAt.continuousWithinAt) he
    (fun x hx => hF x ⟨hx.1.le,hx.2.le⟩)
  have hde' : F₁ d = F₁ b := by simpa only [F₁,sub_self,mul_zero,hb] using hde
  obtain ⟨c,hcm,hce⟩ := exists_hasDerivAt_eq_zero hdm.2
    (fun x hx => (hF₁ x ⟨hdm.1.le.trans hx.1,hx.2⟩).continuousAt.continuousWithinAt) hde'
    (fun x hx => hF₁ x ⟨(hdm.1.trans hx.1).le,hx.2.le⟩)
  refine ⟨c,⟨hdm.1.trans hcm.1,hcm.2⟩,?_⟩
  dsimp [R] at hce
  field_simp [hn] at hce
  nlinarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exists_second_order_mean
