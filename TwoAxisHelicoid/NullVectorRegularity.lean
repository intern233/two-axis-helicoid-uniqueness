import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex

def ComplexNull (p : Fin 3 → ℂ) : Prop := (p 0)^2+(p 1)^2+(p 2)^2 = 0

noncomputable def nullMetric (p : Fin 3 → ℂ) : ℝ :=
  (p 0).re^2+(p 1).re^2+(p 2).re^2

theorem complexNull_real_identities {p : Fin 3 → ℂ} (hp : ComplexNull p) :
    nullMetric p = (p 0).im^2+(p 1).im^2+(p 2).im^2 ∧
    (p 0).re*(p 0).im+(p 1).re*(p 1).im+(p 2).re*(p 2).im = 0 := by
  have hr := congrArg Complex.re hp
  have hi := congrArg Complex.im hp
  simp only [pow_two,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.zero_re,Complex.zero_im] at hr hi
  constructor
  · unfold nullMetric
    nlinarith
  · nlinarith

theorem nullMetric_pos {p : Fin 3 → ℂ} (hp : ComplexNull p) (hn : p ≠ 0) :
    0 < nullMetric p := by
  have hr := (complexNull_real_identities hp).1
  unfold nullMetric at hr ⊢
  by_contra h
  have hs : (p 0).re^2+(p 1).re^2+(p 2).re^2 ≤ 0 := le_of_not_gt h
  apply hn
  ext j
  fin_cases j <;> apply Complex.ext <;> dsimp <;>
    nlinarith [sq_nonneg (p 0).re,sq_nonneg (p 1).re,sq_nonneg (p 2).re,
      sq_nonneg (p 0).im,sq_nonneg (p 1).im,sq_nonneg (p 2).im]

theorem nullVector_real_map_zero {p : Fin 3 → ℂ} (hp : ComplexNull p) (hn : p ≠ 0)
    {w : ℂ} (hw : ∀ j, (w*p j).re = 0) : w = 0 := by
  have hid := complexNull_real_identities hp
  have hpos := nullMetric_pos hp hn
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  simp only [Complex.mul_re] at h0 h1 h2
  have hre : w.re*nullMetric p = 0 := by
    unfold nullMetric
    linear_combination (p 0).re*h0+(p 1).re*h1+(p 2).re*h2+w.im*hid.2
  have him : w.im*nullMetric p = 0 := by
    unfold nullMetric at hid ⊢
    linear_combination -(p 0).im*h0-(p 1).im*h1-(p 2).im*h2+w.re*hid.2+w.im*hid.1
  apply Complex.ext
  · exact (mul_eq_zero.mp hre).resolve_right hpos.ne'
  · exact (mul_eq_zero.mp him).resolve_right hpos.ne'

theorem nullVector_real_map_injective {p : Fin 3 → ℂ} (hp : ComplexNull p) (hn : p ≠ 0) :
    Function.Injective (fun w : ℂ => fun j => (w*p j).re) := by
  intro u v h
  apply sub_eq_zero.mp
  apply nullVector_real_map_zero hp hn
  intro j
  have he := congrFun h j
  simpa only [sub_mul,Complex.sub_re,sub_eq_zero] using he

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.nullVector_real_map_injective
