import TwoAxisHelicoid.HeightExtremalDoublePoint
import TwoAxisHelicoid.WeierstrassRotation

namespace TwoAxisHelicoid
open Complex
open scoped ComplexConjugate

/-- The real direction of the horizontal level curve is the quarter-turn
of the Gauss phase, with the actual positive length factor. -/
theorem levelTangent_weierstrass {g h : ℂ} (hh : h≠0) :
    levelTangent (weierstrassTriple g h) =
      ![((normSq g)⁻¹+1)/2*g.im,-(((normSq g)⁻¹+1)/2)*g.re,0] := by
  funext j
  fin_cases j
  · change (I/h*((g⁻¹-g)/2*h)).re=_
    rw [show I/h*((g⁻¹-g)/2*h) = I*(g⁻¹-g)/2 by field_simp]
    simp [Complex.mul_re,Complex.sub_im,Complex.inv_im,div_eq_mul_inv]
    ring
  · change (I/h*(I*(g⁻¹+g)/2*h)).re=_
    have e : I/h*(I*(g⁻¹+g)/2*h) = (I*I)*((g⁻¹+g)/2) := by field_simp
    rw [e,I_mul_I]
    simp [Complex.inv_re,div_eq_mul_inv]
    ring
  · change (I/h*h).re=0
    rw [div_mul_cancel₀ _ hh,I_re]

/-- Two regular horizontal level directions are parallel precisely
when the two nonzero Gauss values have the same phase modulo π. -/
theorem levelTangent_det_zero_iff {g k h l : ℂ} (hh : h≠0) (hl : l≠0) :
    let A := levelTangent (weierstrassTriple g h)
    let B := levelTangent (weierstrassTriple k l)
    A 0*B 1-A 1*B 0=0 ↔ (conj g*k).im=0 := by
  dsimp only
  rw [levelTangent_weierstrass hh,levelTangent_weierstrass hl]
  let a := ((normSq g)⁻¹+1)/2
  let b := ((normSq k)⁻¹+1)/2
  have positiveFactor (u : ℂ) : 0<((normSq u)⁻¹+1)/2 := div_pos (add_pos_of_nonneg_of_pos (inv_nonneg.mpr (normSq_nonneg _)) one_pos) (by norm_num)
  have ap : 0<a := positiveFactor g
  have bp : 0<b := positiveFactor k
  change (a*g.im)*(-b*k.re)-(-a*g.re)*(b*k.im)=0 ↔ _
  rw [show (a*g.im)*(-b*k.re)-(-a*g.re)*(b*k.im)=(a*b)*(conj g*k).im by
    simp [Complex.mul_im]; ring]
  exact mul_eq_zero_iff_left (mul_pos ap bp).ne'

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.levelTangent_det_zero_iff
