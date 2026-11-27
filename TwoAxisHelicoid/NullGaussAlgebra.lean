import TwoAxisHelicoid.NullVectorRegularity

namespace TwoAxisHelicoid
open Complex
open scoped ComplexConjugate

noncomputable def nullHorizontalMinus (p : Fin 3 → ℂ) : ℂ := p 0-I*p 1
noncomputable def nullHorizontalPlus (p : Fin 3 → ℂ) : ℂ := p 0+I*p 1
noncomputable def nullGauss (p : Fin 3 → ℂ) : ℂ := p 2/nullHorizontalMinus p

theorem null_horizontal_product {p : Fin 3 → ℂ} (hp : ComplexNull p) :
    nullHorizontalMinus p*nullHorizontalPlus p = -(p 2)^2 := by
  unfold ComplexNull at hp
  unfold nullHorizontalMinus nullHorizontalPlus
  linear_combination hp-(p 1)^2*Complex.I_sq

theorem null_horizontal_nonzero_of_height {p : Fin 3 → ℂ} (hp : ComplexNull p) (h2 : p 2 ≠ 0) :
    nullHorizontalMinus p ≠ 0 ∧ nullHorizontalPlus p ≠ 0 := by
  apply mul_ne_zero_iff.mp
  rw [null_horizontal_product hp]
  exact neg_ne_zero.mpr (pow_ne_zero 2 h2)

theorem null_horizontal_not_both_zero {p : Fin 3 → ℂ} (hp : ComplexNull p) (hn : p ≠ 0) :
    nullHorizontalMinus p ≠ 0 ∨ nullHorizontalPlus p ≠ 0 := by
  by_contra! h
  have hm : p 0-I*p 1 = 0 := h.1
  have hp' : p 0+I*p 1 = 0 := h.2
  have h0 : p 0 = 0 := by linear_combination (hm+hp')/2
  have h1 : p 1 = 0 := by
    have hi : I*p 1 = 0 := by linear_combination (hp'-hm)/2
    exact (mul_eq_zero.mp hi).resolve_left I_ne_zero
  have hprod := null_horizontal_product hp
  rw [h.1,h.2,zero_mul,eq_comm,neg_eq_zero] at hprod
  have h2 : p 2 = 0 := by
    have he : p 2*p 2 = 0 := by simpa only [pow_two] using hprod
    exact (mul_eq_zero.mp he).elim id id
  apply hn
  funext j
  fin_cases j <;> simp [h0,h1,h2]

theorem null_gauss_inverse_eq {p : Fin 3 → ℂ} (hp : ComplexNull p)
    (hplus : nullHorizontalPlus p ≠ 0) : (nullGauss p)⁻¹ = -p 2/nullHorizontalPlus p := by
  have he := null_horizontal_product hp
  unfold nullGauss
  rw [inv_div]
  by_cases h2 : p 2 = 0
  · have hm : nullHorizontalMinus p = 0 := by
      apply (mul_eq_zero.mp (show nullHorizontalMinus p*nullHorizontalPlus p = 0 by simpa [h2] using he)).resolve_right hplus
    simp [h2,hm]
  · field_simp [hplus,h2]
    linear_combination he

theorem null_gauss_opposite_product {p : Fin 3 → ℂ} (hp : ComplexNull p) (h2 : p 2 ≠ 0) :
    (p 2/nullHorizontalPlus p)*nullGauss p = -1 := by
  have hn := null_horizontal_nonzero_of_height hp h2
  have he := null_horizontal_product hp
  unfold nullGauss
  field_simp [hn.1,hn.2]
  linear_combination he

theorem null_gauss_reconstruct {p : Fin 3 → ℂ} (hp : ComplexNull p) (h2 : p 2 ≠ 0) :
    (1/nullGauss p-nullGauss p)*p 2/2 = p 0 ∧
      I*(1/nullGauss p+nullGauss p)*p 2/2 = p 1 := by
  have hn := null_horizontal_nonzero_of_height hp h2
  have he := null_horizontal_product hp
  have hi : (1/nullGauss p)*p 2 = nullHorizontalMinus p := by
    unfold nullGauss
    field_simp [h2,hn.1]
  have hg : nullGauss p*p 2 = -nullHorizontalPlus p := by
    unfold nullGauss
    field_simp [hn.1]
    linear_combination he
  constructor
  · rw [sub_mul,hi,hg]
    unfold nullHorizontalMinus nullHorizontalPlus
    ring
  · calc I*(1/nullGauss p+nullGauss p)*p 2/2 =
          I*((1/nullGauss p)*p 2+nullGauss p*p 2)/2 := by ring
      _ = p 1 := by
        rw [hi,hg]
        unfold nullHorizontalMinus nullHorizontalPlus
        linear_combination -(p 1)*Complex.I_sq

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.null_gauss_inverse_eq
#print axioms TwoAxisHelicoid.null_gauss_reconstruct
