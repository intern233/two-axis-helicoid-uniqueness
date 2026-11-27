import TwoAxisHelicoid.CentralLevelThetaFactor

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

/-- On a fixed physical height, a single rotation and a positive real
factor recover the actual Gauss map from the meromorphic theta quotient. -/
theorem physical_level_gauss_theta_ratio {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (root : thetaG t a=0) (z : ℂ) :
    let H := actualComplexHeight t a 1 ht z
    let α := 2*(a-1)
    thetaGauss t a 1 z=I*exp (I*((α*H.re:ℝ):ℂ))*
      (Real.exp (-α*H.im):ℂ)*centralPhaseThetaRatio t a z := by
  intro H α
  have e : I*((2*(a-(1:ℤ))/1:ℝ):ℂ)*H=I*((α*H.re:ℝ):ℂ)+((-α*H.im:ℝ):ℂ) := by
    apply Complex.ext <;> simp [α,Complex.mul_re,Complex.mul_im]
  have ident := gauss_height_factor_identity (a:=a) (c:=1) ht one_ne_zero 1 z
  change I*thetaGauss t a 1 z=exp (I*((2*(a-(1:ℤ))/1:ℝ):ℂ)*H)*_ at ident
  rw [closed_heightGaussFactor_theta_ratio ht ha root,e,exp_add,← ofReal_exp] at ident
  calc
    thetaGauss t a 1 z = -I*(I*thetaGauss t a 1 z) := by rw [← mul_assoc,neg_mul,I_mul_I,neg_neg,one_mul]
    _ = _ := by rw [ident]; ring

/-- Every equal-height comparison of horizontal directions can be made
with the meromorphic quotient, even on noncentral regular levels. The
determinants agree up to the explicitly positive factor below. -/
theorem equal_height_gauss_theta_determinant {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (root : thetaG t a=0) {z w : ℂ}
    (same : (actualComplexHeight t a 1 ht z).re=(actualComplexHeight t a 1 ht w).re) :
    let G := thetaGauss t a 1
    let R := centralPhaseThetaRatio t a
    ∃ c : ℝ, 0<c ∧ conj (G z)*G w=(c:ℂ)*(conj (R z)*R w) ∧
      ((conj (G z)*G w).im=0 ↔ (conj (R z)*R w).im=0) := by
  intro G R
  let H := actualComplexHeight t a 1 ht
  let α := 2*(a-1)
  let s := fun u => Real.exp (-α*(H u).im)
  let E := exp (I*((α*(H w).re:ℝ):ℂ))
  have unit : conj E*E=1 := by
    dsimp only [E]
    rw [← exp_conj,← exp_add]
    simp
  have gz := physical_level_gauss_theta_ratio ht ha root z
  have gw := physical_level_gauss_theta_ratio ht ha root w
  dsimp only at gz gw
  rw [same] at gz
  change G z=I*E*(s z:ℂ)*R z at gz
  change G w=I*E*(s w:ℂ)*R w at gw
  have cp : 0<s z*s w := mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have eq : conj (G z)*G w=((s z*s w:ℝ):ℂ)*(conj (R z)*R w) := by
    rw [gz,gw]
    simp only [map_mul,conj_I,conj_ofReal,ofReal_mul]
    calc
      _ = -(I*I)*(conj E*E)*(s z:ℂ)*(s w:ℂ)*(conj (R z)*R w) := by ring
      _ = _ := by rw [unit,I_mul_I]; ring
  refine ⟨_,cp,eq,?_⟩
  rw [eq]
  simp [Complex.mul_im,cp.ne']

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_level_gauss_theta_ratio
#print axioms TwoAxisHelicoid.equal_height_gauss_theta_determinant
