import TwoAxisHelicoid.JacobiThetaLogDerivative
import TwoAxisHelicoid.LambertGeometricRearrangement
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

namespace TwoAxisHelicoid
open Complex

private theorem jacobi_euler_lambert {Q X : ℂ} (hQ : ‖Q‖<1) (hX : ‖Q‖*‖X‖<1) :
    let L := fun k : ℕ => (Q*X)^(k+1)/(1-Q^(k+1))
    Summable L ∧ X*logDeriv (jacobiFactorProduct Q) X= -(∑' k, L k) := by
  obtain ⟨s,e⟩ := (geometric_lambert_orders_zero_one hQ (show ‖Q*X‖<1 by rwa [norm_mul])).1
  refine ⟨s,?_⟩
  rw [jacobiFactorProduct_logDeriv hQ hX,← tsum_mul_left,← e,← tsum_neg]
  apply tsum_congr
  intro j
  rw [pow_succ]
  ring

private theorem jacobi_exp_sine (z : ℂ) (k : ℕ) :
    Complex.sin ((k:ℂ)*Real.pi*z)=((jacobiExp z)⁻¹^k-(jacobiExp z)^k)*I/2 := by
  unfold Complex.sin jacobiExp
  rw [show -((k:ℂ)*Real.pi*z)*I= -((k:ℂ)*(I*(Real.pi:ℂ)*z)) by ring,
    show (k:ℂ)*Real.pi*z*I=(k:ℂ)*(I*(Real.pi:ℂ)*z) by ring,
    Complex.exp_neg,Complex.exp_nat_mul,inv_pow]

private theorem jacobi_cotangent_principal {z : ℂ} (hx : jacobiExp z≠1) :
    I*(Real.pi:ℂ)*(-1/2-jacobiExp z/(1-jacobiExp z))=
      (Real.pi:ℂ)/2*Complex.cot ((Real.pi:ℂ)*z/2) := by
  rw [Complex.cot_eq_exp_ratio,show 2*I*((Real.pi:ℂ)*z/2)=I*(Real.pi:ℂ)*z by ring]
  change I*(Real.pi:ℂ)*(-1/2-jacobiExp z/(1-jacobiExp z))=
    (Real.pi:ℂ)/2*((jacobiExp z+1)/(I*(1-jacobiExp z)))
  field_simp [sub_ne_zero.mpr hx.symm, I_ne_zero]
  ring_nf
  simp only [I_sq]
  ring

/-- Fourier series of the rectangular theta product's logarithmic
derivative on the whole annulus of convergence. Both bilateral
geometric contributions are proved absolutely summable. -/
theorem jacobi_product_log_fourier {Q z : ℂ} (hQ : ‖Q‖<1) (hx : jacobiExp z≠1)
    (hp : ‖Q‖*‖jacobiExp z‖<1) (hm : ‖Q‖*‖(jacobiExp z)⁻¹‖<1) :
    let S := fun j : ℕ => Q^(j+1)/(1-Q^(j+1))*Complex.sin (((j+1:ℕ):ℂ)*Real.pi*z)
    Summable S ∧ logDeriv (jacobiThetaProduct Q) z=
      (Real.pi:ℂ)/2*Complex.cot ((Real.pi:ℂ)*z/2)+2*Real.pi*(∑' j, S j) := by
  let X := jacobiExp z
  let A := fun (x : ℂ) (j : ℕ) => (Q*x)^(j+1)/(1-Q^(j+1))
  let S := fun j : ℕ => Q^(j+1)/(1-Q^(j+1))*Complex.sin (((j+1:ℕ):ℂ)*Real.pi*z)
  obtain ⟨sP,eP⟩ := jacobi_euler_lambert hQ hp
  obtain ⟨sM,eM⟩ := jacobi_euler_lambert hQ hm
  change Summable (A X) at sP
  change Summable (A X⁻¹) at sM
  change X*logDeriv (jacobiFactorProduct Q) X= -(∑' j, A X j) at eP
  change X⁻¹*logDeriv (jacobiFactorProduct Q) X⁻¹= -(∑' j, A X⁻¹ j) at eM
  have term (j : ℕ) : (I/2)*(A X⁻¹ j-A X j)=S j := by
    dsimp only [A,S]
    rw [jacobi_exp_sine,mul_pow,mul_pow]
    dsimp only [X]
    ring
  have s := ((sM.sub sP).mul_left (I/2)).congr term
  have series : (∑' j, S j)=(I/2)*((∑' j, A X⁻¹ j)-(∑' j, A X j)) := by
    rw [← tsum_congr term,tsum_mul_left,sM.tsum_sub sP]
  change Summable S ∧ _=_
  refine ⟨s,?_⟩
  rw [jacobiThetaProduct_logDeriv hQ hx hp hm,← jacobi_cotangent_principal hx]
  change I*(Real.pi:ℂ)*(-1/2-X/(1-X)+X*logDeriv (jacobiFactorProduct Q) X-X⁻¹*logDeriv (jacobiFactorProduct Q) X⁻¹)=
    I*(Real.pi:ℂ)*(-1/2-X/(1-X))+2*Real.pi*(∑' j, S j)
  rw [eP,eM,series]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.jacobi_product_log_fourier

