import TwoAxisHelicoid.SigmaAdditionIdentity
import TwoAxisHelicoid.ThetaSigmaKernel

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaSigma thetaZeta thetaG thetaA

noncomputable def thetaGauss (t a : ℝ) (m : ℤ) (z : ℂ) : ℂ :=
  I*Complex.exp (2*(a-m)*thetaZeta t z+2*m*thetaEtaExpression t*z)*
    thetaSigma t (z-a)/thetaSigma t (z+a)

theorem thetaGauss_height_sigma {t a : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) (c : ℝ) {z : ℂ}
    (ha : (a:ℂ) ∉ (rhombicPeriodPair t ht0).lattice)
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice)
    (hzp : z+a ∉ (rhombicPeriodPair t ht0).lattice) :
    thetaGauss t a 1 z*(I*c*((rhombicPeriodPair t ht0).weierstrassP z-
      (rhombicPeriodPair t ht0).weierstrassP a)) = (c:ℂ)*thetaSigmaKernel t a z := by
  have hsa := mt (thetaSigma_zero_iff_lattice ht ht0 (a:ℂ)).mp ha
  have hsz := mt (thetaSigma_zero_iff_lattice ht ht0 z).mp hz
  have hsp := mt (thetaSigma_zero_iff_lattice ht ht0 (z+a)).mp hzp
  have hAdd := thetaSigma_addition ht ht0 ha hz
  rw [← neg_sub ((rhombicPeriodPair t ht0).weierstrassP a)
    ((rhombicPeriodPair t ht0).weierstrassP z),← hAdd]
  simp only [thetaGauss,thetaSigmaKernel,Int.cast_one,mul_one]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- The manuscript's g dh = c alpha identity for its m=1 data, on the domain
where the displayed quotient for g is defined. The analytic kernel extends
across the removable cancellation at the finite zeros of dh. -/
theorem thetaGauss_height_kernel {t a : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) (c : ℝ) {z : ℂ}
    (ha : (a:ℂ) ∉ (rhombicPeriodPair t ht0).lattice)
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice)
    (hzp : z+a ∉ (rhombicPeriodPair t ht0).lattice) (hG : thetaG t a = 0) :
    thetaGauss t a 1 z*(I*c*((rhombicPeriodPair t ht0).weierstrassP z-
      ((Real.pi/t:ℝ)-thetaEtaExpression t))) = (c:ℂ)*thetaA t a z := by
  have he := thetaG_eq_weierstrassP ht ht0 a ha
  rw [hG] at he
  have hu : ((Real.pi/t:ℝ):ℂ)-thetaEtaExpression t = (rhombicPeriodPair t ht0).weierstrassP a := by
    linear_combination he
  rw [hu,thetaGauss_height_sigma ht ht0 c ha hz hzp,thetaSigmaKernel_eq_thetaA ht ht0 z ha hz]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaGauss_height_kernel
