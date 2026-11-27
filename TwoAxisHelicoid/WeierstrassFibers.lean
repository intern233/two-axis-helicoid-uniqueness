import TwoAxisHelicoid.SigmaAllIdentities

namespace TwoAxisHelicoid
open Complex Set

/-- A genuine finite Weierstrass fiber consists precisely of a point and its
negative, modulo the actual lattice. -/
theorem rhombic_weierstrassP_eq_iff {t : ℝ} (ht : 0 < t) {a z : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht).lattice)
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    (rhombicPeriodPair t ht).weierstrassP z = (rhombicPeriodPair t ht).weierstrassP a ↔
      z-a ∈ (rhombicPeriodPair t ht).lattice ∨ z+a ∈ (rhombicPeriodPair t ht).lattice := by
  have he := thetaSigma_addition_of_pos ht ht ha hz
  have haS := mt (thetaSigma_zero_iff_lattice_of_pos ht ht a).mp ha
  have hzS := mt (thetaSigma_zero_iff_lattice_of_pos ht ht z).mp hz
  have hd : thetaSigma t z^2*thetaSigma t a^2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hzS) (pow_ne_zero 2 haS)
  rw [← sub_eq_zero,← neg_sub]
  rw [neg_eq_zero,← he,div_eq_zero_iff]
  simp only [hd,or_false,mul_eq_zero]
  rw [thetaSigma_zero_iff_lattice_of_pos ht ht,thetaSigma_zero_iff_lattice_of_pos ht ht]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rhombic_weierstrassP_eq_iff
