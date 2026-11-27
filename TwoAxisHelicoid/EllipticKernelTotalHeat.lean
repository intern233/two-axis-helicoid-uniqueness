import TwoAxisHelicoid.OriginalMovingComplexPeriod

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaA thetaLt thetaLa thetaLz thetaW verticalA periodD

noncomputable def ellipticKernelRa (t : ℝ) (ht : 0 < t) (a : ℝ) (z : ℂ) : ℂ :=
  ((rhombicPeriodPair t ht).derivWeierstrassP z+
    (rhombicPeriodPair t ht).derivWeierstrassP a)/
      ((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a)

theorem thetaLa_eq_neg_ellipticKernelRa {t a : ℝ} (ht : 0 < t) {z : ℂ}
    (ha : (a : ℂ) ∉ (rhombicPeriodPair t ht).lattice)
    (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    thetaLa t a z = -ellipticKernelRa t ht a z := by
  simpa only [ellipticKernelRa,neg_div] using thetaLa_elliptic_quotient ht ha hz hm hp

theorem thetaLz_eq_ellipticKernelRa {t a : ℝ} (ht : 0 < t) {z : ℂ}
    (ha : (a : ℂ) ∉ (rhombicPeriodPair t ht).lattice)
    (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    thetaLz t a z = ellipticKernelRa t ht a z-2*thetaW t a-
      2*(a-1)*((rhombicPeriodPair t ht).weierstrassP z+thetaEtaExpression t) := by
  have h := thetaLa_add_Lz_elliptic ht a hz
  rw [thetaLa_eq_neg_ellipticKernelRa ht ha hz hm hp] at h
  unfold thetaW
  linear_combination h

theorem thetaA_total_logarithmic_heat {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht.1).lattice)
    (hm : z-verticalA t ∉ (rhombicPeriodPair t ht.1).lattice)
    (hp : z+verticalA t ∉ (rhombicPeriodPair t ht.1).lattice) :
    (Real.pi : ℂ)*(thetaLt t (verticalA t) z+
      ((deriv verticalA t : ℝ) : ℂ)*thetaLa t (verticalA t) z) =
      thetaW t z*thetaLz t (verticalA t) z-
        (verticalA t-1)*(rhombicPeriodPair t ht.1).derivWeierstrassP z+
        (periodD t (verticalA t) : ℂ)*ellipticKernelRa t ht.1 (verticalA t) z+
        2*(rhombicPeriodPair t ht.1).weierstrassP z+
        2*(rhombicPeriodPair t ht.1).weierstrassP (verticalA t)-2*thetaEtaExpression t := by
  have ha := real_not_mem_rhombic_lattice_of_pos ht.1 (verticalA_spec ht).1.1
    (show verticalA t < 2 by linarith [(verticalA_spec ht).1.2])
  have hW : ((thetaW t (verticalA t)).re : ℂ) = thetaW t (verticalA t) := by
    apply Complex.ext <;> simp only [Complex.ofReal_re,Complex.ofReal_im,thetaW_real]
  have hap : ((deriv verticalA t : ℝ) : ℂ) =
      -(thetaW t (verticalA t)+(periodD t (verticalA t) : ℂ))/(Real.pi : ℂ) := by
    rw [verticalA_deriv_WD ht]
    push_cast
    rw [hW]
  rw [mul_add,thetaLt_elliptic_identity ht.1 ha hz hm hp,hap,
    thetaLa_eq_neg_ellipticKernelRa ht.1 ha hz hm hp]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

theorem thetaA_along_vertical_hasDerivAt_elliptic {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht.1).lattice)
    (hm : z-verticalA t ∉ (rhombicPeriodPair t ht.1).lattice)
    (hp : z+verticalA t ∉ (rhombicPeriodPair t ht.1).lattice) :
    HasDerivAt (fun r : ℝ => thetaA r (verticalA r) z)
      (thetaA t (verticalA t) z*
        (thetaW t z*thetaLz t (verticalA t) z-
          (verticalA t-1)*(rhombicPeriodPair t ht.1).derivWeierstrassP z+
          (periodD t (verticalA t) : ℂ)*ellipticKernelRa t ht.1 (verticalA t) z+
          2*(rhombicPeriodPair t ht.1).weierstrassP z+
          2*(rhombicPeriodPair t ht.1).weierstrassP (verticalA t)-2*thetaEtaExpression t)/
        (Real.pi : ℂ)) t := by
  have ha := (verticalA_spec ht).1
  have hdenz := mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht.1 z).mp hz
  have hdenm := mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht.1 (z-verticalA t)).mp hm
  have hd := thetaA_curve_hasDerivAt (hasDerivAt_id t)
    (verticalA_hasDerivAt ht).differentiableAt.hasDerivAt (hasDerivAt_const t z) ht.1
    (thetaJet_one_at_zero_ne_zero_of_pos ht.1)
    (theta_vertical_denominator ht.1 ha.1 (by linarith [ha.2])) hdenz hdenm
  convert hd using 1
  · rfl
  · simp only [id_eq,Complex.ofReal_one,one_mul,zero_mul,add_zero]
    rw [← thetaA_total_logarithmic_heat ht hz hm hp]
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaA_total_logarithmic_heat
#print axioms TwoAxisHelicoid.thetaA_along_vertical_hasDerivAt_elliptic
