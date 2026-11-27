import TwoAxisHelicoid.SigmaAllIdentities

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaSigma thetaZeta

theorem sigmaRatio_z_hasDerivAt {t : ℝ} (ht : 0 < t) {a z : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht).lattice) (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice) (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    HasDerivAt (sigmaRatio (thetaSigma t) a)
      (sigmaRatio (thetaSigma t) a z*(thetaZeta t (z-a)+thetaZeta t (z+a)-2*thetaZeta t z)) z := by
  have hsa := mt (thetaSigma_zero_iff_lattice_of_pos ht ht a).mp ha
  have hsz := mt (thetaSigma_zero_iff_lattice_of_pos ht ht z).mp hz
  have hM := (thetaSigma_hasDerivAt_zeta_of_pos ht ht hm).comp
    (h := fun w : ℂ => w-a) z ((hasDerivAt_id z).sub_const a)
  have hP := (thetaSigma_hasDerivAt_zeta_of_pos ht ht hp).comp
    (h := fun w : ℂ => w+a) z ((hasDerivAt_id z).add_const a)
  have hD := ((thetaSigma_hasDerivAt_zeta_of_pos ht ht hz).pow 2).mul_const (thetaSigma t a^2)
  convert (hM.mul hP).div hD (mul_ne_zero (pow_ne_zero 2 hsz) (pow_ne_zero 2 hsa)) using 1
  · rfl
  · simp only [sigmaRatio,Pi.mul_apply,Pi.pow_apply]
    norm_num
    field_simp

theorem sigmaRatio_a_hasDerivAt {t : ℝ} (ht : 0 < t) {a z : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht).lattice) (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice) (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    HasDerivAt (fun b : ℂ => sigmaRatio (thetaSigma t) b z)
      (sigmaRatio (thetaSigma t) a z*(-thetaZeta t (z-a)+thetaZeta t (z+a)-2*thetaZeta t a)) a := by
  have hsa := mt (thetaSigma_zero_iff_lattice_of_pos ht ht a).mp ha
  have hsz := mt (thetaSigma_zero_iff_lattice_of_pos ht ht z).mp hz
  have hM := (thetaSigma_hasDerivAt_zeta_of_pos ht ht hm).comp
    (h := fun b : ℂ => z-b) a ((hasDerivAt_id a).const_sub z)
  have hP := (thetaSigma_hasDerivAt_zeta_of_pos ht ht hp).comp
    (h := fun b : ℂ => z+b) a ((hasDerivAt_id a).const_add z)
  have hD := ((thetaSigma_hasDerivAt_zeta_of_pos ht ht ha).pow 2).const_mul (thetaSigma t z^2)
  convert (hM.mul hP).div hD (mul_ne_zero (pow_ne_zero 2 hsz) (pow_ne_zero 2 hsa)) using 1
  · rfl
  · simp only [sigmaRatio,Pi.mul_apply,Pi.pow_apply]
    norm_num
    field_simp

theorem thetaZeta_addition_cross {t : ℝ} (ht : 0 < t) {a z : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht).lattice) (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice) (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    2*(thetaZeta t (z-a)-thetaZeta t z+thetaZeta t a)*
      ((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a) =
      (rhombicPeriodPair t ht).derivWeierstrassP z+(rhombicPeriodPair t ht).derivWeierstrassP a := by
  let L := rhombicPeriodPair t ht
  have hez : sigmaRatio (thetaSigma t) a =ᶠ[𝓝 z] fun w => L.weierstrassP a-L.weierstrassP w := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact thetaSigma_addition_of_pos ht ht ha hw
  have hea : (fun b : ℂ => sigmaRatio (thetaSigma t) b z) =ᶠ[𝓝 a] fun b => L.weierstrassP b-L.weierstrassP z := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds ha] with b hb
    exact thetaSigma_addition_of_pos ht ht hb hz
  have hdZ := (sigmaRatio_z_hasDerivAt ht ha hz hm hp).unique
    (((rhombic_weierstrassP_hasDerivAt ht hz).const_sub (L.weierstrassP a)).congr_of_eventuallyEq hez)
  have hdA := (sigmaRatio_a_hasDerivAt ht ha hz hm hp).unique
    (((rhombic_weierstrassP_hasDerivAt ht ha).sub_const (L.weierstrassP z)).congr_of_eventuallyEq hea)
  have hs : sigmaRatio (thetaSigma t) a z = L.weierstrassP a-L.weierstrassP z :=
    thetaSigma_addition_of_pos ht ht ha hz
  rw [hs] at hdZ hdA
  change 2*(thetaZeta t (z-a)-thetaZeta t z+thetaZeta t a)*(L.weierstrassP z-L.weierstrassP a) = _
  linear_combination hdA-hdZ

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaZeta_addition_cross
