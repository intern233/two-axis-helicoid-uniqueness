import TwoAxisHelicoid.ThetaKernelRegular

/-! Holomorphic continuation of the manuscript's three coordinate differentials.
These statements concern the actual functions, including the finite zeros of dh.
They do not assert the global period problem, completeness or embeddedness. -/
namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaA thetaGauss

noncomputable def coordinateData (t a c : ℝ) (ht : 0 < t) (z : ℂ) : Fin 3 → ℂ :=
  ![-(c:ℂ)/2*(thetaA t a (-z)+thetaA t a z),
    I*c/2*(thetaA t a z-thetaA t a (-z)),
    I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a)]

theorem coordinateData_analyticAt {t a c : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    AnalyticAt ℂ (coordinateData t a c ht) z := by
  have hA := thetaA_analyticAt_off_lattice ht a hz
  have hN : AnalyticAt ℂ (fun w : ℂ => thetaA t a (-w)) z :=
    (thetaA_analyticAt_off_lattice ht a (show -z ∉ _ by simpa using hz)).comp
      (f := fun w : ℂ => -w) (by fun_prop)
  have hP := (rhombicPeriodPair t ht).analyticOnNhd_weierstrassP z hz
  apply AnalyticAt.pi
  intro j
  fin_cases j <;> dsimp [coordinateData] <;> fun_prop

theorem coordinateData_null {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 1)
    {z : ℂ} (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    (coordinateData t a c ht z 0)^2+(coordinateData t a c ht z 1)^2+
      (coordinateData t a c ht z 2)^2 = 0 := by
  have hp := thetaA_neg_product ht
    (real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])) hz
  dsimp [coordinateData]
  calc
    _ = (c:ℂ)^2*(thetaA t a z*thetaA t a (-z)-
        ((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a)^2) := by
      ring_nf
      simp only [I_sq]
      ring
    _ = 0 := by rw [hp]; ring

theorem coordinateData_ne_zero {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 1)
    (hc : c ≠ 0) {z : ℂ} (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    coordinateData t a c ht z ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [coordinateData,Matrix.cons_val_zero,Matrix.cons_val_one,Pi.zero_apply] at h0 h1
  have hcC : (c:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hsum := (mul_eq_zero.mp h0).resolve_left (div_ne_zero (neg_ne_zero.mpr hcC) (by norm_num))
  have hsub := (mul_eq_zero.mp h1).resolve_left
    (div_ne_zero (mul_ne_zero I_ne_zero hcC) (by norm_num))
  have hA : thetaA t a z = 0 := by linear_combination (hsum+hsub)/2
  have hN : thetaA t a (-z) = 0 := by linear_combination (hsum-hsub)/2
  rcases thetaA_pair_not_both_zero ht ha hz with h | h
  · exact h hA
  · exact h hN

theorem coordinateData_eq_original {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 1)
    {z : ℂ} (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    coordinateData t a c ht z =
      ![((thetaGauss t a 1 z)⁻¹-thetaGauss t a 1 z)/2*
          (I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a)),
        I*((thetaGauss t a 1 z)⁻¹+thetaGauss t a 1 z)/2*
          (I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a)),
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a)] := by
  have haL := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  have hg := thetaGauss_height_sigma_of_pos ht ht c haL hz hp
  rw [thetaSigmaKernel_eq_thetaA_of_pos ht ht z haL hz] at hg
  have hnz : -z ∉ (rhombicPeriodPair t ht).lattice := by simpa using hz
  have hnp : -z+a ∉ (rhombicPeriodPair t ht).lattice := by
    simpa only [show -z+(a:ℂ) = -(z-a) by ring,neg_mem_iff] using hm
  have hgn := thetaGauss_height_sigma_of_pos ht ht c haL hnz hnp
  rw [thetaSigmaKernel_eq_thetaA_of_pos ht ht (-z) haL hnz,
    (rhombicPeriodPair t ht).weierstrassP_neg] at hgn
  have hprod := thetaGauss_neg_product ht a 1 hm hp
  have hne := thetaGauss_ne_zero ht a 1 hm hp
  have he : thetaGauss t a 1 (-z) = -(thetaGauss t a 1 z)⁻¹ := by
    apply (mul_right_cancel₀ hne)
    rw [hprod]
    simp [hne]
  rw [he] at hgn
  ext j
  fin_cases j <;> dsimp [coordinateData]
  · linear_combination (hg+hgn)/2
  · linear_combination -I*(hg-hgn)/2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.coordinateData_analyticAt
#print axioms TwoAxisHelicoid.coordinateData_null
#print axioms TwoAxisHelicoid.coordinateData_ne_zero
#print axioms TwoAxisHelicoid.coordinateData_eq_original
