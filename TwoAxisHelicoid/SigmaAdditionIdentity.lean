import TwoAxisHelicoid.SigmaAdditionRegularity

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaSigma

theorem sigmaAdditionDifference_add_lattice {t : ℝ} (ht : 0 < t) (a z : ℂ)
    (l : (rhombicPeriodPair t ht).lattice) :
    sigmaAdditionDifference t ht a (z+l) = sigmaAdditionDifference t ht a z := by
  simp only [sigmaAdditionDifference,thetaSigmaRatio_add_lattice ht,PeriodPair.weierstrassP_add_coe]
  congr 1
  simpa using ((rhombicPeriodPair t ht).lattice.toAddSubgroup.add_mem_cancel_right
    (y := z) l.property)

theorem sigmaAdditionDifference_sub_lattice {t : ℝ} (ht : 0 < t) (a z : ℂ)
    (l : (rhombicPeriodPair t ht).lattice) :
    sigmaAdditionDifference t ht a (z-l) = sigmaAdditionDifference t ht a z := by
  rw [← sigmaAdditionDifference_add_lattice ht a (z-l) l,sub_add_cancel]

theorem sigmaAdditionDifference_analyticAt {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) {a : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht0).lattice) (z : ℂ) :
    AnalyticAt ℂ (sigmaAdditionDifference t ht0 a) z := by
  let L := rhombicPeriodPair t ht0
  by_cases hz : z ∈ L.lattice
  · have h0 := sigmaAdditionDifference_analyticAt_zero ht ht0 ha
    rw [← sub_self z] at h0
    convert h0.comp (f := fun w => w-z) (by fun_prop) using 1
    funext w
    exact (sigmaAdditionDifference_sub_lattice ht0 a w ⟨z,hz⟩).symm
  · have hf : AnalyticAt ℂ (fun w => sigmaRatio (thetaSigma t) a w+L.weierstrassP w-L.weierstrassP a) z :=
      ((thetaSigmaRatio_analyticAt ht ht0 ha hz).add (L.analyticOnNhd_weierstrassP z hz)).sub analyticAt_const
    apply hf.congr
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    change w ∉ (rhombicPeriodPair t ht0).lattice at hw
    simp only [sigmaAdditionDifference,ite_eq_right hw]
    rfl

theorem sigmaAdditionDifference_eq_zero {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) {a : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht0).lattice) (z : ℂ) : sigmaAdditionDifference t ht0 a z = 0 := by
  let L := rhombicPeriodPair t ht0
  have hd : Differentiable ℂ (sigmaAdditionDifference t ht0 a) :=
    fun w => (sigmaAdditionDifference_analyticAt ht ht0 ha w).differentiableAt
  have hb := (IsZLattice.isCompact_range_of_periodic L.lattice (sigmaAdditionDifference t ht0 a)
    hd.continuous (fun x w hw => sigmaAdditionDifference_add_lattice ht0 a x ⟨w,hw⟩)).isBounded
  exact (hd.apply_eq_apply_of_bounded hb z 0).trans (sigmaAdditionDifference_zero t ht0 a)

theorem thetaSigma_addition {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) {a z : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht0).lattice) (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    thetaSigma t (z-a)*thetaSigma t (z+a)/(thetaSigma t z^2*thetaSigma t a^2) =
      (rhombicPeriodPair t ht0).weierstrassP a-(rhombicPeriodPair t ht0).weierstrassP z := by
  have h := sigmaAdditionDifference_eq_zero ht ht0 ha z
  rw [sigmaAdditionDifference,ite_eq_right hz,sigmaRatio] at h
  linear_combination h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaSigma_addition
