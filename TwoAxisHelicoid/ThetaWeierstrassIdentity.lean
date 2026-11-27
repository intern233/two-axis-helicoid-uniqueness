import TwoAxisHelicoid.ThetaWeierstrassRegularity

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaJet thetaScaledJet thetaLogSecond

theorem thetaWeierstrassDifference_add_lattice {t : ℝ} (ht : 0 < t) (z : ℂ)
    (l : (rhombicPeriodPair t ht).lattice) :
    thetaWeierstrassDifference t ht (z+l) = thetaWeierstrassDifference t ht z := by
  simp only [thetaWeierstrassDifference,thetaLogSecond_add_lattice ht,
    PeriodPair.weierstrassP_add_coe]
  congr 1
  simpa using ((rhombicPeriodPair t ht).lattice.toAddSubgroup.add_mem_cancel_right
    (y := z) l.property)

theorem thetaWeierstrassDifference_sub_lattice {t : ℝ} (ht : 0 < t) (z : ℂ)
    (l : (rhombicPeriodPair t ht).lattice) :
    thetaWeierstrassDifference t ht (z-l) = thetaWeierstrassDifference t ht z := by
  rw [← thetaWeierstrassDifference_add_lattice ht (z-l) l,sub_add_cancel]

theorem thetaWeierstrassDifference_analyticAt {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) (z : ℂ) :
    AnalyticAt ℂ (thetaWeierstrassDifference t ht0) z := by
  let L := rhombicPeriodPair t ht0
  by_cases hz : z ∈ L.lattice
  · have h0 := thetaWeierstrassDifference_analyticAt_zero ht ht0
    rw [← sub_self z] at h0
    convert h0.comp (f := fun w => w-z) (by fun_prop) using 1
    funext w
    exact (thetaWeierstrassDifference_sub_lattice ht0 w ⟨z,hz⟩).symm
  · have hf : AnalyticAt ℂ (fun w => thetaLogSecond t w-L.weierstrassP w-thetaEtaExpression t) z :=
      ((thetaLogSecond_analyticAt ht ht0 hz).sub
        (L.analyticOnNhd_weierstrassP z hz)).sub analyticAt_const
    apply hf.congr
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    change w ∉ (rhombicPeriodPair t ht0).lattice at hw
    simp only [thetaWeierstrassDifference,ite_eq_right hw]
    rfl

theorem thetaWeierstrassDifference_eq_zero {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) (z : ℂ) :
    thetaWeierstrassDifference t ht0 z = 0 := by
  let L := rhombicPeriodPair t ht0
  have hd : Differentiable ℂ (thetaWeierstrassDifference t ht0) :=
    fun w => (thetaWeierstrassDifference_analyticAt ht ht0 w).differentiableAt
  have hb := (IsZLattice.isCompact_range_of_periodic L.lattice
    (thetaWeierstrassDifference t ht0) hd.continuous
    (fun x w hw => thetaWeierstrassDifference_add_lattice ht0 x ⟨w,hw⟩)).isBounded
  exact (hd.apply_eq_apply_of_bounded hb z 0).trans (thetaWeierstrassDifference_zero t ht0)

/-- The actual mathlib Weierstrass function, rather than a second function
defined to have the desired theta formula. The threshold is explicit. -/
theorem thetaLogSecond_eq_weierstrassP_add_eta {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t)
    {z : ℂ} (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    thetaLogSecond t z = (rhombicPeriodPair t ht0).weierstrassP z+thetaEtaExpression t := by
  have h := thetaWeierstrassDifference_eq_zero ht ht0 z
  rw [thetaWeierstrassDifference,ite_eq_right hz] at h
  linear_combination h

theorem thetaG_eq_weierstrassP {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) (a : ℝ)
    (ha : (a:ℂ) ∉ (rhombicPeriodPair t ht0).lattice) :
    thetaG t a = (rhombicPeriodPair t ht0).weierstrassP a+thetaEtaExpression t-(Real.pi/t:ℝ) := by
  have h := thetaLogSecond_eq_weierstrassP_add_eta ht ht0 ha
  unfold thetaG
  unfold thetaLogSecond at h
  rw [h]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaLogSecond_eq_weierstrassP_add_eta
