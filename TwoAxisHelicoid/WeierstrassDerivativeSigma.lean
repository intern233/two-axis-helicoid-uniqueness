import TwoAxisHelicoid.SigmaAdditionIdentity

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaSigma

theorem rhombic_weierstrassP_hasDerivAt {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    HasDerivAt (rhombicPeriodPair t ht).weierstrassP ((rhombicPeriodPair t ht).derivWeierstrassP z) z := by
  simpa only [PeriodPair.deriv_weierstrassP] using
    ((rhombicPeriodPair t ht).analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt

theorem thetaSigmaRatio_hasDerivAt_self {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) {a : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht0).lattice) :
    HasDerivAt (sigmaRatio (thetaSigma t) a) (thetaSigma t (2*a)/thetaSigma t a^4) a := by
  have hn := mt (thetaSigma_zero_iff_lattice ht ht0 a).mp ha
  have h0 : HasDerivAt (thetaSigma t) 1 (a-a) := by
    simpa only [sub_self] using thetaSigma_hasDerivAt_zero ht
  have hm := h0.comp (h := fun z : ℂ => z-a) a ((hasDerivAt_id a).sub_const a)
  have hp := (thetaSigma_hasDerivAt ht0 (a+a)).comp (h := fun z : ℂ => z+a) a ((hasDerivAt_id a).add_const a)
  have hd := ((thetaSigma_hasDerivAt ht0 a).pow 2).mul_const (thetaSigma t a^2)
  have hr := (hm.mul hp).div hd (mul_ne_zero (pow_ne_zero 2 hn) (pow_ne_zero 2 hn))
  convert hr using 1
  · rfl
  · simp only [Pi.mul_apply,Pi.pow_apply,Function.comp_apply,sub_self,thetaSigma_zero,zero_mul,sub_zero,add_zero,
      one_mul,mul_one,show a+a = 2*a by ring]
    field_simp

theorem rhombic_weierstrassP_derivative_sigma {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) {a : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht0).lattice) :
    (rhombicPeriodPair t ht0).derivWeierstrassP a = -thetaSigma t (2*a)/thetaSigma t a^4 := by
  let L := rhombicPeriodPair t ht0
  have he : sigmaRatio (thetaSigma t) a =ᶠ[𝓝 a] fun z => L.weierstrassP a-L.weierstrassP z := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds ha] with z hz
    exact thetaSigma_addition ht ht0 ha hz
  have hr := (thetaSigmaRatio_hasDerivAt_self ht ht0 ha).congr_of_eventuallyEq he.symm
  have hp := (rhombic_weierstrassP_hasDerivAt ht0 ha).const_sub (L.weierstrassP a)
  have h := hr.unique hp
  linear_combination h

theorem rhombic_weierstrassP_critical_iff {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) {a : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht0).lattice) :
    (rhombicPeriodPair t ht0).derivWeierstrassP a = 0 ↔ 2*a ∈ (rhombicPeriodPair t ht0).lattice := by
  have hn := mt (thetaSigma_zero_iff_lattice ht ht0 a).mp ha
  rw [rhombic_weierstrassP_derivative_sigma ht ht0 ha,div_eq_zero_iff,neg_eq_zero]
  simp only [pow_ne_zero 4 hn,or_false]
  exact thetaSigma_zero_iff_lattice ht ht0 (2*a)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rhombic_weierstrassP_critical_iff
