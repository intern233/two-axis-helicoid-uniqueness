import TwoAxisHelicoid.ThetaWeierstrassIdentity
import TwoAxisHelicoid.ThetaAllSimpleZeros

/-! The Weierstrass identities for every positive height. The modular theta
transformation supplies the zero set and simple-zero statements needed by the
same local principal-part and Liouville argument. -/
namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaJet thetaScaledJet thetaLogSecond

theorem thetaScaledJet_zero_iff_lattice_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) (z : ℂ) :
    thetaScaledJet t 0 z = 0 ↔ z ∈ (rhombicPeriodPair t ht0).lattice := by
  simp only [thetaScaledJet,pow_zero,one_mul]
  rw [show (Real.pi/2:ℂ)*z = Real.pi*z/2 by ring]
  exact thetaJet_zero_iff_rhombic_lattice_of_pos ht z


theorem thetaLogSecond_analyticAt_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice) : AnalyticAt ℂ (thetaLogSecond t) z := by
  have hn : thetaScaledJet t 0 z ≠ 0 := mt (thetaScaledJet_zero_iff_lattice_of_pos ht ht0 z).mp hz
  have he : thetaLogSecond t = fun z =>
      (thetaScaledJet t 1 z/thetaScaledJet t 0 z)^2-thetaScaledJet t 2 z/thetaScaledJet t 0 z :=
    funext (thetaLogSecond_scaled t)
  rw [he]
  have h0 := thetaScaledJet_analyticAt ht0 0 z
  have h1 := thetaScaledJet_analyticAt ht0 1 z
  have h2 := thetaScaledJet_analyticAt ht0 2 z
  exact ((h1.div h0 hn).pow 2).sub (h2.div h0 hn)


theorem thetaWeierstrassDifference_weighted_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) :
    (thetaWeierstrassDifference t ht0*(thetaScaledJet t 0)^2*(id : ℂ → ℂ)^2) =ᶠ[𝓝 0]
      logSecondNumerator (thetaScaledJet t) ((rhombicPeriodPair t ht0).weierstrassPExcept 0)
        (thetaEtaExpression t) := by
  let L := rhombicPeriodPair t ht0
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  by_cases hz0 : z = 0
  · simp [hz0,logSecondNumerator,thetaScaledJet_zero_at_zero]
  have hzL : z ∉ L.lattice := by simpa [hz0] using hz
  change z ∉ (rhombicPeriodPair t ht0).lattice at hzL
  have hf0 : thetaScaledJet t 0 z ≠ 0 := mt (thetaScaledJet_zero_iff_lattice_of_pos ht ht0 z).mp hzL
  have hp : L.weierstrassP z = L.weierstrassPExcept 0 z+1/z^2 := by
    simpa using (L.weierstrassPExcept_add (0 : L.lattice) z).symm
  simp only [Pi.mul_apply,Pi.pow_apply,id_eq,thetaWeierstrassDifference,
    ite_eq_right hzL,thetaLogSecond_scaled,logSecondNumerator]
  change (((thetaScaledJet t 1 z/thetaScaledJet t 0 z)^2-
      thetaScaledJet t 2 z/thetaScaledJet t 0 z)-L.weierstrassP z-thetaEtaExpression t)*
      (thetaScaledJet t 0 z)^2*z^2 = _
  rw [hp]
  field_simp
  ring


theorem thetaScaledJet_zero_meromorphicOrder_of_pos {t : ℝ} (ht : 0 < t) :
    meromorphicOrderAt (thetaScaledJet t 0) 0 = 1 := by
  have ht0 : 0 < t := by linarith
  have hf := thetaScaledJet_analyticAt ht0 0 0
  have hd : deriv (thetaScaledJet t 0) 0 ≠ 0 := by
    rw [(thetaScaledJet_hasDerivAt ht0 0 0).deriv]
    exact thetaScaledJet_one_ne_zero_of_pos ht
  rw [hf.meromorphicOrderAt_eq,
    hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (thetaScaledJet_zero_at_zero t) hd]
  norm_num


theorem thetaWeierstrassDifference_analyticAt_zero_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) :
    AnalyticAt ℂ (thetaWeierstrassDifference t ht0) 0 := by
  let L := rhombicPeriodPair t ht0
  let W := thetaWeierstrassDifference t ht0*(thetaScaledJet t 0)^2*(id : ℂ → ℂ)^2
  let N := logSecondNumerator (thetaScaledJet t) (L.weierstrassPExcept 0) (thetaEtaExpression t)
  have hF (j : ℕ) := thetaScaledJet_analyticAt ht0 j 0
  have hg := L.analyticAt_weierstrassPExcept 0
  have hN : AnalyticAt ℂ N 0 := by
    unfold N logSecondNumerator
    have hf0 := hF 0
    have hf1 := hF 1
    have hf2 := hF 2
    fun_prop
  have he : W =ᶠ[𝓝 0] N := thetaWeierstrassDifference_weighted_of_pos ht ht0
  have hW : AnalyticAt ℂ W 0 := hN.congr he.symm
  have hc : 3*thetaEtaExpression t*thetaScaledJet t 1 0+thetaScaledJet t 3 0 = 0 := by
    unfold thetaEtaExpression
    field_simp [thetaScaledJet_one_ne_zero_of_pos ht]
    ring
  have hvanish (n : ℕ) (hn : n < 5) : iteratedDeriv n W 0 = 0 := by
    rw [he.iteratedDeriv_eq n]
    exact logSecondNumerator_derivatives_vanish (thetaScaledJet t) (L.weierstrassPExcept 0)
      (thetaEtaExpression t) hF hg
      (fun j k => congrFun (thetaScaledJet_iteratedDeriv ht0 j k) 0)
      (thetaScaledJet_zero_at_zero t) (thetaScaledJet_two_at_zero t)
      (L.weierstrassPExcept_zero 0) hc hn
  have horder : (5 : WithTop ℤ) ≤ meromorphicOrderAt W 0 := by
    rw [hW.meromorphicOrderAt_eq]
    exact ENat.monotone_map_iff.mpr Nat.mono_cast
      ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hW).mpr hvanish)
  have hD := thetaWeierstrassDifference_meromorphic ht0 0
  have hM := (hF 0).meromorphicAt
  have hId : MeromorphicAt (id : ℂ → ℂ) 0 := analyticAt_id.meromorphicAt
  change (5 : WithTop ℤ) ≤ meromorphicOrderAt
    (thetaWeierstrassDifference t ht0*(thetaScaledJet t 0)^2*(id : ℂ → ℂ)^2) 0 at horder
  rw [meromorphicOrderAt_mul (hD.mul (hM.pow 2)) (hId.pow 2),
    meromorphicOrderAt_mul hD (hM.pow 2),meromorphicOrderAt_pow hM,
    meromorphicOrderAt_pow hId,thetaScaledJet_zero_meromorphicOrder_of_pos ht,
    meromorphicOrderAt_id] at horder
  have hpos : (1 : WithTop ℤ) ≤ meromorphicOrderAt (thetaWeierstrassDifference t ht0) 0 := by
    rw [← WithTop.add_le_add_iff_right (z := 4) (by simp)]
    norm_num only [mul_one,add_assoc] at horder ⊢
    exact horder
  exact AnalyticAt.of_meromorphicOrderAt_pos (one_pos.trans_le hpos)
    (thetaWeierstrassDifference_zero t ht0)


theorem thetaWeierstrassDifference_analyticAt_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) (z : ℂ) :
    AnalyticAt ℂ (thetaWeierstrassDifference t ht0) z := by
  let L := rhombicPeriodPair t ht0
  by_cases hz : z ∈ L.lattice
  · have h0 := thetaWeierstrassDifference_analyticAt_zero_of_pos ht ht0
    rw [← sub_self z] at h0
    convert h0.comp (f := fun w => w-z) (by fun_prop) using 1
    funext w
    exact (thetaWeierstrassDifference_sub_lattice ht0 w ⟨z,hz⟩).symm
  · have hf : AnalyticAt ℂ (fun w => thetaLogSecond t w-L.weierstrassP w-thetaEtaExpression t) z :=
      ((thetaLogSecond_analyticAt_of_pos ht ht0 hz).sub
        (L.analyticOnNhd_weierstrassP z hz)).sub analyticAt_const
    apply hf.congr
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    change w ∉ (rhombicPeriodPair t ht0).lattice at hw
    simp only [thetaWeierstrassDifference,ite_eq_right hw]
    rfl


theorem thetaWeierstrassDifference_eq_zero_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) (z : ℂ) :
    thetaWeierstrassDifference t ht0 z = 0 := by
  let L := rhombicPeriodPair t ht0
  have hd : Differentiable ℂ (thetaWeierstrassDifference t ht0) :=
    fun w => (thetaWeierstrassDifference_analyticAt_of_pos ht ht0 w).differentiableAt
  have hb := (IsZLattice.isCompact_range_of_periodic L.lattice
    (thetaWeierstrassDifference t ht0) hd.continuous
    (fun x w hw => thetaWeierstrassDifference_add_lattice ht0 x ⟨w,hw⟩)).isBounded
  exact (hd.apply_eq_apply_of_bounded hb z 0).trans (thetaWeierstrassDifference_zero t ht0)


theorem thetaLogSecond_eq_weierstrassP_add_eta_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t)
    {z : ℂ} (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    thetaLogSecond t z = (rhombicPeriodPair t ht0).weierstrassP z+thetaEtaExpression t := by
  have h := thetaWeierstrassDifference_eq_zero_of_pos ht ht0 z
  rw [thetaWeierstrassDifference,ite_eq_right hz] at h
  linear_combination h


theorem thetaG_eq_weierstrassP_of_pos {t : ℝ} (ht : 0 < t) (ht0 : 0 < t) (a : ℝ)
    (ha : (a:ℂ) ∉ (rhombicPeriodPair t ht0).lattice) :
    thetaG t a = (rhombicPeriodPair t ht0).weierstrassP a+thetaEtaExpression t-(Real.pi/t:ℝ) := by
  have h := thetaLogSecond_eq_weierstrassP_add_eta_of_pos ht ht0 ha
  unfold thetaG
  unfold thetaLogSecond at h
  rw [h]


end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaLogSecond_eq_weierstrassP_add_eta_of_pos
