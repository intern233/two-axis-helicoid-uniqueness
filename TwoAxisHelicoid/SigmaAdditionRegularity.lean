import TwoAxisHelicoid.SigmaAdditionDifference

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaSigma

theorem thetaSigma_meromorphicOrder_zero {t : ℝ} (ht : 43/50 ≤ t) :
    meromorphicOrderAt (thetaSigma t) 0 = 1 := by
  have ht0 : 0 < t := by linarith
  have hf := thetaSigma_analyticAt ht0 0
  have hd : deriv (thetaSigma t) 0 ≠ 0 := by rw [(thetaSigma_hasDerivAt_zero ht).deriv]; norm_num
  rw [hf.meromorphicOrderAt_eq,hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (thetaSigma_zero t) hd]
  norm_num

theorem sigmaAdditionDifference_analyticAt_zero {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) {a : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht0).lattice) :
    AnalyticAt ℂ (sigmaAdditionDifference t ht0 a) 0 := by
  let L := rhombicPeriodPair t ht0
  let U : ℂ → ℂ := fun z => thetaSigma t (z-a)
  let V : ℂ → ℂ := fun z => thetaSigma t (z+a)
  let g : ℂ → ℂ := fun z => L.weierstrassPExcept 0 z-L.weierstrassP a
  let W := sigmaAdditionDifference t ht0 a*(thetaSigma t)^2*(id : ℂ → ℂ)^2
  let N := sigmaAdditionNumerator (thetaSigma t) U V g (thetaSigma t a)
  have hf := thetaSigma_analyticAt ht0 0
  have hu : AnalyticAt ℂ U 0 :=
    (thetaSigma_analyticAt ht0 (0-a)).comp (f := fun z => z-a) (by fun_prop)
  have hv : AnalyticAt ℂ V 0 :=
    (thetaSigma_analyticAt ht0 (0+a)).comp (f := fun z => z+a) (by fun_prop)
  have hg : AnalyticAt ℂ g 0 := (L.analyticAt_weierstrassPExcept 0).sub analyticAt_const
  have hsa := mt (thetaSigma_zero_iff_lattice ht ht0 a).mp ha
  have hN : AnalyticAt ℂ N 0 := by
    unfold N sigmaAdditionNumerator
    simp only [div_eq_mul_inv]
    fun_prop
  have he : W =ᶠ[𝓝 0] N := sigmaAdditionDifference_weighted ht ht0 ha
  have hW : AnalyticAt ℂ W 0 := hN.congr he.symm
  have hu0 : U 0 = -thetaSigma t a := by simp [U,thetaSigma_neg]
  have hv0 : V 0 = thetaSigma t a := by simp [V]
  have hu1 : deriv U 0 = deriv (thetaSigma t) a := by
    simpa only [iteratedDeriv_one,zero_sub,thetaSigma_deriv_neg] using
      congrFun (iteratedDeriv_comp_sub_const 1 (thetaSigma t) a) 0
  have hv1 : deriv V 0 = deriv (thetaSigma t) a := by
    simpa only [iteratedDeriv_one,zero_add] using
      congrFun (iteratedDeriv_comp_add_const 1 (thetaSigma t) a) 0
  have hu2 : iteratedDeriv 2 U 0 = -iteratedDeriv 2 (thetaSigma t) a := by
    simpa only [zero_sub,thetaSigma_second_neg] using
      congrFun (iteratedDeriv_comp_sub_const 2 (thetaSigma t) a) 0
  have hv2 : iteratedDeriv 2 V 0 = iteratedDeriv 2 (thetaSigma t) a := by
    simpa only [zero_add] using congrFun (iteratedDeriv_comp_add_const 2 (thetaSigma t) a) 0
  have hg0 : g 0 = -L.weierstrassP a := by simp [g]
  have hvanish (n : ℕ) (hn : n < 5) : iteratedDeriv n W 0 = 0 := by
    rw [he.iteratedDeriv_eq n]
    exact sigmaAdditionNumerator_derivatives_vanish (thetaSigma t) U V g
      (thetaSigma t a) (deriv (thetaSigma t) a) (iteratedDeriv 2 (thetaSigma t) a) (L.weierstrassP a)
      hf hu hv hg hsa (thetaSigma_zero t) (thetaSigma_hasDerivAt_zero ht).deriv
      (thetaSigma_second_zero ht0) (thetaSigma_third_zero ht) hu0 hv0 hu1 hv1 hu2 hv2 hg0
      (thetaSigma_wronskian ht ht0 ha) hn
  have horder : (5 : WithTop ℤ) ≤ meromorphicOrderAt W 0 := by
    rw [hW.meromorphicOrderAt_eq]
    exact ENat.monotone_map_iff.mpr Nat.mono_cast
      ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hW).mpr hvanish)
  have hD := sigmaAdditionDifference_meromorphic ht0 a 0
  have hM := hf.meromorphicAt
  have hId : MeromorphicAt (id : ℂ → ℂ) 0 := analyticAt_id.meromorphicAt
  change (5 : WithTop ℤ) ≤ meromorphicOrderAt
    (sigmaAdditionDifference t ht0 a*(thetaSigma t)^2*(id : ℂ → ℂ)^2) 0 at horder
  rw [meromorphicOrderAt_mul (hD.mul (hM.pow 2)) (hId.pow 2),
    meromorphicOrderAt_mul hD (hM.pow 2),meromorphicOrderAt_pow hM,
    meromorphicOrderAt_pow hId,thetaSigma_meromorphicOrder_zero ht,meromorphicOrderAt_id] at horder
  have hpos : (1 : WithTop ℤ) ≤ meromorphicOrderAt (sigmaAdditionDifference t ht0 a) 0 := by
    rw [← WithTop.add_le_add_iff_right (z := 4) (by simp)]
    norm_num only [mul_one,add_assoc] at horder ⊢
    exact horder
  exact AnalyticAt.of_meromorphicOrderAt_pos (one_pos.trans_le hpos)
    (sigmaAdditionDifference_zero t ht0 a)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.sigmaAdditionDifference_analyticAt_zero
