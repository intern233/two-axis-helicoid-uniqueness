import TwoAxisHelicoid.ThetaWeierstrassDifference

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaJet thetaScaledJet thetaLogSecond

theorem thetaScaledJet_zero_meromorphicOrder {t : ℝ} (ht : 43/50 ≤ t) :
    meromorphicOrderAt (thetaScaledJet t 0) 0 = 1 := by
  have ht0 : 0 < t := by linarith
  have hf := thetaScaledJet_analyticAt ht0 0 0
  have hd : deriv (thetaScaledJet t 0) 0 ≠ 0 := by
    rw [(thetaScaledJet_hasDerivAt ht0 0 0).deriv]
    exact thetaScaledJet_one_ne_zero ht
  rw [hf.meromorphicOrderAt_eq,
    hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (thetaScaledJet_zero_at_zero t) hd]
  norm_num

theorem thetaWeierstrassDifference_analyticAt_zero {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) :
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
  have he : W =ᶠ[𝓝 0] N := thetaWeierstrassDifference_weighted ht ht0
  have hW : AnalyticAt ℂ W 0 := hN.congr he.symm
  have hc : 3*thetaEtaExpression t*thetaScaledJet t 1 0+thetaScaledJet t 3 0 = 0 := by
    unfold thetaEtaExpression
    field_simp [thetaScaledJet_one_ne_zero ht]
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
    meromorphicOrderAt_pow hId,thetaScaledJet_zero_meromorphicOrder ht,
    meromorphicOrderAt_id] at horder
  have hpos : (1 : WithTop ℤ) ≤ meromorphicOrderAt (thetaWeierstrassDifference t ht0) 0 := by
    rw [← WithTop.add_le_add_iff_right (z := 4) (by simp)]
    norm_num only [mul_one,add_assoc] at horder ⊢
    exact horder
  exact AnalyticAt.of_meromorphicOrderAt_pos (one_pos.trans_le hpos)
    (thetaWeierstrassDifference_zero t ht0)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaWeierstrassDifference_analyticAt_zero
