import TwoAxisHelicoid.ThetaSigmaZeta

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaJet thetaScaledJet thetaSigma

noncomputable def quadraticExp (c z : ℂ) : ℂ := Complex.exp (c*z^2/2)

theorem quadraticExp_hasDerivAt (c z : ℂ) :
    HasDerivAt (quadraticExp c) (c*z*quadraticExp c z) z := by
  have hd := ((((hasDerivAt_id z).pow 2).const_mul c).div_const 2).cexp
  convert hd using 1
  · rfl
  · simp only [quadraticExp,Pi.pow_apply,id_eq]
    ring

theorem quadraticExp_deriv (c : ℂ) : deriv (quadraticExp c) = fun z => c*z*quadraticExp c z :=
  funext (fun z => (quadraticExp_hasDerivAt c z).deriv)

theorem quadraticExp_analyticAt (c z : ℂ) : AnalyticAt ℂ (quadraticExp c) z :=
  (show Differentiable ℂ (quadraticExp c) from
    fun w => (quadraticExp_hasDerivAt c w).differentiableAt).analyticAt z

theorem quadraticExp_zero (c : ℂ) : quadraticExp c 0 = 1 := by simp [quadraticExp]

theorem quadraticExp_iterated_one_zero (c : ℂ) : iteratedDeriv 1 (quadraticExp c) 0 = 0 := by
  rw [iteratedDeriv_one,(quadraticExp_hasDerivAt c 0).deriv]
  simp

theorem quadraticExp_iterated_two_zero (c : ℂ) : iteratedDeriv 2 (quadraticExp c) 0 = c := by
  rw [show 2 = 1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,quadraticExp_deriv]
  have hd := ((hasDerivAt_id (0:ℂ)).const_mul c).mul (quadraticExp_hasDerivAt c 0)
  change HasDerivAt (fun z => c*z*quadraticExp c z) _ 0 at hd
  simpa [quadraticExp_zero] using hd.deriv

theorem thetaSigma_second_zero {t : ℝ} (ht : 0 < t) : iteratedDeriv 2 (thetaSigma t) 0 = 0 := by
  have hD (n : ℕ) : iteratedDeriv n (thetaScaledJet t 0) 0 = thetaScaledJet t n 0 := by
    simpa using congrFun (thetaScaledJet_iteratedDeriv ht 0 n) 0
  have he : thetaSigma t = fun z => quadraticExp (thetaEtaExpression t) z*
      thetaScaledJet t 0 z/thetaScaledJet t 1 0 := by unfold thetaSigma quadraticExp; rfl
  rw [he,iteratedDeriv_div_const,iteratedDeriv_fun_mul
    (quadraticExp_analyticAt (thetaEtaExpression t) 0).contDiffAt
    (thetaScaledJet_analyticAt ht 0 0).contDiffAt]
  simp [Finset.sum_range_succ,Nat.choose,hD,quadraticExp_zero,
    quadraticExp_iterated_one_zero,thetaScaledJet_zero_at_zero,thetaScaledJet_two_at_zero]

theorem thetaSigma_third_zero {t : ℝ} (ht : 43/50 ≤ t) : iteratedDeriv 3 (thetaSigma t) 0 = 0 := by
  have ht0 : 0 < t := by linarith
  have hD (n : ℕ) : iteratedDeriv n (thetaScaledJet t 0) 0 = thetaScaledJet t n 0 := by
    simpa using congrFun (thetaScaledJet_iteratedDeriv ht0 0 n) 0
  have he : thetaSigma t = fun z => quadraticExp (thetaEtaExpression t) z*
      thetaScaledJet t 0 z/thetaScaledJet t 1 0 := by unfold thetaSigma quadraticExp; rfl
  rw [he,iteratedDeriv_div_const,iteratedDeriv_fun_mul
    (quadraticExp_analyticAt (thetaEtaExpression t) 0).contDiffAt
    (thetaScaledJet_analyticAt ht0 0 0).contDiffAt]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,hD]
  norm_num [Nat.choose,quadraticExp_zero,quadraticExp_iterated_one_zero,
    quadraticExp_iterated_two_zero,thetaScaledJet_zero_at_zero,thetaScaledJet_one_ne_zero ht]
  unfold thetaEtaExpression
  field_simp [thetaScaledJet_one_ne_zero ht]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaSigma_third_zero
