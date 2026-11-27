import TwoAxisHelicoid.CentralLevelThetaFactor
import TwoAxisHelicoid.CentralRatioJetData

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaJet thetaScaledJet

private theorem central_ratio_evaluate_steps (high : Bool) (c e : ℂ) (m p J : ℕ → ℂ) (nz : p 0≠0)
    (law : ∀ n : ℕ, ∑ i ∈ Finset.range (n+1), (n.choose i:ℂ)*J i*p (n-i) =
      ∑ i ∈ Finset.range (n+1), (n.choose i:ℂ)*c^i*e*m (n-i)) :
    jetProgramValue (centralRatioInputs c e m p) (centralRatioProgram high)=J (if high then 3 else 2) := by
  let env := centralRatioInputs c e m p
  have d0 : (centralRatioJetStep 0).value env=J 0 := by
    change e*m 0/p 0=_
    apply (div_eq_iff nz).mpr
    simpa using (law 0).symm
  have d1 : (centralRatioJetStep 1).value (jetCons (J 0) env)=J 1 := by
    change (e*(c*m 0+m 1)-J 0*p 1)/p 0=_
    apply (div_eq_iff nz).mpr
    have h := law 1
    norm_num [Finset.sum_range_succ,Nat.choose] at h
    linear_combination -h
  have d2 : (centralRatioJetStep 2).value (jetCons (J 1) (jetCons (J 0) env))=J 2 := by
    simp only [centralRatioJetStep,BallExpression.value_div,BallExpression.value_pow,BallExpression.value_sub,
      BallExpression.value,BallExpression.value_rational,jetCons,env,centralRatioInputs]
    norm_num1
    apply (div_eq_iff nz).mpr
    have h := law 2
    norm_num [Finset.sum_range_succ,Nat.choose] at h
    linear_combination -h
  cases high with
  | false =>
    change jetProgramValue env (centralRatioProgram false)=J 2
    simp only [centralRatioProgram,Bool.false_eq_true,ite_false,jetProgramValue,d0,d1,d2,jetCons]
  | true =>
    have d3 : (centralRatioJetStep 3).value (jetCons (J 2) (jetCons (J 1) (jetCons (J 0) env)))=J 3 := by
      simp only [centralRatioJetStep,BallExpression.value_div,BallExpression.value_pow,BallExpression.value_sub,
        BallExpression.value,BallExpression.value_rational,jetCons,env,centralRatioInputs]
      norm_num1
      apply (div_eq_iff nz).mpr
      have h := law 3
      norm_num [Finset.sum_range_succ,Nat.choose] at h
      linear_combination -h
    change jetProgramValue env (centralRatioProgram true)=J 3
    simp only [centralRatioProgram,ite_true,jetProgramValue,d0,d1,d2,d3,jetCons]

/-- The recurrence checked in each cell yields the actual second or third
holomorphic derivative, in the coordinate scaled by π/2. -/
theorem central_ratio_derivative_from_jets {t a : ℝ} (ht : 0<t) {z : ℂ}
    (regular : z+a∉(rhombicPeriodPair t ht).lattice) (high : Bool) :
    let K := (Real.pi/2:ℂ)
    let c := ((4*(1-a)/t:ℝ):ℂ)
    let M := fun n => thetaJet t n (Real.pi*(z-a)/2)
    let P := fun n => thetaJet t n (Real.pi*(z+a)/2)
    let n := if high then 3 else 2
    jetProgramValue (centralRatioInputs c (exp (K*c*z)) M P) (centralRatioProgram high) =
      iteratedDeriv n (centralPhaseThetaRatio t a) z/K^n := by
  intro K c M P n
  let R := centralPhaseThetaRatio t a
  let J := fun i => iteratedDeriv i R z/K^i
  let A := fun w : ℂ => thetaScaledJet t 0 (w-a)
  let B := fun w : ℂ => thetaScaledJet t 0 (w+a)
  let E := fun w : ℂ => exp (K*c*w)
  have kn : K≠0 := div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) (by norm_num)
  have nz := mt (thetaScaledJet_zero_iff_lattice_of_pos ht ht (z+a)).mp regular
  have pn := mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht (z+a)).mp regular
  have constEq : ((2*(1-a)*Real.pi/t:ℝ):ℂ)=K*c := by push_cast [K,c]; ring
  have aa : AnalyticAt ℂ A z := (thetaScaledJet_analyticAt ht 0 _).comp (analyticAt_id.sub analyticAt_const)
  have bb : AnalyticAt ℂ B z := (thetaScaledJet_analyticAt ht 0 _).comp (analyticAt_id.add analyticAt_const)
  have ee : AnalyticAt ℂ E z := (analyticAt_const.mul analyticAt_id).cexp
  have rr := centralPhaseThetaRatio_analyticAt (a:=a) ht regular
  have germ : R*B =ᶠ[𝓝 z] E*A := by
    filter_upwards [bb.continuousAt.eventually_ne (show B z≠0 from nz)] with w hw
    change exp (((2*(1-a)*Real.pi/t:ℝ):ℂ)*w)*(A w/B w)*B w=E w*A w
    rw [mul_assoc,div_mul_cancel₀ _ hw,constEq]
  have dm (i : ℕ) : iteratedDeriv i A z=K^i*M i := by
    dsimp only [A]
    rw [iteratedDeriv_comp_sub_const,thetaScaledJet_iteratedDeriv ht,zero_add]
    simp only [thetaScaledJet,K,M]
    rw [show (Real.pi/2:ℂ)*(z-a)=Real.pi*(z-a)/2 by ring]
  have dp (i : ℕ) : iteratedDeriv i B z=K^i*P i := by
    dsimp only [B]
    rw [iteratedDeriv_comp_add_const,thetaScaledJet_iteratedDeriv ht,zero_add]
    simp only [thetaScaledJet,K,P]
    rw [show (Real.pi/2:ℂ)*(z+a)=Real.pi*(z+a)/2 by ring]
  have de (i : ℕ) : iteratedDeriv i E z=(K*c)^i*E z := by
    dsimp only [E]
    rw [iteratedDeriv_cexp_const_mul]
  have dr (i : ℕ) : iteratedDeriv i R z=K^i*J i := by dsimp [J]; field_simp
  apply central_ratio_evaluate_steps high c (E z) M P J pn
  intro j
  have rule := (germ.iteratedDeriv j).self_of_nhds
  rw [iteratedDeriv_mul (rr.contDiffAt) (bb.contDiffAt),iteratedDeriv_mul (ee.contDiffAt) (aa.contDiffAt)] at rule
  apply (mul_right_inj' (pow_ne_zero j kn)).mp
  rw [Finset.mul_sum,Finset.mul_sum]
  have power (i : ℕ) (hi : i∈Finset.range (j+1)) : K^j=K^i*K^(j-i) := by
    rw [← pow_add,Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
  calc
    _ = ∑ i ∈ Finset.range (j+1), (j.choose i:ℂ)*iteratedDeriv i R z*iteratedDeriv (j-i) B z := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [power i hi,dr,dp]
      ring
    _ = _ := rule
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [power i hi,de,dm,mul_pow]
      ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.central_ratio_derivative_from_jets
