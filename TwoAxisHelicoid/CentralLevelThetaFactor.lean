import TwoAxisHelicoid.ActualGaussHeightCorrection
import TwoAxisHelicoid.SigmaRealPositive

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate
attribute [local irreducible] thetaScaledJet thetaSigma thetaEtaExpression

/-- Theta quotient after removing the rotation due to physical height. Its
poles are outside the closed saddle-to-midpoint parameter rectangle. -/
noncomputable def centralPhaseThetaRatio (t a : ℝ) (z : ℂ) : ℂ :=
  exp (((2*(1-a)*Real.pi/t:ℝ):ℂ)*z) *
    (thetaScaledJet t 0 (z-a) / thetaScaledJet t 0 (z+a))

theorem closed_heightGaussFactor_theta_ratio {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (closed : thetaG t a=0) (z : ℂ) :
    heightGaussFactor t a 1 ht z = -centralPhaseThetaRatio t a z := by
  let E := thetaEtaExpression t
  let P := (rhombicPeriodPair t ht).weierstrassP a
  have h := thetaG_eq_weierstrassP_of_pos ht ht a
    (real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2]))
  rw [closed] at h
  have period : E+P=((Real.pi/t:ℝ):ℂ) := by
    dsimp [E,P]
    linear_combination -h
  have ratio : thetaSigma t (z-a)/thetaSigma t (z+a) =
      exp (-2*E*a*z) * (thetaScaledJet t 0 (z-a)/thetaScaledJet t 0 (z+a)) := by
    unfold thetaSigma
    rw [div_div_div_cancel_right₀ (thetaScaledJet_one_ne_zero_of_pos ht),mul_div_mul_comm,← exp_sub]
    congr 2
    dsimp [E]
    ring
  have exponent : (2*E-2*((a:ℂ)-1)*P)*z+(-2*E*a*z)=((2*(1-a)*Real.pi/t:ℝ):ℂ)*z := by
    rw [show 2*(1-a)*Real.pi/t=2*(1-a)*(Real.pi/t) by ring,ofReal_mul,← period]
    push_cast
    ring
  unfold heightGaussFactor
  simp only [Int.cast_one,mul_one]
  rw [mul_div_assoc,ratio,centralPhaseThetaRatio,neg_mul,← mul_assoc,← exp_add,exponent]

/-- On the physical central level the two components of the Gauss map
are a fixed quarter-turn of this quotient, with strictly positive scale. -/
theorem central_level_gauss_theta_ratio {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (closed : thetaG t a=0) {z : ℂ} (level : (actualComplexHeight t a 1 ht z).re=0) :
    ∃ s : ℝ, 0<s ∧ thetaGauss t a 1 z=I*(s:ℂ)*centralPhaseThetaRatio t a z := by
  let H := actualComplexHeight t a 1 ht z
  let u : ℝ := -(2*(a-1)*H.im)
  have realExponent : I*((2*(a-(1:ℤ))/1:ℝ):ℂ)*H=(u:ℂ) := by
    apply Complex.ext <;> simp [u,H,Complex.mul_re,Complex.mul_im,level]
  have ident := gauss_height_factor_identity (a:=a) (c:=1) ht one_ne_zero 1 z
  rw [closed_heightGaussFactor_theta_ratio ht ha closed,realExponent,← ofReal_exp] at ident
  refine ⟨Real.exp u,Real.exp_pos _,?_⟩
  calc
    thetaGauss t a 1 z = -I*(I*thetaGauss t a 1 z) := by rw [← mul_assoc,neg_mul,I_mul_I,neg_neg,one_mul]
    _ = _ := by rw [ident]; ring

theorem centralPhaseThetaRatio_conj (t a : ℝ) (z : ℂ) :
    centralPhaseThetaRatio t a (conj z)=conj (centralPhaseThetaRatio t a z) := by
  simp only [centralPhaseThetaRatio,map_mul,map_div₀,← Complex.exp_conj,conj_ofReal]
  rw [← thetaScaledJet_conj,← thetaScaledJet_conj]
  simp

theorem centralPhaseThetaRatio_real (t a x : ℝ) :
    (centralPhaseThetaRatio t a (x:ℂ)).im=0 := by
  have h := congrArg Complex.im (centralPhaseThetaRatio_conj t a (x:ℂ))
  simp only [conj_ofReal,conj_im] at h
  linarith

theorem centralPhaseThetaRatio_saddle (t a : ℝ) : centralPhaseThetaRatio t a (a:ℂ)=0 := by
  simp [centralPhaseThetaRatio,thetaScaledJet_zero_at_zero]

theorem centralPhaseThetaRatio_real_segment {t a x : ℝ} (ht : 43/50≤t)
    (ha : a∈Ioo (0:ℝ) 1) (hx : x∈Ioo (0:ℝ) a) :
    (centralPhaseThetaRatio t a (x:ℂ)).re<0 := by
  have minus := thetaScaledJet_zero_re_pos ht (x:=a-x) (by linarith [hx.2]) (by linarith [hx.1,ha.2])
  have plus := thetaScaledJet_zero_re_pos ht (x:=x+a) (by linarith [hx.1,ha.1]) (by linarith [hx.2,ha.2])
  have σ : thetaScaledJet t 0 ((x:ℂ)-a)= -thetaScaledJet t 0 (((a-x:ℝ):ℂ)) := by
    rw [show (x:ℂ)-a= -(((a-x:ℝ):ℂ)) by push_cast; ring,thetaScaledJet_neg]
    simp
  rw [centralPhaseThetaRatio,σ,← ofReal_add,← ofReal_mul,← ofReal_exp,thetaScaledJet_eq_ofReal t 0 (a-x),
    thetaScaledJet_eq_ofReal t 0 (x+a),← ofReal_neg,← ofReal_div,← ofReal_mul,ofReal_re]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) (div_neg_of_neg_of_pos (neg_lt_zero.mpr minus) plus)

theorem centralPhaseThetaRatio_analyticAt {t a : ℝ} (ht : 0<t) {z : ℂ}
    (regular : z+a∉(rhombicPeriodPair t ht).lattice) : AnalyticAt ℂ (centralPhaseThetaRatio t a) z := by
  have hn := mt (thetaScaledJet_zero_iff_lattice_of_pos ht ht (z+a)).mp regular
  exact ((analyticAt_const.mul analyticAt_id).cexp).mul
    (((thetaScaledJet_analyticAt ht 0 _).comp (analyticAt_id.sub analyticAt_const)).div
      ((thetaScaledJet_analyticAt ht 0 _).comp (analyticAt_id.add analyticAt_const)) hn)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.central_level_gauss_theta_ratio
#print axioms TwoAxisHelicoid.centralPhaseThetaRatio_real_segment
