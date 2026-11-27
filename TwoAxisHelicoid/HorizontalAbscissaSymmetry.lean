import TwoAxisHelicoid.ThetaParity
import TwoAxisHelicoid.ThetaAReality
import TwoAxisHelicoid.AllHorizontalDerivative

namespace TwoAxisHelicoid
open Complex
open scoped ComplexConjugate
attribute [local irreducible] thetaJet thetaA thetaQuotient

theorem thetaJet_sub_pi (t : ℝ) (j : ℕ) (v : ℂ) :
    thetaJet t j (v-Real.pi) = -thetaJet t j v := by
  have h := thetaJet_add_pi t j (v-Real.pi)
  rw [sub_add_cancel] at h
  linear_combination h

theorem thetaA_reflect_abscissa (t a : ℝ) (z : ℂ) :
    thetaA t (2-a) z = thetaA t a (-z) := by
  have hba : (Real.pi*((2-a:ℝ):ℂ)/2:ℂ) = -(Real.pi*a/2)+Real.pi := by push_cast; ring
  have hma : (Real.pi*(z-((2-a:ℝ):ℂ))/2:ℂ) = Real.pi*(z+a)/2-Real.pi := by push_cast; ring
  have hmn : (Real.pi*(-z-a)/2:ℂ) = -(Real.pi*(z+a)/2) := by ring
  have hzn : (Real.pi*(-z)/2:ℂ) = -(Real.pi*z/2) := by ring
  simp only [thetaA,hba,hma,hmn,hzn,thetaJet_add_pi,thetaJet_sub_pi,
    thetaQuotient,thetaJet_neg]
  norm_num only [Nat.zero_add,Nat.one_add,pow_one,neg_one_mul,neg_neg,even_two,Even.neg_pow,
    one_pow,one_mul,neg_div,div_neg,neg_neg,neg_sq]
  congr 1
  congr 1
  push_cast
  ring

theorem horizontal_period_reflect_abscissa (t a : ℝ) :
    thetaHorizontalPeriod t (2-a) = thetaHorizontalPeriod t a := by
  have he (x : ℝ) : thetaA t (2-a) ((x:ℂ)+I*((t/2:ℝ):ℂ)) =
      conj (thetaA t a (((-x:ℝ):ℂ)+I*((t/2:ℝ):ℂ))) := by
    rw [thetaA_reflect_abscissa]
    have hz : -((x:ℂ)+I*((t/2:ℝ):ℂ)) = conj (((-x:ℝ):ℂ)+I*((t/2:ℝ):ℂ)) := by
      simp only [map_add,map_mul,map_neg,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg]
      ring
    rw [hz,thetaA_conj]
  unfold thetaHorizontalPeriod
  simp_rw [he]
  rw [intervalIntegral.intervalIntegral_conj,Complex.conj_re]
  have hi := intervalIntegral.integral_comp_neg
    (fun x : ℝ => thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ))) (a := (-1:ℝ)) (b := (1:ℝ))
  simpa only [neg_neg] using congrArg (fun v : ℂ => (1/2:ℝ)*v.re) hi

theorem horizontal_period_da_at_one {t : ℝ} (ht : 0 < t) : horizontalPeriodDa t 1 = 0 := by
  have hd := horizontal_period_a_hasDerivAt ht (by norm_num : (1:ℝ) ∈ Set.Ioo 0 2)
  have hd' : HasDerivAt (thetaHorizontalPeriod t) (horizontalPeriodDa t 1) (2-1:ℝ) := by
    norm_num
    exact hd
  have hleft := hd'.comp (h := fun a : ℝ => 2-a) 1 ((hasDerivAt_id (1:ℝ)).const_sub 2)
  have he : (fun a : ℝ => thetaHorizontalPeriod t (2-a)) = thetaHorizontalPeriod t :=
    funext (horizontal_period_reflect_abscissa t)
  have hleft' : HasDerivAt (thetaHorizontalPeriod t) (-horizontalPeriodDa t 1) 1 := by
    simpa only [Function.comp_def,he,mul_neg_one] using hleft
  have h := hd.unique hleft'
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.horizontal_period_reflect_abscissa
#print axioms TwoAxisHelicoid.horizontal_period_da_at_one
