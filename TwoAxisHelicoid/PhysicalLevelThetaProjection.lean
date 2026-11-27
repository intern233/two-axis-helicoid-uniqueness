import TwoAxisHelicoid.PhysicalLevelThetaPhase
import TwoAxisHelicoid.TorusThetaDirection
import TwoAxisHelicoid.RegularHorizontalFiberTangent
import TwoAxisHelicoid.RegularHorizontalFibers
import TwoAxisHelicoid.HeightEndAxisCenter

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

/-- A strictly negative real part of the corrected theta direction on
one entire regular level gives a strictly monotone linear spatial
projection of the full horizontal line and hence spatial injectivity. -/
theorem actual_height_level_injective_of_theta_direction {t a h : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (root : thetaG t a=0) (hn : h≠0) {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → X (z+ω)=X z)
    (neg : ∀ z, z∉(rhombicPeriodPair t ht).lattice → X z 2=X 1 2+h → (torusThetaDirection t a z).re<0) :
    let L := rhombicPeriodPair t ht
    let Y := fun p : PuncturedPeriodTorus L => periodTorusLift L X per p.1
    InjOn Y {p | Y p 2=X 1 2+h} := by
  intro L Y
  obtain ⟨g,s,q,cg,data,_,rq⟩ := actual_regular_horizontal_fibers ht ha (one_ne_zero : (1:ℝ)≠0) d per hn
  have same (y : ℝ) : Y (q y)=X (g y) := congrArg (periodTorusLift L X per) (data y).2.2
  have lev (y : ℝ) : X (g y) 2=X 1 2+h := by
    have mem : q y∈range q := mem_range_self y
    rw [rq] at mem
    exact (congrFun (same y) 2).symm.trans mem
  let E := exp (I*((2*(a-1)*s:ℝ):ℂ))
  let proj := fun v : Fin 3 → ℝ => E.re*v 0+E.im*v 1
  let f := fun y : ℝ => proj (X (g y))
  have decreasing : StrictAnti f := by
    apply strictAnti_of_deriv_neg
    intro y
    let G := thetaGauss t a 1 (g y)
    let k := ((normSq G)⁻¹+1)/2
    let R := torusThetaDirection t a (g y)
    let b := Real.exp (-(2*(a-1))*(actualComplexHeight t a 1 ht (g y)).im)*
      Real.exp (2*(1-a)*Real.pi/t*(g y).re)
    have bp : 0<b := mul_pos (Real.exp_pos _) (Real.exp_pos _)
    have kp : 0<k := div_pos (add_pos_of_nonneg_of_pos (inv_nonneg.mpr (normSq_nonneg _)) one_pos) (by norm_num)
    have e := physical_level_gauss_theta_ratio ht ha root (g y)
    dsimp only at e
    have fixed : (actualComplexHeight t a 1 ht (g y)).re=s := congrArg re (data y).2.1
    rw [fixed,theta_ratio_torus_direction] at e
    have ge : G=I*E*(b:ℂ)*R := calc
      G=I*E*(Real.exp (-(2*(a-1))*(actualComplexHeight t a 1 ht (g y)).im):ℂ)*
        ((Real.exp (2*(1-a)*Real.pi/t*(g y).re):ℂ)*R) := e
      _ = _ := by dsimp only [b]; push_cast; ring
    have neq : X (g y) 2≠X 1 2 := fun eq => hn (by linarith [lev y])
    have vel := (actual_regular_horizontal_fiber_tangent ht ha one_ne_zero d per cg (fun x => (data x).2.1) (data y).1 neq).2
    have d₀ := (hasDerivAt_pi.mp vel 0).const_mul E.re
    have d₁ := (hasDerivAt_pi.mp vel 1).const_mul E.im
    have df : HasDerivAt f (E.re*(k*G.im)+E.im*(-k*G.re)) y := d₀.add d₁
    have unit : E.re^2+E.im^2=1 := by
      have n : ‖E‖=1 := by simp [E,norm_exp,Complex.mul_re]
      have eq : E.re^2+E.im^2=‖E‖^2 := by simpa [Complex.normSq_apply,pow_two] using Complex.normSq_eq_norm_sq E
      rw [eq,n,one_pow]
    have realNeg := neg _ (data y).1 (lev y)
    have alg : E.re*(k*G.im)+E.im*(-k*G.re)=k*b*R.re := by
      rw [ge]
      simp only [Complex.mul_re,Complex.mul_im,I_re,I_im,ofReal_re,ofReal_im,one_mul,zero_mul,zero_add,
        zero_sub,mul_zero,sub_zero]
      linear_combination k*b*R.re*unit
    rw [df.deriv,alg]
    exact mul_neg_of_pos_of_neg (mul_pos kp bp) realNeg
  rw [← rq]
  rintro _ ⟨u,rfl⟩ _ ⟨v,rfl⟩ eq
  have fe : f u=f v := congrArg proj ((same u).symm.trans (eq.trans (same v)))
  exact congrArg q (decreasing.injective fe)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_height_level_injective_of_theta_direction
