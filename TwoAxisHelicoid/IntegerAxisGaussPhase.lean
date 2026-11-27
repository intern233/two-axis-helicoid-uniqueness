import TwoAxisHelicoid.AxisWindingRestriction
import TwoAxisHelicoid.ActualComplexHeight

namespace TwoAxisHelicoid
open Set Complex MeasureTheory
open scoped ComplexConjugate
attribute [local irreducible] thetaGauss thetaZeta thetaEtaExpression

theorem integerAxis_regular_points {t a y : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) (2*t)) :
    I*(y : ℂ) ∉ (rhombicPeriodPair t ht).lattice ∧
    I*(y : ℂ)-a ∉ (rhombicPeriodPair t ht).lattice ∧
    I*(y : ℂ)+a ∉ (rhombicPeriodPair t ht).lattice := by
  have hp : |a| < 1 := by simpa [abs_of_pos ha.1] using ha.2
  refine ⟨?_,?_,?_⟩
  · simpa only [Complex.ofReal_zero,zero_add] using
      rhombic_vertical_strip_not_mem ht (by norm_num : (0 : ℝ) ∈ Ioo (-1) 1) hy
  · simpa only [Complex.ofReal_neg,show -(a : ℂ)+(y : ℂ)*I = I*(y : ℂ)-a by ring] using
      rhombic_noninteger_vertical_not_mem ht (x := -a) (by simpa using hp) (neg_ne_zero.mpr ha.1.ne') y
  · simpa only [show (a : ℂ)+(y : ℂ)*I = I*(y : ℂ)+a by ring] using
      rhombic_noninteger_vertical_not_mem ht hp ha.1.ne' y

theorem axisClosedRegularOmega_real (t a y : ℝ) (m : ℤ) :
    ((axisClosedRegularOmega t a m (I*y)).re : ℂ) = axisClosedRegularOmega t a m (I*y) := by
  let z := I*(y : ℂ)
  have hm : conj (z-a) = -(z+a) := by simp [z]; ring
  have h1 := thetaZeta_conj t (z-a)
  rw [hm,thetaZeta_neg] at h1
  apply Complex.ext
  · rfl
  · have hh := congrArg Complex.im h1
    simp only [Complex.neg_im,Complex.conj_im,neg_inj] at hh
    change 0 = (axisClosedRegularOmega t a m z).im
    simp [axisClosedRegularOmega,Complex.mul_im,Complex.div_ofReal_im,thetaEtaExpression_real,hh]

theorem integerAxisPhase_hasDerivAt {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    (m : ℤ) (y : ℝ) : HasDerivAt (integerAxisPhase t a m)
      (axisClosedRegularOmega t a m (I*y)).re y := by
  have hc := Complex.continuous_re.comp (axisClosedRegularOmega_continuous ht ha m)
  exact (hc.integral_hasStrictDerivAt t y).hasDerivAt

/-- Along the vertical cycle the integral phase is the actual argument
increment of the Gauss map after subtracting the helicoidal height rotation. -/
theorem thetaGauss_integerAxisPhase_identity {t a c y : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hG : thetaG t a = 0) (hc : c ≠ 0) (m : ℤ)
    (hy : y ∈ Ioo (0 : ℝ) (2*t)) :
    let α : ℂ := ((2*(a-(m:ℝ))/c : ℝ) : ℂ)
    let h := fun u : ℝ => actualComplexHeight t a c ht (I*u)
    thetaGauss t a m (I*y) = thetaGauss t a m (I*t) *
      Complex.exp (I*(α*(h y-h t)+(integerAxisPhase t a m y : ℂ))) := by
  dsimp only
  let α : ℂ := ((2*(a-(m:ℝ))/c : ℝ) : ℂ)
  let h := fun u : ℝ => actualComplexHeight t a c ht (I*u)
  let g := fun u : ℝ => thetaGauss t a m (I*u)
  let δ := fun u : ℝ => (integerAxisPhase t a m u : ℂ)
  let Q := fun u : ℝ => g u * Complex.exp (-I*(α*h u+δ u))
  have hQ (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) (2*t)) : HasDerivAt Q 0 u := by
    obtain ⟨hz,hm,hp⟩ := integerAxis_regular_points ht ha hu
    let z := I*(u : ℂ)
    let D := coordinateData t a c ht z 2
    let Ω := axisClosedRegularOmega t a m z
    let A := thetaGaussLogDerivative t a ht m z
    have hΩ : A-I*α*D = Ω := by
      have he := axisClosedRegularOmega_actual_differential ht ha hG hc m hz hm hp
      rw [thetaGauss_log_derivative ht a m hz hm hp] at he
      exact he
    have hg' : HasDerivAt g ((g u*A)*I) u := by
      simpa only [Function.comp_def,id_eq,mul_one] using!
        ((thetaGauss_hasDerivAt ht a m hz hm hp).comp (u : ℂ) ((hasDerivAt_id (u : ℂ)).const_mul I)).comp_ofReal
    have hh' : HasDerivAt h (D*I) u := by
      simpa only [Function.comp_def,id_eq,mul_one] using!
        ((actualComplexHeight_hasDerivAt (a := a) (c := c) ht hz).comp (u : ℂ)
          ((hasDerivAt_id (u : ℂ)).const_mul I)).comp_ofReal
    have hδ' : HasDerivAt δ Ω u := by
      change HasDerivAt δ (axisClosedRegularOmega t a m (I*u)) u
      rw [← axisClosedRegularOmega_real t a u m]
      exact (integerAxisPhase_hasDerivAt ht ha m u).ofReal_comp
    have hd := hg'.mul ((((hh'.const_mul α).add hδ').const_mul (-I)).cexp)
    convert hd using 1
    rw [← hΩ]
    ring
  have he : Q y = Q t := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0 : ℝ) (2*t)).isPreconnected
    (fun u hu => (hQ u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hQ u hu).deriv) hy ⟨ht,by linarith⟩
  have hh : g y = g t * Complex.exp (I*(α*(h y-h t)+δ y)) := by
    have hh := congrArg (fun v => v*Complex.exp (I*(α*h y+δ y))) he
    dsimp only [Q] at hh
    rw [mul_assoc,← Complex.exp_add,show -I*(α*h y+δ y)+I*(α*h y+δ y) = 0 by ring,
      Complex.exp_zero,mul_one,mul_assoc,← Complex.exp_add] at hh
    simpa only [δ,integerAxisPhase_midpoint,Complex.ofReal_zero,add_zero,
      show -I*(α*h t)+I*(α*h y+(integerAxisPhase t a m y : ℂ)) =
        I*(α*(h y-h t)+(integerAxisPhase t a m y : ℂ)) by ring] using hh
  exact hh

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.thetaGauss_integerAxisPhase_identity
