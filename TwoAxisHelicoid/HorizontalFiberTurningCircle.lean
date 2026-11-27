import TwoAxisHelicoid.QuarterRelativeGaussCoordinate
import TwoAxisHelicoid.RegularHorizontalFiberTangent
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology ComplexConjugate

/-- Signed turning speed for the horizontal tangent, in the imaginary
height coordinate. Writing B = 1/(℘−℘(a)) makes its sign a single
affine inequality in Re B. -/
theorem horizontal_gauss_turning_formula {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {z : ℂ} (hz : z∈complexOpenRect 0 1 0 t) :
    let L := rhombicPeriodPair t ht
    let B := (L.weierstrassP z-L.weierstrassP a)⁻¹
    let D := (L.derivWeierstrassP a).re
    let C := axisConstant t ht a
    let G := thetaGauss t a 1
    let h := coordinateData t a 1 ht z 2
    0<B.im ∧ 0<C ∧ D<0 ∧
      (deriv G z/G z/h).re=2*B.im*(C+D*B.re) := by
  intro L B D C G h
  let P := L.weierstrassP z-L.weierstrassP a
  have rep : (z.re:ℂ)+I*z.im=z := by apply Complex.ext <;> simp
  have pn : P.im<0 := by
    have s := rhombic_weierstrassP_quarter_im_neg ht hz.1 hz.2
    rw [rep] at s
    simpa [P,L,sub_im,rhombic_weierstrassP_real] using s
  have nz : P≠0 := fun e => pn.ne (by rw [e]; rfl)
  have bi : 0<B.im := by change 0<(P⁻¹).im; rw [Complex.inv_im]; exact div_pos (neg_pos.mpr pn) (normSq_pos.mpr nz)
  have off : z∉L.lattice := rhombic_horizontal_strip_not_mem ht hz.2
  have m : z-a∉L.lattice := rhombic_horizontal_strip_not_mem ht (by change (z-a).im∈Ioo 0 t; simpa using hz.2)
  have p : z+a∉L.lattice := rhombic_horizontal_strip_not_mem ht (by change (z+a).im∈Ioo 0 t; simpa using hz.2)
  have ζ : (thetaZeta t a).im=0 := by
    have k := congrArg im (thetaZeta_conj t (a:ℂ))
    simp only [conj_ofReal,conj_im] at k
    linarith
  have constEq : 2*(thetaEtaExpression t-thetaZeta t a+(1-a)*L.weierstrassP a)=2*(C:ℂ) := by
    apply Complex.ext <;> simp [C,axisConstant,L,Complex.mul_re,Complex.mul_im,thetaEtaExpression_real,ζ,rhombic_weierstrassP_real]
  have reg : axisRegularCoefficient t ht a z=2*(C:ℂ)+(D:ℂ)*B := by
    change _+L.derivWeierstrassP a/P=_
    rw [constEq,real_wp_derivative_as_real ht ha,div_eq_mul_inv]
  have hval : h=I*P := by change I*(1:ℂ)*P=_; rw [mul_one]
  have hn : h≠0 := hval ▸ mul_ne_zero I_ne_zero nz
  have rel := actualGauss_end_regular_coefficient (c:=1) ht ha one_ne_zero off m p
  simp only [div_one] at rel
  have logEq : deriv G z/G z=I*(((2*(a-1):ℝ):ℂ))*h+(2*(C:ℂ)+(D:ℂ)*B) := by
    rw [← reg]
    exact (sub_eq_iff_eq_add.mp rel).trans (add_comm _ _)
  have quotient : deriv G z/G z/h=I*(((2*(a-1):ℝ):ℂ)) + (-I)*((2*(C:ℂ)+(D:ℂ)*B)*B) := by
    rw [logEq,add_div,mul_div_cancel_right₀ _ hn,hval,div_eq_mul_inv,mul_inv_rev,inv_I]
    dsimp only [B,P]
    ring
  refine ⟨bi,axisConstant_pos ht ha,rhombic_weierstrassP_derivative_real_neg_of_pos ht ht ha.1 ha.2,?_⟩
  rw [quotient]
  simp [Complex.mul_re,Complex.mul_im]
  ring

/-- At a parameter on a horizontal height line, the relative argument
of the actual Gauss map is a local direction angle of its horizontal
tangent. Its derivative is positive, zero or negative according to the
position of the reciprocal ℘-coordinate relative to one vertical line. -/
theorem actual_horizontal_tangent_turning_test {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {γ : ℝ → ℂ} {s y : ℝ} (continuity : ContinuousAt γ y)
    (height : ∀ u, actualComplexHeight t a 1 ht (γ u)=⟨s,u⟩) (hz : γ y∈complexOpenRect 0 1 0 t) :
    let L := rhombicPeriodPair t ht
    let B := (L.weierstrassP (γ y)-L.weierstrassP a)⁻¹
    let G := thetaGauss t a 1
    let θ := fun u => Complex.arg (G (γ u)/G (γ y))
    let threshold := axisConstant t ht a/ -(L.derivWeierstrassP a).re
    θ y=0 ∧ DifferentiableAt ℝ θ y ∧
      (0<deriv θ y ↔ B.re<threshold) ∧ (deriv θ y=0 ↔ B.re=threshold) ∧
      (deriv θ y<0 ↔ threshold<B.re) := by
  intro L B G θ threshold
  let z := γ y
  let h := coordinateData t a 1 ht z 2
  let C := axisConstant t ht a
  let D := (L.derivWeierstrassP a).re
  obtain ⟨bi,cp,dn,eq⟩ := horizontal_gauss_turning_formula ht ha hz
  have negD : 0< -D := neg_pos.mpr dn
  have off : z∉L.lattice := rhombic_horizontal_strip_not_mem ht hz.2
  have m : z-a∉L.lattice := rhombic_horizontal_strip_not_mem ht (by change (z-a).im∈Ioo 0 t; simpa using hz.2)
  have p : z+a∉L.lattice := rhombic_horizontal_strip_not_mem ht (by change (z+a).im∈Ioo 0 t; simpa using hz.2)
  have hn : h≠0 := by
    change I*(1:ℂ)*(_-_)≠0
    exact mul_ne_zero (mul_ne_zero I_ne_zero one_ne_zero)
      (weierstrass_sub_ne_zero_of_sigma ht (real_not_mem_rhombic_lattice_of_pos ht ha.1 (ha.2.trans (by norm_num))) off m p)
  have gg : G z≠0 := thetaGauss_ne_zero ht a 1 m p
  have g' := vertical_complex_coordinate_lift_derivative (actualComplexHeight_hasDerivAt ht off) hn continuity height
  have d := (thetaGauss_hasDerivAt ht a 1 off m p).differentiableAt.hasDerivAt
  let q := fun u => G (γ u)/G z
  have dq : HasDerivAt q ((I/h*deriv G z)/G z) y := (d.scomp y g').div_const _
  have q1 : q y=1 := div_self gg
  have logD := (Complex.hasDerivAt_log (by simp : (1:ℂ)∈slitPlane)).scomp_of_eq y dq q1.symm
  have angle := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y logD
  have algebra : ((I/h*deriv G z)/G z).im=(deriv G z/G z/h).re := by
    rw [show I/h*deriv G z/G z=I*(deriv G z/G z/h) by ring]
    simp
  have exactD : HasDerivAt θ (2*B.im*(C+D*B.re)) y := by
    change (deriv G z/G z/h).re=2*B.im*(C+D*B.re) at eq
    rw [← eq,← algebra]
    simpa [θ,q,z,Function.comp_def,smul_eq_mul,log_im] using! angle
  have unit : θ y=0 := by change (G z/G z).arg=0; simp [gg]
  refine ⟨unit,exactD.differentiableAt,?_,?_,?_⟩ <;> rw [exactD.deriv]
  · rw [mul_pos_iff_of_pos_left (by positivity : 0<2*B.im),lt_div_iff₀ negD]
    constructor <;> intro h <;> linarith
  · rw [mul_eq_zero_iff_left (by positivity : 2*B.im≠0),eq_div_iff negD.ne']
    constructor <;> intro h <;> linarith
  · have sign : 2*B.im*(C+D*B.re)<0 ↔ C+D*B.re<0 :=
      ⟨fun e => neg_of_mul_neg_right e (by positivity),fun e => mul_neg_of_pos_of_neg (by positivity) e⟩
    rw [sign,div_lt_iff₀ negD]
    constructor <;> intro h <;> linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_horizontal_tangent_turning_test
