import TwoAxisHelicoid.UnivalentQuarterHeightCoordinate
import TwoAxisHelicoid.ActualGaussHeightCorrection
import TwoAxisHelicoid.AxisGaussRegular

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology ComplexConjugate

theorem real_wp_derivative_as_real {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) :
    let L := rhombicPeriodPair t ht
    L.derivWeierstrassP a=(((L.derivWeierstrassP a).re:ℝ):ℂ) := by
  intro L
  have nr := real_not_mem_rhombic_lattice_of_pos ht ha.1 (ha.2.trans (by norm_num))
  have s (x : ℝ) : thetaSigma t x=((thetaSigma t x).re:ℂ) := Complex.ext rfl (thetaSigma_real t x)
  rw [show L.derivWeierstrassP a= -thetaSigma t (2*(a:ℂ))/thetaSigma t a^4 from
    rhombic_weierstrassP_derivative_sigma_of_pos ht ht nr]
  rw [show 2*(a:ℂ)=((2*a:ℝ):ℂ) by push_cast; rfl,s (2*a),s a]
  norm_cast

/-- The imaginary part of the logarithmic Gauss differential after
subtracting the helical rotation has one strict sign on a whole cell. -/
theorem relative_gauss_coefficient_quarter_im_neg {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {z : ℂ} (hz : z∈complexOpenRect 0 1 0 t) : (axisRegularCoefficient t ht a z).im<0 := by
  let L := rhombicPeriodPair t ht
  let P := L.weierstrassP z-L.weierstrassP a
  have repr : (z.re:ℂ)+I*z.im=z := by apply Complex.ext <;> simp
  have p : P.im<0 := by
    have h := rhombic_weierstrassP_quarter_im_neg ht hz.1 hz.2
    rw [repr] at h
    simpa [P,L,Complex.sub_im,rhombic_weierstrassP_real] using h
  have nz : P≠0 := fun e => p.ne (by rw [e]; rfl)
  have ζ : (thetaZeta t a).im=0 := by
    have h := congrArg im (thetaZeta_conj t (a:ℂ))
    simp only [conj_ofReal,conj_im] at h
    linarith
  have dn := rhombic_weierstrassP_derivative_real_neg_of_pos ht ht ha.1 ha.2
  change (2*(thetaEtaExpression t-thetaZeta t a+(1-a)*L.weierstrassP a)+L.derivWeierstrassP a/P).im<0
  rw [real_wp_derivative_as_real ht ha,div_eq_mul_inv]
  simpa [Complex.add_im,Complex.mul_im,Complex.sub_im,thetaEtaExpression_real,ζ,rhombic_weierstrassP_real ht a,
    L,Complex.inv_im] using mul_neg_of_neg_of_pos dn (div_pos (neg_pos.mpr p) (Complex.normSq_pos.mpr nz))

/-- On the open rectangle the normalized Gauss map has a global
univalent logarithm up to a nonzero multiplicative constant. Its imaginary
part is the continuous relative angle, before reduction modulo two π. -/
theorem actual_relative_gauss_quarter_logarithm {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) :
    let U := complexOpenRect 0 1 0 t
    ∃ (F : ℂ → ℂ) (k : ℂ), k≠0 ∧ InjOn F U ∧
      (∀ z∈U, HasDerivAt F (axisRegularCoefficient t ht a z) z ∧
        heightGaussFactor t a 1 ht z=k*exp (F z)) ∧
      ∀ z∈U, ∀ w∈U, w≠z → ((F w-F z)/(w-z)).im<0 := by
  intro U
  let f := heightGaussFactor t a 1 ht
  let Ω := axisRegularCoefficient t ht a
  let L := rhombicPeriodPair t ht
  have off (z : ℂ) (hz : z∈U) : z∉L.lattice ∧ z-a∉L.lattice ∧ z+a∉L.lattice := by
    refine ⟨rhombic_horizontal_strip_not_mem ht hz.2,rhombic_horizontal_strip_not_mem ht ?_,rhombic_horizontal_strip_not_mem ht ?_⟩
    · change (z-a).im∈Ioo 0 t
      simpa using hz.2
    · change (z+a).im∈Ioo 0 t
      simpa using hz.2
  have anal (z : ℂ) (hz : z∈U) : AnalyticAt ℂ Ω z := by
    have n := weierstrass_sub_ne_zero_of_sigma ht (real_not_mem_rhombic_lattice_of_pos ht ha.1 (ha.2.trans (by norm_num)))
      (off z hz).1 (off z hz).2.1 (off z hz).2.2
    exact analyticAt_const.add (analyticAt_const.div ((L.analyticOnNhd_weierstrassP z (off z hz).1).sub analyticAt_const) n)
  let c : ℂ := ⟨1/2,t/2⟩
  have hc : c∈U := ⟨⟨by norm_num [c],by norm_num [c]⟩,⟨by change 0<t/2; linarith,by change t/2<t; linarith⟩⟩
  let F := fun z => wedgeIntegral c z Ω
  have dF := holomorphic_rectangle_has_primitive (f:=Ω)
    (fun z h => (anal z h).differentiableAt.differentiableWithinAt) hc
  have sec {z w : ℂ} (hz : z∈U) (hw : w∈U) (ne : w≠z) : ((F w-F z)/(w-z)).im<0 := by
    have ds (u : ℂ) (h : u∈U) : HasDerivAt (fun u => I*F u) (I*Ω u) u := (dF u h).const_mul I
    have p := positive_real_secant_of_derivative (complexOpenRect_convex 0 1 0 t) ds
      (fun u h => by simpa [Ω,Complex.mul_re] using relative_gauss_coefficient_quarter_im_neg ht ha h) hz hw ne
    rwa [← mul_sub, mul_div_assoc,Complex.mul_re,I_re,I_im,zero_mul,one_mul,zero_sub,neg_pos] at p
  have inject : InjOn F U := by
    intro z hz w hw eq
    by_contra ne
    have s := sec hw hz ne
    simp [eq] at s
  let α : ℂ := I*(2*((a:ℂ)-1))
  let H := actualComplexHeight t a 1 ht
  let g := thetaGauss t a 1
  have identity (z : ℂ) : f z=I*g z*exp (-α*H z) := by
    have id := gauss_height_factor_identity (a:=a) ht (one_ne_zero : (1:ℝ)≠0) 1 z
    simp only [Int.cast_one,div_one,ofReal_mul,ofReal_ofNat,ofReal_sub,ofReal_one] at id
    change I*g z=exp (α*H z)*f z at id
    rw [id,mul_right_comm,← exp_add,show α*H z+ -α*H z=0 by ring,exp_zero,one_mul]
  have non (z : ℂ) (hz : z∈U) : f z≠0 := by
    rw [identity]
    exact mul_ne_zero (mul_ne_zero I_ne_zero (thetaGauss_ne_zero ht a 1 (off z hz).2.1 (off z hz).2.2)) (exp_ne_zero _)
  have logder (z : ℂ) (hz : z∈U) : HasDerivAt f (f z*Ω z) z := by
    obtain ⟨o,m,p⟩ := off z hz
    have dg := thetaGauss_hasDerivAt ht a 1 o m p
    have dh := actualComplexHeight_hasDerivAt (a:=a) (c:=1) ht o
    have rel := thetaGaussLogDerivative_regular_part ht ha o m p
    have alg : thetaGaussLogDerivative t a ht 1 z-α*coordinateData t a 1 ht z 2=Ω z := by
      dsimp only [Ω]
      rw [← rel]
      change _-α*(I*(1:ℂ)*(L.weierstrassP z-L.weierstrassP a))=_
      dsimp [α,L]
      ring_nf
      simp [I_sq]
      ring
    rw [show f=(fun u => I*g u*exp (-α*H u)) from funext identity]
    convert (dg.const_mul I).mul ((dh.const_mul (-α)).cexp) using 1
    change I*g z*exp (-α*H z)*Ω z=_
    rw [← alg]
    dsimp only [g,H]
    ring
  have constant := (complexOpenRect_isOpen 0 1 0 t).exists_is_const_of_deriv_eq_zero
    (complexOpenRect_convex 0 1 0 t).isPreconnected (f:=fun z => f z*exp (-F z))
    (fun z h => ((logder z h).mul ((dF z h).neg.cexp)).differentiableAt.differentiableWithinAt)
    (fun z h => by
      have e := ((logder z h).mul ((dF z h).neg.cexp)).deriv
      apply e.trans
      change f z*Ω z*exp (-F z)+f z*(exp (-F z)* -Ω z)=0
      ring)
  obtain ⟨k,hk⟩ := constant
  have kn : k≠0 := (hk c hc) ▸ mul_ne_zero (non c hc) (exp_ne_zero _)
  refine ⟨F,k,kn,inject,fun z h => ⟨dF z h,?_⟩,fun _ hz _ hw => sec hz hw⟩
  change f z=k*exp (F z)
  rw [← hk z h]
  rw [mul_assoc,← exp_add,neg_add_cancel,exp_zero,mul_one]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_relative_gauss_quarter_logarithm
