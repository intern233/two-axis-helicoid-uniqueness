import TwoAxisHelicoid.HarmonicIntegerCoordinateData
import TwoAxisHelicoid.RealPrimitivePeriods
import TwoAxisHelicoid.SlopingIntegralBridge

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Interval ComplexConjugate
attribute [local irreducible] thetaA thetaGauss thetaZeta thetaScaledJet

/-- The spinor square occurring in the horizontal differential of the zero
integer branch. The factor in front of the index-one kernel changes its
essential singularity and cannot be dropped from its period integral. -/
noncomputable def zeroBranchKernel (t a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (2*(thetaZeta t z-thetaEtaExpression t*z))*thetaA t a z

theorem zeroBranchKernel_scaled (t a : ℝ) (z : ℂ) :
    zeroBranchKernel t a z =
      (thetaScaledJet t 1 0/thetaScaledJet t 0 (a:ℂ))^2*
      (thetaScaledJet t 0 (z-a)/thetaScaledJet t 0 z)^2*
      Complex.exp (2*a*(thetaScaledJet t 1 z/thetaScaledJet t 0 z)) := by
  rw [zeroBranchKernel,thetaA_eq_scaled]
  unfold thetaZeta
  rw [show 2*(thetaScaledJet t 1 z/thetaScaledJet t 0 z+thetaEtaExpression t*z-
      thetaEtaExpression t*z) = 2*(thetaScaledJet t 1 z/thetaScaledJet t 0 z) by ring]
  rw [mul_left_comm,← Complex.exp_add]
  congr 2
  ring

theorem thetaGauss_zero_height_kernel {t a : ℝ} (ht : 0 < t) (c : ℝ) {z : ℂ}
    (ha : (a:ℂ) ∉ (rhombicPeriodPair t ht).lattice)
    (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    thetaGauss t a 0 z*coordinateData t a c ht z 2 = (c:ℂ)*zeroBranchKernel t a z := by
  have h := thetaGauss_height_sigma_of_pos ht ht c ha hz hp
  rw [thetaSigmaKernel_eq_thetaA_of_pos ht ht z ha hz] at h
  have he : thetaGauss t a 0 z =
      Complex.exp (2*(thetaZeta t z-thetaEtaExpression t*z))*thetaGauss t a 1 z := by
    unfold thetaGauss
    simp only [Int.cast_zero,Int.cast_one,sub_zero,mul_zero,zero_mul,add_zero,mul_one]
    rw [show 2*(a:ℂ)*thetaZeta t z = 2*(thetaZeta t z-thetaEtaExpression t*z)+
        (2*(a-1)*thetaZeta t z+2*thetaEtaExpression t*z) by ring,Complex.exp_add]
    ring
  change thetaGauss t a 0 z*(I*c*((rhombicPeriodPair t ht).weierstrassP z-
      (rhombicPeriodPair t ht).weierstrassP a)) = _
  rw [he,mul_assoc,h,zeroBranchKernel]
  ring

theorem zeroBranchKernel_period_two (t a : ℝ) : Function.Periodic (zeroBranchKernel t a) 2 := by
  intro z
  rw [zeroBranchKernel,zeroBranchKernel,thetaA_periodic,thetaZeta_add_two]
  congr 3
  ring

theorem zeroBranchKernel_half_period {t : ℝ} (ht : 0 < t) (a : ℝ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    zeroBranchKernel t a (z+(1+I*t)) = zeroBranchKernel t a z := by
  rw [zeroBranchKernel,zeroBranchKernel,thetaA_complex_period ht a,thetaZeta_add_half_of_pos ht ht hz]
  rw [show 2*(thetaZeta t z+thetaEtaExpression t*(1+I*t)-Real.pi*I-
        thetaEtaExpression t*(z+(1+I*t))) =
        2*(thetaZeta t z-thetaEtaExpression t*z)-(2*Real.pi*I) by ring,
    Complex.exp_sub,Complex.exp_two_pi_mul_I,div_one]

theorem zeroBranchKernel_differentiableAt {t : ℝ} (ht : 0 < t) (a : ℝ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) : DifferentiableAt ℂ (zeroBranchKernel t a) z := by
  unfold zeroBranchKernel
  have hd := (thetaZeta_hasDerivAt_of_pos ht ht hz).differentiableAt
  have ha := (thetaA_analyticAt_off_lattice ht a hz).differentiableAt
  fun_prop

noncomputable def zeroBranchMidline (t x : ℝ) : ℂ := x+I*((t/2:ℝ):ℂ)

noncomputable def zeroBranchHorizontalPeriod (t a : ℝ) : ℝ :=
  ((1/2:ℂ)*∫ x : ℝ in (-1)..1, zeroBranchKernel t a (zeroBranchMidline t x)).re

theorem zeroBranchMidline_regular {t : ℝ} (ht : 0 < t) (a x : ℝ) :
    zeroBranchMidline t x ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a := by
  apply (not_mem_gaussLogPoleSet _ _ _).mpr
  refine ⟨rhombic_midline_not_mem ht x,?_,?_⟩
  · convert rhombic_midline_not_mem ht (x-a) using 2
    unfold zeroBranchMidline
    push_cast
    ring
  · convert rhombic_midline_not_mem ht (x+a) using 2
    unfold zeroBranchMidline
    push_cast
    ring

theorem zeroBranchMidline_negative_integral {t : ℝ} (ht : 0 < t) (a : ℝ) :
    (∫ x : ℝ in (-1)..1, zeroBranchKernel t a (-zeroBranchMidline t x)) =
      ∫ x : ℝ in (-1)..1, zeroBranchKernel t a (zeroBranchMidline t x) := by
  let f := fun x => zeroBranchKernel t a (zeroBranchMidline t x)
  have hp : Function.Periodic f 2 := by
    intro x
    dsimp only [f]
    rw [show zeroBranchMidline t (x+2) = zeroBranchMidline t x+2 by
      unfold zeroBranchMidline; push_cast; ring,zeroBranchKernel_period_two]
  have he (x : ℝ) : zeroBranchKernel t a (-zeroBranchMidline t x) = f (1-x) := by
    have hn : -zeroBranchMidline t x ∉ (rhombicPeriodPair t ht).lattice := by
      simpa only [neg_mem_iff,zeroBranchMidline] using rhombic_midline_not_mem ht x
    dsimp only [f]
    rw [show zeroBranchMidline t (1-x) = -zeroBranchMidline t x+(1+I*t) by
      unfold zeroBranchMidline; push_cast; ring,zeroBranchKernel_half_period ht a hn]
  simp_rw [he]
  rw [intervalIntegral.integral_comp_sub_left]
  simpa only [sub_self,sub_neg_eq_add,one_add_one_eq_two,zero_add,
    show (-1:ℝ)+2 = 1 by norm_num] using hp.intervalIntegral_add_eq 0 (-1)

theorem zeroBranch_x_coefficient {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) {z : ℂ}
    (hz : z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a) :
    weierstrassTriple (thetaGauss t a 0 z) (coordinateData t a c ht z 2) 0 =
      -(c:ℂ)/2*(zeroBranchKernel t a (-z)+zeroBranchKernel t a z) := by
  obtain ⟨hL,hm,hp⟩ := (not_mem_gaussLogPoleSet _ _ _).mp hz
  have haL := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  have h := thetaGauss_zero_height_kernel ht c haL hL hp
  have hn := thetaGauss_zero_height_kernel ht c haL (z := -z) (by simpa using hL)
    (by simpa only [show -z+(a:ℂ) = -(z-a) by ring,neg_mem_iff] using hm)
  have hh : coordinateData t a c ht (-z) 2 = coordinateData t a c ht z 2 := by
    change I*c*((rhombicPeriodPair t ht).weierstrassP (-z)-_) = _
    rw [(rhombicPeriodPair t ht).weierstrassP_neg]
    rfl
  have hne := thetaGauss_ne_zero ht a 0 hm hp
  have he : thetaGauss t a 0 (-z) = -(thetaGauss t a 0 z)⁻¹ := by
    apply (mul_right_cancel₀ hne)
    rw [thetaGauss_neg_product ht a 0 hm hp]
    simp [hne]
  rw [he,hh] at hn
  change (_⁻¹-_)/2*_ = _
  linear_combination -(h+hn)/2

/-- Single-valuedness of the actual harmonic map forces the real horizontal
period of the zero-branch kernel to vanish. The path lies on the horizontal
midline, away from the puncture and both finite divisor points. -/
theorem harmonic_zero_branch_horizontal_period {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 = coordinateData t a c ht z 2)
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a 0 z) :
    zeroBranchHorizontalPeriod t a = 0 := by
  let k := zeroBranchKernel t a
  let p := zeroBranchMidline t
  let f := fun z => -(c:ℂ)/2*(k (-z)+k z)
  have hD := harmonic_integer_gauss_data_has_coordinate_differential ht ha hc 0 hX hh hg
  have hp (x : ℝ) : HasDerivAt p 1 x := by
    have hx : HasDerivAt (fun s : ℝ => (s:ℂ)) 1 x := by
      simpa using! (Complex.ofRealCLM.hasDerivAt (x := x))
    exact hx.add_const (I*((t/2:ℝ):ℂ))
  have hreg (x : ℝ) := zeroBranchMidline_regular ht a x
  have hL (x : ℝ) : p x ∉ (rhombicPeriodPair t ht).lattice := rhombic_midline_not_mem ht x
  have hF (x : ℝ) : HasFDerivAt (fun z => X z 0) (realCoefficientDerivative (f (p x))) (p x) := by
    have h := (ContinuousLinearMap.proj 0 : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp (p x)
      (hD _ (hreg x))
    rw [← show weierstrassTriple (thetaGauss t a 0 (p x)) (coordinateData t a c ht (p x) 2) 0 =
        f (p x) from zeroBranch_x_coefficient ht ha (hreg x)]
    exact h
  have hI : Continuous (fun x => k (p x)) := continuous_iff_continuousAt.mpr (fun x =>
    (zeroBranchKernel_differentiableAt ht a (hL x)).continuousAt.comp (hp x).continuousAt)
  have hN : Continuous (fun x => k (-p x)) := continuous_iff_continuousAt.mpr (fun x =>
    (zeroBranchKernel_differentiableAt ht a (show -p x ∉ _ by simpa using hL x)).continuousAt.comp
      (f := fun y => -p y) (hp x).continuousAt.neg)
  have hI' : IntervalIntegrable (fun x => f (p x)) volume (-1) 1 :=
    ((hN.add hI).const_mul _).intervalIntegrable _ _
  have h := real_primitive_path_integral_eq_sub (fun s _ => hp s) (fun s _ => hF s) hI'
  have hend : p 1 = p (-1)+2 := by dsimp [p,zeroBranchMidline]; push_cast; ring
  rw [one_mul,hend,congrFun (hX.periodic _ (hL (-1)) 2 (rhombicPeriodPair t ht).ω₁_mem_lattice) 0,
    sub_self] at h
  dsimp only [f] at h
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
    (hN.intervalIntegrable (-1) 1) (hI.intervalIntegrable (-1) 1),
    show (∫ s : ℝ in (-1)..1, k (-p s)) = ∫ s : ℝ in (-1)..1, k (p s) from
      zeroBranchMidline_negative_integral ht a] at h
  let J := ∫ s : ℝ in (-1)..1, k (p s)
  change (-(c:ℂ)/2*(J+J)).re = 0 at h
  have hJ : J.re = 0 := by
    rw [show -(c:ℂ)/2*(J+J) = -(c*J) by ring] at h
    simpa [Complex.mul_re,hc] using h
  change ((1/2:ℂ)*J).re = 0
  simp [Complex.mul_re,hJ]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_zero_branch_horizontal_period
