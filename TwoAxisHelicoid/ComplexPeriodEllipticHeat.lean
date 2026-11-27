import TwoAxisHelicoid.WeightedIntegrationByParts
import TwoAxisHelicoid.ComplexPeriodTimeDerivative

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
attribute [local irreducible] thetaA thetaW thetaAa thetaAtMidline

noncomputable def fullComplexSlopeWeight (t : ℝ) (ht : 0 < t) (a : ℝ) : ℂ :=
  (1/2:ℂ)*(∫ x : ℝ in (-1)..1,
    (rhombicPeriodPair t ht).derivWeierstrassP ((x:ℂ)+I*((t/2:ℝ):ℂ))*
      thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ)))

theorem fullComplexPeriod_t_elliptic_intermediate {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (fun s => fullComplexPeriod s a)
      ((3*fullComplexWeight t ht a+
        (2*(rhombicPeriodPair t ht).weierstrassP a-thetaEtaExpression t)*fullComplexPeriod t a+
        thetaW t a*deriv (fullComplexPeriod t) a-(a-1)*fullComplexSlopeWeight t ht a)/(Real.pi:ℂ)) t := by
  let z := fun x : ℝ => (x:ℂ)+I*((t/2:ℝ):ℂ)
  let A := fun x : ℝ => thetaA t a (z x)
  let Aa := fun x : ℝ => thetaAa t a (z x)
  let P := fun x : ℝ => (rhombicPeriodPair t ht).weierstrassP (z x)
  let V := fun x : ℝ => (rhombicPeriodPair t ht).derivWeierstrassP (z x)
  let W := fun x : ℝ => thetaW t (z x)
  let D := fun x : ℝ => deriv (thetaA t a) (z x)
  let wa := thetaW t a
  let k : ℂ := a-1
  let u := (rhombicPeriodPair t ht).weierstrassP a
  let eta := thetaEtaExpression t
  have harg (x : ℝ) : ContinuousAt z x := by fun_prop
  have hc := horizontal_composite_continuousOn (S := (univ:Set ℝ)) (u := fun _ => t)
    (b := fun _ => a) (x := id) continuousOn_const continuousOn_const continuousOn_id
    (fun _ _ => ht) (fun _ _ => ha)
  have hAc : Continuous A := continuousOn_univ.mp hc.1
  have hAac : Continuous Aa := continuousOn_univ.mp hc.2.1
  have hPc : Continuous P := continuous_iff_continuousAt.mpr fun x =>
    (rhombic_weierstrassP_hasDerivAt ht (rhombic_midline_not_mem ht x)).continuousAt.comp
      (f := z) (x := x) (harg x)
  have hVc : Continuous V := continuous_iff_continuousAt.mpr fun x =>
    ((rhombicPeriodPair t ht).analyticOnNhd_derivWeierstrassP _ (rhombic_midline_not_mem ht x)).continuousAt.comp
      (f := z) (x := x) (harg x)
  have hWc : Continuous W := continuous_iff_continuousAt.mpr fun x =>
    (thetaW_hasDerivAt ht (rhombic_midline_not_mem ht x)).continuousAt.comp (f := z) (x := x) (harg x)
  have hDc : Continuous D := continuous_iff_continuousAt.mpr fun x =>
    ((thetaA_deriv_continuousOn ht a).continuousAt
      ((thetaRegular_isOpen ht).mem_nhds (horizontal_midline_regular ht x))).comp
        (f := z) (x := x) (harg x)
  have hnA := real_not_mem_rhombic_lattice_of_pos ht ha.1 ha.2
  have hId (x : ℝ) : (Real.pi:ℂ)*thetaAtMidline t a (z x) =
      W x*D x+wa*Aa x-k*(V x*A x)+2*(P x*A x)+(2*u-2*eta)*A x+
        (Real.pi*I/2:ℂ)*D x := by
    have hm := mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht (z x-a)).mpr (horizontal_shift_regular ht a x)
    have hp : z x+a ∉ (rhombicPeriodPair t ht).lattice := by
      have he : z x+a = ((x+a:ℝ):ℂ)+I*((t/2:ℝ):ℂ) := by dsimp [z]; push_cast; ring
      rw [he]
      exact rhombic_midline_not_mem ht (x+a)
    have hheat := thetaLt_elliptic_identity ht hnA (rhombic_midline_not_mem ht x) hm hp
    have hD := thetaA_spatial_deriv ht a (theta_vertical_denominator ht ha.1 ha.2)
      (horizontal_midline_regular ht x) (horizontal_shift_regular ht a x)
    dsimp only [D,Aa,A,W,P,V,wa,k,u,eta]
    rw [hD]
    unfold thetaAtMidline thetaAa
    linear_combination thetaA t a (z x)*hheat
  have hEq := congrArg (fun f : ℝ → ℂ => ∫ x : ℝ in (-1)..1, f x) (funext hId)
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add,intervalIntegral.integral_sub,intervalIntegral.integral_const_mul] at hEq
  have hWint := weighted_spatial_integral ht ha
  change (∫ x : ℝ in (-1)..1, W x*D x) = ∫ x : ℝ in (-1)..1, (P x+eta)*A x at hWint
  have hexpand (x : ℝ) : (P x+eta)*A x = P x*A x+eta*A x := by ring
  simp_rw [hexpand] at hWint
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add,intervalIntegral.integral_const_mul] at hWint
  have hDint := thetaA_integral_spatial_derivative_zero ht a (t/2) (fun x _ => horizontal_midline_regular ht x)
  change (∫ x : ℝ in (-1)..1, D x) = 0 at hDint
  rw [hWint,hDint,mul_zero,add_zero] at hEq
  have hvalue : ((1/2:ℂ)*∫ x : ℝ in (-1)..1, thetaAtMidline t a (z x)) =
      (3*fullComplexWeight t ht a+(2*u-eta)*fullComplexPeriod t a+
        wa*deriv (fullComplexPeriod t) a-k*fullComplexSlopeWeight t ht a)/(Real.pi:ℂ) := by
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).mpr
    rw [(fullComplexPeriod_a_hasDerivAt_integral ht ha).deriv]
    unfold fullComplexWeight fullComplexPeriod fullComplexSlopeWeight
    change ((1/2:ℂ)*(∫ x : ℝ in (-1)..1, thetaAtMidline t a (z x)))*(Real.pi:ℂ) =
      3*((1/2:ℂ)*∫ x : ℝ in (-1)..1, P x*A x)+(2*u-eta)*((1/2:ℂ)*∫ x : ℝ in (-1)..1, A x)+
      wa*((1/2:ℂ)*∫ x : ℝ in (-1)..1, Aa x)-k*((1/2:ℂ)*∫ x : ℝ in (-1)..1, V x*A x)
    linear_combination (1/2:ℂ)*hEq
  have hd := fullComplexPeriod_t_hasDerivAt_integral ht ha
  change HasDerivAt (fun s => fullComplexPeriod s a)
    ((1/2:ℂ)*∫ x : ℝ in (-1)..1, thetaAtMidline t a (z x)) t at hd
  rw [hvalue] at hd
  exact hd

theorem fullComplexPeriod_t_hasDerivAt_elliptic {t a : ℝ}
    (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (fun s => fullComplexPeriod s a)
      (((3-2*(a-1)*thetaW t a)*fullComplexWeight t ht a-
        (a-1)*fullComplexSlopeWeight t ht a+
        (2*(rhombicPeriodPair t ht).weierstrassP a-thetaEtaExpression t-
          2*(thetaW t a)^2-2*thetaEtaExpression t*(a-1)*thetaW t a)*
            fullComplexPeriod t a)/(Real.pi:ℂ)) t := by
  have hd := fullComplexPeriod_t_elliptic_intermediate ht ha
  rw [(fullComplexPeriod_a_hasDerivAt ht ha).deriv] at hd
  convert hd using 1
  unfold thetaW
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.fullComplexPeriod_t_elliptic_intermediate
#print axioms TwoAxisHelicoid.fullComplexPeriod_t_hasDerivAt_elliptic
