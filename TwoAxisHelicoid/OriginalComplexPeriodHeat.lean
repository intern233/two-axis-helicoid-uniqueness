import TwoAxisHelicoid.OriginalMovingEndpoint
import TwoAxisHelicoid.OriginalWeightedIntegration
import TwoAxisHelicoid.OriginalComplexPeriodDerivative

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Interval
attribute [local irreducible] thetaA thetaLt thetaLz thetaLa thetaW

noncomputable def originalComplexSlopeWeight (t : ℝ) (ht : 0 < t) (a : ℝ) : ℂ :=
  slopingIntegral t (fun z => (rhombicPeriodPair t ht).derivWeierstrassP z*thetaA t a z)

theorem originalPath_add_abscissa_not_mem {t a s : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Icc (-1 : ℝ) 1) :
    originalPeriodPath t s+a ∉ (rhombicPeriodPair t ht).lattice := by
  have hs' : -s ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hs.1,hs.2]
  have hm := mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht
    (originalPeriodPath t (-s)-a)).mpr (originalPath_shift_regular ht ha hs')
  intro hp
  have htwo : (2 : ℂ) ∈ (rhombicPeriodPair t ht).lattice :=
    (rhombicPeriodPair t ht).ω₁_mem_lattice
  have hn := sub_mem (neg_mem hp) htwo
  have he : -(originalPeriodPath t s+(a : ℂ))-2 = originalPeriodPath t (-s)-a := by
    unfold originalPeriodPath
    push_cast
    ring
  rw [he] at hn
  exact hm hn

theorem originalSlopingPeriod_t_elliptic_intermediate {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun r : ℝ => originalSlopingPeriod r a)
      ((3*originalComplexWeight t ht a+
        (2*(rhombicPeriodPair t ht).weierstrassP a-thetaEtaExpression t)*originalSlopingPeriod t a+
        thetaW t a*deriv (originalSlopingPeriod t) a-
        (a-1)*originalComplexSlopeWeight t ht a)/(Real.pi : ℂ)) t := by
  let z := originalPeriodPath t
  let A := fun s : ℝ => thetaA t a (z s)
  let Aa := fun s : ℝ => thetaAa t a (z s)
  let P := fun s : ℝ => (rhombicPeriodPair t ht).weierstrassP (z s)
  let V := fun s : ℝ => (rhombicPeriodPair t ht).derivWeierstrassP (z s)
  let W := fun s : ℝ => thetaW t (z s)
  let D := fun s : ℝ => deriv (thetaA t a) (z s)
  let wa := thetaW t a
  let k : ℂ := a-1
  let u := (rhombicPeriodPair t ht).weierstrassP a
  let eta := thetaEtaExpression t
  let q : ℂ := (1-I*t)/2
  have hn (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) : z s ∉ (rhombicPeriodPair t ht).lattice :=
    rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht hs)
  have hz : ContinuousOn z (Icc (-1 : ℝ) 1) := by
    dsimp [z]
    unfold originalPeriodPath
    fun_prop
  have hAc : ContinuousOn A (Icc (-1 : ℝ) 1) :=
    thetaA_comp_continuousOn (u := fun _ => t) (b := fun _ => a)
      continuousOn_const continuousOn_const hz (fun _ _ => ht)
      (fun _ _ => theta_vertical_denominator ht ha.1 (by linarith [ha.2]))
      (fun _ hs => originalPath_regular ht hs)
  have hAac : ContinuousOn Aa (Icc (-1 : ℝ) 1) :=
    thetaAa_comp_continuousOn (u := fun _ => t) (b := fun _ => a)
      continuousOn_const continuousOn_const hz (fun _ _ => ht)
      (fun _ _ => theta_vertical_denominator ht ha.1 (by linarith [ha.2]))
      (fun _ hs => originalPath_regular ht hs) (fun _ hs => originalPath_shift_regular ht ha hs)
  have hPc : ContinuousOn P (Icc (-1 : ℝ) 1) := by
    intro s hs
    exact ((rhombicPeriodPair t ht).analyticOnNhd_weierstrassP _ (hn s hs)).continuousAt.comp_continuousWithinAt
      (f := z) (hz s hs)
  have hVc : ContinuousOn V (Icc (-1 : ℝ) 1) := by
    intro s hs
    exact ((rhombicPeriodPair t ht).analyticOnNhd_derivWeierstrassP _ (hn s hs)).continuousAt.comp_continuousWithinAt
      (f := z) (hz s hs)
  have hWc : ContinuousOn W (Icc (-1 : ℝ) 1) := by
    intro s hs
    exact (thetaW_hasDerivAt ht (hn s hs)).continuousAt.comp_continuousWithinAt (f := z) (hz s hs)
  have hDc : ContinuousOn D (Icc (-1 : ℝ) 1) := originalPath_derivative_continuousOn ht a
  have hId (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) :
      (Real.pi : ℂ)*(A s*thetaLt t a (z s)) =
        W s*D s+wa*Aa s-k*(V s*A s)+2*(P s*A s)+(2*u-2*eta)*A s := by
    have hm := mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht (z s-a)).mpr
      (originalPath_shift_regular ht ha hs)
    have hh := thetaLt_elliptic_identity ht
      (real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2]))
      (hn s hs) hm (originalPath_add_abscissa_not_mem ht ha hs)
    dsimp [A,Aa,W,D,P,V,wa,k,u,eta]
    rw [thetaA_spatial_deriv ht a
      (theta_vertical_denominator ht ha.1 (by linarith [ha.2]))
      (originalPath_regular ht hs) (originalPath_shift_regular ht ha hs)]
    unfold thetaAa
    linear_combination thetaA t a (z s)*hh
  have hEq : (∫ s : ℝ in (-1)..1, (Real.pi : ℂ)*(A s*thetaLt t a (z s))) =
      ∫ s : ℝ in (-1)..1, W s*D s+wa*Aa s-k*(V s*A s)+2*(P s*A s)+(2*u-2*eta)*A s := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact hId s (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hs)
  simp (disch := apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num); fun_prop) only
    [intervalIntegral.integral_add,intervalIntegral.integral_sub,intervalIntegral.integral_const_mul] at hEq
  have hWint := original_weighted_spatial_integral ht a
  change q*(∫ s : ℝ in (-1)..1, W s*D s) =
    q*(∫ s : ℝ in (-1)..1, (P s+eta)*A s)+(Real.pi : ℂ)*I*A (-1) at hWint
  have hexpand (s : ℝ) : (P s+eta)*A s = P s*A s+eta*A s := by ring
  simp_rw [hexpand] at hWint
  simp (disch := apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num); fun_prop) only
    [intervalIntegral.integral_add,intervalIntegral.integral_const_mul] at hWint
  have hvalue : slopingIntegral t (fun w => thetaA t a w*thetaLt t a w)-I*A (-1) =
      (3*originalComplexWeight t ht a+(2*u-eta)*originalSlopingPeriod t a+
        wa*deriv (originalSlopingPeriod t) a-k*originalComplexSlopeWeight t ht a)/(Real.pi : ℂ) := by
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).mpr
    rw [(originalSlopingPeriod_a_hasDerivAt_integral ht ha).deriv]
    unfold originalComplexWeight originalSlopingPeriod originalComplexSlopeWeight slopingIntegral
    change (q*(∫ s : ℝ in (-1)..1, A s*thetaLt t a (z s))-I*A (-1))*(Real.pi : ℂ) =
      3*(q*∫ s : ℝ in (-1)..1, P s*A s)+(2*u-eta)*(q*∫ s : ℝ in (-1)..1, A s)+
      wa*(q*∫ s : ℝ in (-1)..1, Aa s)-k*(q*∫ s : ℝ in (-1)..1, V s*A s)
    linear_combination q*hEq+hWint
  have hd := originalSlopingPeriod_t_hasDerivAt_moving_endpoint ht ha
  change HasDerivAt (fun r : ℝ => originalSlopingPeriod r a)
    (slopingIntegral t (fun w => thetaA t a w*thetaLt t a w)-I*A (-1)) t at hd
  rw [hvalue] at hd
  exact hd

theorem originalSlopingPeriod_t_hasDerivAt_elliptic {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun r : ℝ => originalSlopingPeriod r a)
      (((3-2*(a-1)*thetaW t a)*originalComplexWeight t ht a-
        (a-1)*originalComplexSlopeWeight t ht a+
        (2*(rhombicPeriodPair t ht).weierstrassP a-thetaEtaExpression t-
          2*(thetaW t a)^2-2*thetaEtaExpression t*(a-1)*thetaW t a)*
            originalSlopingPeriod t a)/(Real.pi : ℂ)) t := by
  have hd := originalSlopingPeriod_t_elliptic_intermediate ht ha
  rw [(originalSlopingPeriod_a_hasDerivAt ht ha).deriv] at hd
  convert hd using 1
  unfold thetaW
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.originalSlopingPeriod_t_hasDerivAt_elliptic
