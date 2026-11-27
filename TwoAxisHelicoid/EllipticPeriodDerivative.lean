import TwoAxisHelicoid.HorizontalParameterAnalytic
import TwoAxisHelicoid.HorizontalRightValue

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology
attribute [local irreducible] thetaA thetaAa thetaLa thetaLz thetaJet thetaQuotient thetaLogSecond

noncomputable def fullComplexPeriod (t a : ℝ) : ℂ :=
  (1/2:ℂ)*(∫ x : ℝ in (-1)..1, thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ)))

noncomputable def fullComplexWeight (t : ℝ) (ht : 0 < t) (a : ℝ) : ℂ :=
  (1/2:ℂ)*(∫ x : ℝ in (-1)..1,
    (rhombicPeriodPair t ht).weierstrassP ((x:ℂ)+I*((t/2:ℝ):ℂ))*thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ)))

theorem fullComplexPeriod_re (t a : ℝ) : (fullComplexPeriod t a).re = thetaHorizontalPeriod t a := by
  simp [fullComplexPeriod,thetaHorizontalPeriod,Complex.mul_re]

theorem thetaA_spatial_deriv {t : ℝ} (ht : 0 < t) (a : ℝ) {z : ℂ}
    (ha : thetaJet t 0 (Real.pi*a/2) ≠ 0)
    (hz : thetaJet t 0 (Real.pi*z/2) ≠ 0)
    (hm : thetaJet t 0 (Real.pi*(z-a)/2) ≠ 0) :
    deriv (thetaA t a) z = thetaA t a z*thetaLz t a z := by
  have harg : HasDerivAt (fun x : ℝ => z+(x:ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).ofReal_comp.const_add z
  have hd := thetaA_curve_hasDerivAt (hasDerivAt_const (0:ℝ) t) (hasDerivAt_const (0:ℝ) a)
    harg ht (thetaJet_one_at_zero_ne_zero_of_pos ht) ha (by simpa using hz) (by simpa using hm)
  have hz' : z ∈ thetaRegular t := hz
  have hp : HasDerivAt (thetaA t a) (deriv (thetaA t a) z) (z+(0:ℝ)) := by
    simpa only [Complex.ofReal_zero,add_zero] using (thetaA_differentiableAt ht a hz').hasDerivAt
  have hs := hp.comp (h := fun x : ℝ => z+(x:ℂ)) 0 harg
  have he := hs.unique hd
  simpa only [Complex.ofReal_zero,add_zero,zero_mul,zero_add,one_mul,mul_one] using he

theorem thetaLa_add_Lz_elliptic {t : ℝ} (ht : 0 < t) (a : ℝ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    thetaLa t a z+thetaLz t a z = 2*(thetaEtaExpression t-thetaZeta t a)-
      2*(a-1)*(rhombicPeriodPair t ht).weierstrassP z := by
  have he := thetaLogSecond_eq_weierstrassP_add_eta_of_pos ht ht hz
  rw [thetaZeta_quotient]
  unfold thetaLa thetaLz thetaLogSecond at *
  linear_combination -2*((a:ℂ)-1)*he

theorem fullComplexPeriod_a_hasDerivAt_integral {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (fullComplexPeriod t)
      ((1/2:ℂ)*(∫ x : ℝ in (-1)..1, thetaAa t a ((x:ℂ)+I*((t/2:ℝ):ℂ)))) a := by
  let l := a/2
  let u := (a+2)/2
  have hlu : a ∈ Ioo l u := by dsimp [l,u]; constructor <;> linarith [ha.1,ha.2]
  have hunit (s : ℝ) (hs : s ∈ Icc l u) : s ∈ Ioo (0:ℝ) 2 := by
    dsimp [l,u] at hs
    constructor <;> linarith [ha.1,ha.2,hs.1,hs.2]
  let S : Set (ℝ × ℝ) := Icc l u ×ˢ Icc (-1:ℝ) 1
  have hc := horizontal_composite_continuousOn (S := S) (u := fun _ => t)
    (b := Prod.fst) (x := Prod.snd) continuousOn_const continuous_fst.continuousOn
    continuous_snd.continuousOn (fun _ _ => ht) (fun p hp => hunit p.1 hp.1)
  have hd : ∀ s ∈ Ioo l u, ∀ x ∈ Icc (-1:ℝ) 1,
      HasDerivAt (fun b : ℝ => thetaA t b ((x:ℂ)+I*((t/2:ℝ):ℂ)))
        (thetaAa t s ((x:ℂ)+I*((t/2:ℝ):ℂ))) s := by
    intro s hs x _
    have hs2 := hunit s ⟨hs.1.le,hs.2.le⟩
    unfold thetaAa
    exact thetaA_a_hasDerivAt ht s _ (theta_vertical_denominator ht hs2.1 hs2.2)
      (horizontal_midline_regular ht x) (horizontal_shift_regular ht s x)
  exact (hasDerivAt_intervalIntegral_compact hlu (by norm_num : (-1:ℝ) ≤ 1) hc.1 hc.2.1 hd).const_mul (1/2:ℂ)

theorem fullComplexPeriod_a_hasDerivAt {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (fullComplexPeriod t)
      (2*(thetaEtaExpression t-thetaZeta t a)*fullComplexPeriod t a-
        2*(a-1)*fullComplexWeight t ht a) a := by
  let z := fun x : ℝ => (x:ℂ)+I*((t/2:ℝ):ℂ)
  let A := fun x : ℝ => thetaA t a (z x)
  let P := fun x : ℝ => (rhombicPeriodPair t ht).weierstrassP (z x)
  let K := 2*(thetaEtaExpression t-thetaZeta t a)
  have hc := horizontal_composite_continuousOn (S := (univ:Set ℝ)) (u := fun _ => t)
    (b := fun _ => a) (x := id) continuousOn_const continuousOn_const continuousOn_id
    (fun _ _ => ht) (fun _ _ => ha)
  have hA : Continuous A := continuousOn_univ.mp hc.1
  have hP : Continuous P := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (rhombic_weierstrassP_hasDerivAt ht (rhombic_midline_not_mem ht x)).continuousAt.comp
      (f := z) (by fun_prop)
  have hD : Continuous (fun x : ℝ => deriv (thetaA t a) (z x)) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact ((thetaA_deriv_continuousOn ht a).continuousAt
      ((thetaRegular_isOpen ht).mem_nhds (horizontal_midline_regular ht x))).comp (f := z) (by fun_prop)
  have he (x : ℝ) : thetaAa t a (z x) = K*A x-2*(a-1)*(P x*A x)-deriv (thetaA t a) (z x) := by
    rw [thetaA_spatial_deriv ht a (theta_vertical_denominator ht ha.1 ha.2)
      (horizontal_midline_regular ht x) (horizontal_shift_regular ht a x)]
    have hl := thetaLa_add_Lz_elliptic ht a (rhombic_midline_not_mem ht x)
    unfold thetaAa
    dsimp [K,A,P]
    linear_combination thetaA t a (z x)*hl
  have hzero := thetaA_integral_spatial_derivative_zero ht a (t/2)
    (fun x _ => horizontal_midline_regular ht x)
  have hIA := hA.intervalIntegrable (-1) 1 (μ := volume)
  have hIPA := (hP.mul hA).intervalIntegrable (-1) 1 (μ := volume)
  change IntervalIntegrable (fun x : ℝ => P x*A x) volume (-1) 1 at hIPA
  have hID := hD.intervalIntegrable (-1) 1 (μ := volume)
  change (∫ x : ℝ in (-1)..1, deriv (thetaA t a) (z x)) = 0 at hzero
  have hd := fullComplexPeriod_a_hasDerivAt_integral ht ha
  change HasDerivAt (fullComplexPeriod t) ((1/2:ℂ)*∫ x : ℝ in (-1)..1, thetaAa t a (z x)) a at hd
  simp_rw [he] at hd
  rw [intervalIntegral.integral_sub ((hIA.const_mul K).sub (hIPA.const_mul (2*(a-1)))) hID,
    intervalIntegral.integral_sub (hIA.const_mul K) (hIPA.const_mul (2*(a-1))),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,hzero,sub_zero] at hd
  convert hd using 1
  unfold fullComplexPeriod fullComplexWeight
  dsimp [K,A,P,z]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.fullComplexPeriod_a_hasDerivAt
