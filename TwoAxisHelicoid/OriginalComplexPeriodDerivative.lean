import TwoAxisHelicoid.OriginalPeriodRegularity
import TwoAxisHelicoid.EllipticPeriodDerivative

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Interval
attribute [local irreducible] thetaJet thetaA thetaLa thetaLz

noncomputable def originalComplexWeight (t : ℝ) (ht : 0 < t) (a : ℝ) : ℂ :=
  slopingIntegral t (fun z => (rhombicPeriodPair t ht).weierstrassP z*thetaA t a z)

theorem originalSlopingPeriod_a_hasDerivAt_integral {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (originalSlopingPeriod t)
      (slopingIntegral t (thetaAa t a)) a := by
  let l := a/2
  let u := (a+1)/2
  have hlu : a ∈ Ioo l u := by dsimp [l,u]; constructor <;> linarith [ha.1,ha.2]
  have hunit (b : ℝ) (hb : b ∈ Icc l u) : b ∈ Ioo (0 : ℝ) 1 := by
    dsimp [l,u] at hb
    constructor <;> linarith [ha.1,ha.2,hb.1,hb.2]
  let S : Set (ℝ × ℝ) := Icc l u ×ˢ Icc (-1 : ℝ) 1
  have hz : ContinuousOn (fun p : ℝ × ℝ => originalPeriodPath t p.2) S := by
    unfold originalPeriodPath
    fun_prop
  have hna : ∀ p ∈ S, thetaJet t 0 (Real.pi*p.1/2) ≠ 0 := by
    intro p hp
    have hb := hunit p.1 hp.1
    exact theta_vertical_denominator ht hb.1 (by linarith [hb.2])
  have hnz : ∀ p ∈ S, thetaJet t 0 (Real.pi*originalPeriodPath t p.2/2) ≠ 0 :=
    fun p hp => originalPath_regular ht hp.2
  have hnm : ∀ p ∈ S, thetaJet t 0 (Real.pi*(originalPeriodPath t p.2-p.1)/2) ≠ 0 :=
    fun p hp => originalPath_shift_regular ht (hunit p.1 hp.1) hp.2
  have hc := thetaA_comp_continuousOn (u := fun _ : ℝ × ℝ => t)
    (b := Prod.fst) continuousOn_const continuous_fst.continuousOn hz
    (fun _ _ => ht) hna hnz
  have hc' := thetaAa_comp_continuousOn (u := fun _ : ℝ × ℝ => t)
    (b := Prod.fst) continuousOn_const continuous_fst.continuousOn hz
    (fun _ _ => ht) hna hnz hnm
  have hd : ∀ b ∈ Ioo l u, ∀ s ∈ Icc (-1 : ℝ) 1,
      HasDerivAt (fun r : ℝ => thetaA t r (originalPeriodPath t s))
        (thetaAa t b (originalPeriodPath t s)) b := by
    intro b hb s hs
    have hb' := hunit b ⟨hb.1.le,hb.2.le⟩
    exact thetaA_a_hasDerivAt ht b _
      (theta_vertical_denominator ht hb'.1 (by linarith [hb'.2]))
      (originalPath_regular ht hs) (originalPath_shift_regular ht hb' hs)
  exact (hasDerivAt_intervalIntegral_compact hlu (by norm_num : (-1 : ℝ) ≤ 1)
    hc hc' hd).const_mul ((1-I*t)/2)

theorem originalSlopingPeriod_a_hasDerivAt {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (originalSlopingPeriod t)
      (2*(thetaEtaExpression t-thetaZeta t a)*originalSlopingPeriod t a-
        2*(a-1)*originalComplexWeight t ht a) a := by
  let z := originalPeriodPath t
  let A := fun s : ℝ => thetaA t a (z s)
  let P := fun s : ℝ => (rhombicPeriodPair t ht).weierstrassP (z s)
  let K := 2*(thetaEtaExpression t-thetaZeta t a)
  have hA : ContinuousOn A (Icc (-1 : ℝ) 1) := by
    apply (thetaA_holomorphic_original_rectangle ht a).continuousOn.comp
      (by dsimp [z]; unfold originalPeriodPath; fun_prop)
    exact fun s hs => originalPeriodPath_mem_rectangle ht hs
  have hP : ContinuousOn P (Icc (-1 : ℝ) 1) := by
    intro s hs
    exact ((rhombicPeriodPair t ht).analyticOnNhd_weierstrassP _
      (rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht hs))).continuousAt.comp_continuousWithinAt
        (f := z) (by dsimp [z]; unfold originalPeriodPath; fun_prop)
  have hD := originalPath_derivative_continuousOn ht a
  have hIA := hA.intervalIntegrable_of_Icc (by norm_num : (-1 : ℝ) ≤ 1) (μ := volume)
  have hIPA := (hP.mul hA).intervalIntegrable_of_Icc (by norm_num : (-1 : ℝ) ≤ 1) (μ := volume)
  have hID := hD.intervalIntegrable_of_Icc (by norm_num : (-1 : ℝ) ≤ 1) (μ := volume)
  change IntervalIntegrable (fun s : ℝ => P s*A s) volume (-1) 1 at hIPA
  change IntervalIntegrable (fun s : ℝ => deriv (thetaA t a) (z s)) volume (-1) 1 at hID
  have he (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) :
      thetaAa t a (z s) = K*A s-2*(a-1)*(P s*A s)-deriv (thetaA t a) (z s) := by
    rw [thetaA_spatial_deriv ht a
      (theta_vertical_denominator ht ha.1 (by linarith [ha.2]))
      (originalPath_regular ht hs) (originalPath_shift_regular ht ha hs)]
    have hl := thetaLa_add_Lz_elliptic ht a
      (rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht hs))
    unfold thetaAa
    dsimp [K,A,P,z]
    linear_combination thetaA t a (originalPeriodPath t s)*hl
  have hInt : (∫ s : ℝ in (-1)..1, thetaAa t a (z s)) =
      K*(∫ s : ℝ in (-1)..1, A s)-2*(a-1)*(∫ s : ℝ in (-1)..1, P s*A s)-
        ∫ s : ℝ in (-1)..1, deriv (thetaA t a) (z s) := by
    calc
      _ = ∫ s : ℝ in (-1)..1, K*A s-2*(a-1)*(P s*A s)-deriv (thetaA t a) (z s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact he s (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hs)
      _ = _ := by
        rw [intervalIntegral.integral_sub ((hIA.const_mul K).sub (hIPA.const_mul (2*(a-1)))) hID,
          intervalIntegral.integral_sub (hIA.const_mul K) (hIPA.const_mul (2*(a-1))),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have hzero := originalPath_spatial_derivative_integral_zero ht a
  have hd := originalSlopingPeriod_a_hasDerivAt_integral ht ha
  change HasDerivAt (originalSlopingPeriod t)
    (((1-I*t)/2)*(∫ s : ℝ in (-1)..1, thetaAa t a (z s))) a at hd
  rw [hInt] at hd
  convert hd using 1
  unfold originalSlopingPeriod originalComplexWeight slopingIntegral
  dsimp [K,A,P,z]
  change ((1-I*t)/2)*(∫ s : ℝ in (-1)..1,
    deriv (thetaA t a) (originalPeriodPath t s)) = 0 at hzero
  linear_combination hzero

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.originalSlopingPeriod_a_hasDerivAt
