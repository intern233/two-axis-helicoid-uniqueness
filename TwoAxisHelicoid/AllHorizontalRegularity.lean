import TwoAxisHelicoid.VerticalRegularity
import TwoAxisHelicoid.ThetaADoublePeriod
import TwoAxisHelicoid.ThetaPeriodIntegral

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped ComplexConjugate
attribute [local irreducible] thetaA thetaJet thetaQuotient

theorem horizontal_midline_regular {t : ℝ} (ht : 0 < t) (x : ℝ) :
    thetaJet t 0 (Real.pi*((x:ℂ)+I*((t/2:ℝ):ℂ))/2) ≠ 0 :=
  mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht _).mp (rhombic_midline_not_mem ht x)

theorem horizontal_shift_regular {t : ℝ} (ht : 0 < t) (a x : ℝ) :
    thetaJet t 0 (Real.pi*((x:ℂ)+I*((t/2:ℝ):ℂ)-a)/2) ≠ 0 := by
  have he : ((x-a:ℝ):ℂ)+I*((t/2:ℝ):ℂ) = (x:ℂ)+I*((t/2:ℝ):ℂ)-a := by push_cast; ring
  rw [← he]
  exact horizontal_midline_regular ht (x-a)

theorem horizontal_integrand_continuous {t : ℝ} (ht : 0 < t) (a : ℝ) :
    Continuous (fun x : ℝ => thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ))) := by
  rw [continuous_iff_continuousAt]
  intro x
  have harg : ContinuousAt (fun u : ℝ => (u:ℂ)+I*((t/2:ℝ):ℂ)) x := by fun_prop
  exact (thetaA_differentiableAt ht a (horizontal_midline_regular ht x)).continuousAt.comp
    (f := fun u : ℝ => (u:ℂ)+I*((t/2:ℝ):ℂ)) harg

theorem horizontal_integral_halves {t : ℝ} (ht : 0 < t) (a : ℝ) :
    (∫ x : ℝ in 0..1, thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ))) =
      conj (∫ x : ℝ in (-1)..0, thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ))) := by
  let f : ℝ → ℂ := fun x => thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ))
  calc
    _ = ∫ x : ℝ in (-1)..0, f (x+1) := by
      symm
      simpa only [neg_add_cancel,zero_add] using
        intervalIntegral.integral_comp_add_right f (a := (-1:ℝ)) (b := 0) 1
    _ = ∫ x : ℝ in (-1)..0, conj (f x) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact thetaA_midline_add_one ht a x
    _ = _ := intervalIntegral.intervalIntegral_conj

theorem horizontal_period_half {t : ℝ} (ht : 0 < t) (a : ℝ) :
    thetaHorizontalPeriod t a = (∫ x : ℝ in (-1)..0,
      thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ))).re := by
  have hc := horizontal_integrand_continuous ht a
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-1) 0 (μ := volume)) (hc.intervalIntegrable 0 1 (μ := volume))
  unfold thetaHorizontalPeriod
  rw [← hs,horizontal_integral_halves ht a]
  simp only [Complex.add_re,Complex.conj_re]
  ring

theorem horizontal_composite_continuousOn {α : Type*} [TopologicalSpace α] {S : Set α}
    {u b x : α → ℝ} (hu : ContinuousOn u S) (hb : ContinuousOn b S) (hx : ContinuousOn x S)
    (ht : ∀ p ∈ S, 0 < u p) (ha : ∀ p ∈ S, b p ∈ Ioo (0:ℝ) 2) :
    ContinuousOn (fun p => thetaA (u p) (b p) ((x p:ℂ)+I*((u p/2:ℝ):ℂ))) S ∧
    ContinuousOn (fun p => thetaAa (u p) (b p) ((x p:ℂ)+I*((u p/2:ℝ):ℂ))) S ∧
    ContinuousOn (fun p => thetaAtMidline (u p) (b p) ((x p:ℂ)+I*((u p/2:ℝ):ℂ))) S := by
  let z : α → ℂ := fun p => (x p:ℂ)+I*((u p/2:ℝ):ℂ)
  have hz : ContinuousOn z S :=
    (Complex.continuous_ofReal.comp_continuousOn hx).add
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (hu.div_const 2)))
  have hna (p) (hp : p ∈ S) : thetaJet (u p) 0 (Real.pi*b p/2) ≠ 0 :=
    theta_vertical_denominator (ht p hp) (ha p hp).1 (ha p hp).2
  have hnv (p) (hp : p ∈ S) : thetaJet (u p) 0 (Real.pi*z p/2) ≠ 0 :=
    horizontal_midline_regular (ht p hp) (x p)
  have hnm (p) (hp : p ∈ S) : thetaJet (u p) 0 (Real.pi*(z p-b p)/2) ≠ 0 :=
    horizontal_shift_regular (ht p hp) (b p) (x p)
  exact ⟨thetaA_comp_continuousOn hu hb hz ht hna hnv,
    thetaAa_comp_continuousOn hu hb hz ht hna hnv hnm,
    thetaAtMidline_comp_continuousOn hu hb hz ht hna hnv hnm
      (fun p hp => thetaJet_one_at_zero_ne_zero_of_pos (ht p hp))⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.horizontal_period_half
