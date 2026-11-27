import TwoAxisHelicoid.SpatialConormalFlux
import TwoAxisHelicoid.SymmetricNullDifferential
import Mathlib.MeasureTheory.Integral.CircleIntegral

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped ComplexConjugate

private theorem integral_zero_of_negative_half_period {F : ℝ → ℝ} (hc : Continuous F)
    (hp : ∀ x : ℝ, F (x+Real.pi) = -F x) : (∫ x in 0..2*Real.pi, F x) = 0 := by
  have h := intervalIntegral.integral_comp_add_right (f := F) (a := 0) (b := Real.pi) Real.pi
  simp only [hp,intervalIntegral.integral_neg,zero_add] at h
  have add := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 Real.pi) (hc.intervalIntegrable Real.pi (2*Real.pi))
  rw [← two_mul] at h
  linarith

private theorem integral_zero_of_reflection {F : ℝ → ℝ}
    (hp : ∀ x : ℝ, F (2*Real.pi-x) = -F x) : (∫ x in 0..2*Real.pi, F x) = 0 := by
  have h := intervalIntegral.integral_comp_sub_left (f := F) (a := 0) (b := 2*Real.pi) (2*Real.pi)
  simp only [hp,intervalIntegral.integral_neg,sub_self,sub_zero] at h
  linarith

private theorem circleMap_half_turn (r θ : ℝ) : circleMap 0 r (θ+Real.pi) = -circleMap 0 r θ := by
  simp [circleMap,ofReal_add,add_mul,exp_add,exp_pi_mul_I]

private theorem circleMap_reflect (r θ : ℝ) : circleMap 0 r (2*Real.pi-θ) = conj (circleMap 0 r θ) := by
  rw [sub_eq_neg_add,(periodic_circleMap 0 r) (-θ),conj_circleMap_zero]

/-- The actual puncture-circle conormal flux vanishes in all three spatial
components under the two axis symmetries. The argument uses the circle
parameter itself and allows essential singularities of the forms at zero. -/
theorem two_axis_puncture_circle_flux_zero {L : PeriodPair} {p : ℂ → Fin 3 → ℂ}
    (hp : TwoAxisNullDifferential L p) (hc : ∀ j, ContinuousOn (fun z => p z j) (L.lattice : Set ℂ)ᶜ)
    (X : ℂ → Fin 3 → ℝ) (hd : ∀ z ∉ L.lattice, HasFDerivAt X (nullRealDerivative (p z)) z)
    (r : ℝ) (hcircle : ∀ θ : ℝ, circleMap 0 r θ ∉ L.lattice) (j : Fin 3) :
    (∫ θ : ℝ in 0..2*Real.pi, ‖fderiv ℝ (coordinateToEuclidean ∘ X) (circleMap 0 r θ) (circleMap 0 r θ*I)‖*
      chartRightUnitConormal X (circleMap 0 r θ) (circleMap 0 r θ*I) j) = 0 := by
  let q := fun θ : ℝ => circleMap 0 r θ
  let F := fun θ : ℝ => (q θ*p (q θ) j).re
  have hF : Continuous F := continuous_re.comp ((continuous_circleMap _ _).mul
    ((hc j).comp_continuous (continuous_circleMap _ _) hcircle))
  have eq (θ : ℝ) : ‖fderiv ℝ (coordinateToEuclidean ∘ X) (q θ) (q θ*I)‖*
      chartRightUnitConormal X (q θ) (q θ*I) j = F θ := by
    rw [chartRightUnitConormal_density (hp.null _ (hcircle θ)) (hd _ (hcircle θ))]
    change (q θ*I*p (q θ) j).im = (q θ*p (q θ) j).re
    rw [mul_right_comm,Complex.mul_I_im]
  rw [intervalIntegral.integral_congr (fun θ _ => eq θ)]
  fin_cases j
  · apply integral_zero_of_negative_half_period hF
    intro θ
    change (circleMap 0 r (θ+Real.pi)*p (circleMap 0 r (θ+Real.pi)) 0).re = _
    rw [circleMap_half_turn,hp.neg _ (hcircle θ)]
    simp [F,q]
  · apply integral_zero_of_reflection
    intro θ
    dsimp [F,q]
    rw [circleMap_reflect,hp.conjugation _ (hcircle θ)]
    simp [← map_mul]
  · apply integral_zero_of_reflection
    intro θ
    dsimp [F,q]
    rw [circleMap_reflect,hp.conjugation _ (hcircle θ)]
    simp [← map_mul]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.two_axis_puncture_circle_flux_zero
