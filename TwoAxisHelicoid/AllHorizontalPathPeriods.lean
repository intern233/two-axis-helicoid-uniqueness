import TwoAxisHelicoid.PiecewiseComplexPeriods
import TwoAxisHelicoid.PeriodTorusConjugation
import TwoAxisHelicoid.PrimitivePeriodNecessity

namespace TwoAxisHelicoid
open Complex Set

/-- All real periods of the two horizontal coordinate differentials, on
piecewise continuously differentiable paths whose endpoints agree in the
actual quotient torus. -/
def AllHorizontalPathPeriodsVanish (t a c : ℝ) (ht : 0 < t) : Prop :=
  ∀ {x y : ℂ} (p : PiecewiseComplexPath ((rhombicPeriodPair t ht).lattice : Set ℂ)ᶜ x y),
    periodTorusProjection (rhombicPeriodPair t ht) x = periodTorusProjection (rhombicPeriodPair t ht) y →
    ∀ j : Fin 3, j ≠ 2 → (p.integral (fun z => coordinateData t a c ht z j)).re = 0

/-- Proposition 6.1 for the basic data with its vertical period solved.
An arbitrary closed path can have corners and can wind around the end. -/
theorem all_horizontal_path_periods_iff {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 1)
    (hc : c ≠ 0) (hG : thetaG t a = 0) :
    AllHorizontalPathPeriodsVanish t a c ht ↔ thetaHorizontalPeriod t a = 0 := by
  let L := rhombicPeriodPair t ht
  constructor
  · intro h
    let A : ComplexPeriodArc (L.lattice : Set ℂ)ᶜ := {
      left := -1, right := 1, ordered := by norm_num
      curve := originalPeriodPath t, velocity := fun _ => (1-I*t)/2
      stays := fun _ hs => rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht hs)
      continuous_curve := fun s _ => (originalPeriodPath_hasDerivAt t s).continuousAt.continuousWithinAt
      continuous_velocity := continuousOn_const
      derivative := fun s _ => originalPeriodPath_hasDerivAt t s }
    have hω : 1-I*t ∈ L.lattice := by
      apply PeriodPair.mem_lattice.mpr
      refine ⟨1,-1,?_⟩
      simp only [L,rhombicPeriodPair,Int.cast_one,Int.cast_neg]
      ring
    have hend : A.curve A.right - A.curve A.left = 1-I*t := by
      dsimp [A,originalPeriodPath]
      push_cast
      ring
    have h0 := h (.arc A) ((periodTorusProjection_eq_iff L _ _).mpr (hend ▸ hω)) 0 (by decide)
    change (∫ s : ℝ in (-1)..1, ((1-I*t)/2)*coordinateData t a c ht (originalPeriodPath t s) 0).re = 0 at h0
    rw [intervalIntegral.integral_const_mul] at h0
    change (originalCoordinatePeriod t a c ht 0).re = 0 at h0
    rw [(originalCoordinatePeriod_horizontal ht).1] at h0
    simpa only [mul_re,neg_re,neg_im,ofReal_re,ofReal_im,neg_zero,zero_mul,sub_zero,
      originalSlopingPeriod_re_eq_horizontal ht a,mul_eq_zero,neg_eq_zero,hc,false_or] using h0
  · intro hH x y p hxy j _
    obtain ⟨X,hX,hper⟩ := (actual_global_primitive_exists_iff ht ha hc).mpr ⟨hG,hH⟩
    have hf (z : ℂ) (hz : z ∉ L.lattice) : AnalyticAt ℂ (fun w => coordinateData t a c ht w j) z :=
      ((ContinuousLinearMap.proj j : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt _).comp (coordinateData_analyticAt ht hz)
    have he := p.integral_re_eq_sub (fun z hz => (hf z hz).continuousAt.continuousWithinAt)
      (fun z hz => actual_coordinate_primitive_component ht hX hz j)
    have h := hper x (y-x) ((periodTorusProjection_eq_iff L _ _).mp hxy)
    rw [add_sub_cancel] at h
    simpa only [h,sub_self] using he

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.all_horizontal_path_periods_iff
