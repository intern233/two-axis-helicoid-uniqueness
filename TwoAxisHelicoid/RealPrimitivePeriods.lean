import TwoAxisHelicoid.RhombicGlobalPrimitiveRegularity
import TwoAxisHelicoid.CoordinatePrimitiveUniqueness

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology Interval

theorem real_primitive_path_integral_eq_sub {F : ℂ → ℝ} {f : ℂ → ℂ}
    {path : ℝ → ℂ} {δ : ℂ} {a b : ℝ}
    (hpath : ∀ s ∈ uIcc a b, HasDerivAt path δ s)
    (hF : ∀ s ∈ uIcc a b, HasFDerivAt F (realCoefficientDerivative (f (path s))) (path s))
    (hI : IntervalIntegrable (fun s => f (path s)) volume a b) :
    (δ*(∫ s : ℝ in a..b, f (path s))).re = F (path b)-F (path a) := by
  have hD (s : ℝ) (hs : s ∈ uIcc a b) :
      HasDerivAt (F ∘ path) ((δ*f (path s)).re) s :=
    (hF s hs).comp_hasDerivAt s (hpath s hs)
  have hIR : IntervalIntegrable (fun s => (δ*f (path s)).re) volume a b :=
    intervalIntegrable_iff.mpr (Complex.reCLM.integrable_comp (hI.const_mul δ).def')
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hD hIR
  calc
    (δ*(∫ s : ℝ in a..b, f (path s))).re =
        (∫ s : ℝ in a..b, δ*f (path s)).re := by rw [intervalIntegral.integral_const_mul]
    _ = ∫ s : ℝ in a..b, (δ*f (path s)).re :=
      (Complex.reCLM.intervalIntegral_comp_comm (hI.const_mul δ)).symm
    _ = F (path b)-F (path a) := he

theorem actual_coordinate_primitive_component {t a c : ℝ} (ht : 0 < t)
    {X : ℂ → Fin 3 → ℝ} (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    {z : ℂ} (hz : z ∉ (rhombicPeriodPair t ht).lattice) (j : Fin 3) :
    HasFDerivAt (fun w => X w j) (realCoefficientDerivative (coordinateData t a c ht z j)) z := by
  have h := (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z (hX z hz)
  exact h

/-- A single-valued real primitive forces the real integral on any smooth
constant-velocity generator to vanish. -/
theorem real_primitive_generator_closed {t : ℝ} (ht : 0 < t)
    {F : ℂ → ℝ} {f : ℂ → ℂ}
    (hf : ∀ z ∉ (rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    (hF : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      HasFDerivAt F (realCoefficientDerivative (f z)) z)
    (hp : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      ∀ ω ∈ (rhombicPeriodPair t ht).lattice, F (z+ω) = F z)
    {path : ℝ → ℂ} {δ ω : ℂ}
    (hpath : ∀ s : ℝ, HasDerivAt path δ s)
    (hreg : ∀ s ∈ Icc (-1 : ℝ) 1, path s ∉ (rhombicPeriodPair t ht).lattice)
    (hω : ω ∈ (rhombicPeriodPair t ht).lattice) (hend : path 1 = path (-1)+ω) :
    (δ*(∫ s : ℝ in (-1)..1, f (path s))).re = 0 := by
  have hsub (s : ℝ) (hs : s ∈ uIcc (-1 : ℝ) 1) : s ∈ Icc (-1 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hs
  have hc : ContinuousOn (fun s => f (path s)) (uIcc (-1 : ℝ) 1) := by
    intro s hs
    exact ((hf _ (hreg s (hsub s hs))).continuousAt.comp (hpath s).continuousAt).continuousWithinAt
  have he := real_primitive_path_integral_eq_sub (fun s _ => hpath s)
    (fun s hs => hF _ (hreg s (hsub s hs))) hc.intervalIntegrable
  rw [hend,hp _ (hreg (-1) (by norm_num)) ω hω,sub_self] at he
  exact he

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.real_primitive_generator_closed
