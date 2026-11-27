import TwoAxisHelicoid.RealPrimitivePeriods
import TwoAxisHelicoid.ActualGlobalImmersion

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate
set_option maxHeartbeats 1000000

/-- The actual coordinate integrals close because a real primitive is
single-valued on the lattice quotient. The closing equations are conclusions. -/
theorem periodic_actual_primitive_generators_close {t a c : ℝ} (ht : 0 < t)
    {X : ℂ → Fin 3 → ℝ} (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (hp : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      ∀ ω ∈ (rhombicPeriodPair t ht).lattice, X (z+ω) = X z) :
    ∀ j : Fin 3, (originalCoordinatePeriod t a c ht j).re = 0 ∧
      (conjugateCoordinatePeriod t a c ht j).re = 0 := by
  intro j
  have hf (z : ℂ) (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
      AnalyticAt ℂ (fun w => coordinateData t a c ht w j) z :=
    ((ContinuousLinearMap.proj j : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt _).comp
      (coordinateData_analyticAt ht hz)
  have hF (z : ℂ) (hz : z ∉ (rhombicPeriodPair t ht).lattice) :=
    actual_coordinate_primitive_component ht hX hz j
  have hper (z : ℂ) (hz : z ∉ (rhombicPeriodPair t ht).lattice)
      (ω : ℂ) (hω : ω ∈ (rhombicPeriodPair t ht).lattice) : X (z+ω) j = X z j :=
    congrFun (hp z hz ω hω) j
  constructor
  · have hω : 1-I*t ∈ (rhombicPeriodPair t ht).lattice := by
      apply PeriodPair.mem_lattice.mpr
      refine ⟨1,-1,?_⟩
      simp only [rhombicPeriodPair,Int.cast_one,Int.cast_neg]
      ring
    have hend : originalPeriodPath t 1 = originalPeriodPath t (-1)+(1-I*t) := by
      unfold originalPeriodPath
      push_cast
      ring
    exact real_primitive_generator_closed ht hf hF hper (originalPeriodPath_hasDerivAt t)
      (fun s hs => rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht hs)) hω hend
  · have hend : conj (originalPeriodPath t 1) = conj (originalPeriodPath t (-1))+(1+I*t) := by
      simp [originalPeriodPath,map_ofNat]
      ring
    exact real_primitive_generator_closed ht hf hF hper (conjugatePeriodPath_hasDerivAt t)
      (fun s hs => rhombic_open_rectangle_not_mem ht (conjugatePeriodPath_mem_rectangle ht hs))
      (rhombicPeriodPair t ht).ω₂_mem_lattice hend

theorem periodic_actual_primitive_period_equations {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    {X : ℂ → Fin 3 → ℝ} (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (hp : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      ∀ ω ∈ (rhombicPeriodPair t ht).lattice, X (z+ω) = X z) :
    thetaG t a = 0 ∧ thetaHorizontalPeriod t a = 0 :=
  (original_all_generators_close_iff ht ⟨ha.1,by linarith [ha.2]⟩ hc).mp
    (periodic_actual_primitive_generators_close ht hX hp)

/-- An exact equivalence between the two actual scalar equations and
existence of a single global lattice-periodic real primitive of all coordinate
forms. Thus no unproved all-loops-period hypothesis is used in reconstruction. -/
theorem actual_global_primitive_exists_iff {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) :
    (∃ X : ℂ → Fin 3 → ℝ, HasTwoAxisHelicoidCoordinateDifferential X t a c ht ∧
      ∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice → X (z+ω) = X z) ↔
      thetaG t a = 0 ∧ thetaHorizontalPeriod t a = 0 := by
  constructor
  · rintro ⟨X,hX,hp⟩
    exact periodic_actual_primitive_period_equations ht ha hc hX (fun z _ ω hω => hp z ω hω)
  · rintro ⟨hG,hH⟩
    have h := actual_global_conformal_harmonic_immersion ht ha hc hG hH
    exact ⟨actualGlobalImmersion t a c ht,fun z hz => (h.2.2.2 z hz).1,h.1⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_global_primitive_exists_iff
