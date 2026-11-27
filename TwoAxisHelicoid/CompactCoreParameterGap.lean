import TwoAxisHelicoid.NormalizedBoundedCoreObstruction
import TwoAxisHelicoid.PrimitivePeriodNecessity
import TwoAxisHelicoid.FullPeriodDiscrete

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- A single-valued actual basic-branch position map after normalizing the
asymptotic pitch to absolute value one. -/
structure PitchNormalizedBasicImmersion where
  t : ℝ
  ht : 0 < t
  hT : t < ellipticVerticalUpper
  c : ℝ
  scale : |c| = 2*(1-verticalA t)
  position : ℂ → Fin 3 → ℝ
  differential : HasTwoAxisHelicoidCoordinateDifferential position t (verticalA t) c ht
  periodic : ∀ z ∉ (rhombicPeriodPair t ht).lattice, ∀ ω ∈ (rhombicPeriodPair t ht).lattice,
    position (z+ω) = position z

/-- The precise compact-core consequence of smooth geometric compactness
used in the original Appendix B argument. -/
def HasSubsequentialBoundedGeneratingCores (S : Set PitchNormalizedBasicImmersion) : Prop :=
  ∀ x : ℕ → S, ∃ (φ : ℕ → ℕ) (B : ℝ), StrictMono φ ∧ 0 ≤ B ∧
    ∀ n, Nonempty (BoundedGeneratingCore (rhombicPeriodPair (x (φ n)).1.t (x (φ n)).1.ht) (x (φ n)).1.position B)

/-- Geometric compactness of the cores gives an actual positive parameter
gap without using any horizontal-period estimate near zero. -/
theorem core_compactness_implies_uniform_parameter_gap {S : Set PitchNormalizedBasicImmersion}
    (hS : HasSubsequentialBoundedGeneratingCores S) : ∃ ε : ℝ, 0 < ε ∧ ∀ X ∈ S, ε ≤ X.t := by
  classical
  by_contra! h
  have pick (n : ℕ) : ∃ X : S, X.1.t < 1/((n:ℝ)+1) := by
    obtain ⟨X,hX,hx⟩ := h (1/((n:ℝ)+1)) (by positivity)
    exact ⟨⟨X,hX⟩,hx⟩
  choose x hx using pick
  obtain ⟨φ,B,hφ,hB,hC⟩ := hS x
  have hlim : Tendsto (fun n => (x n).1.t) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat
      (fun n => (x n).1.ht.le) (fun n => (hx n).le),Eventually.of_forall fun n => (x n).1.ht⟩
  exact bounded_generating_cores_preclude_height_collapse (fun n => (x (φ n)).1.ht) (fun n => (x (φ n)).1.hT)
    (fun n => (x (φ n)).1.scale) (fun n => (x (φ n)).1.differential) hB (fun n => (hC n).some)
    (hlim.comp hφ.tendsto_atTop)

/-- The compact-core parameter gap, the right-end limit and analyticity imply
finiteness for the actual periods of any such family. -/
theorem core_compactness_implies_finite_parameters {S : Set PitchNormalizedBasicImmersion}
    (hS : HasSubsequentialBoundedGeneratingCores S) : (PitchNormalizedBasicImmersion.t '' S).Finite := by
  obtain ⟨ε,hε,hS'⟩ := core_compactness_implies_uniform_parameter_gap hS
  apply (actualPeriodAlong_finite_zeros_above hε).subset
  rintro _ ⟨X,hX,rfl⟩
  obtain ⟨ha,_⟩ := verticalA_spec ⟨X.ht,X.hT⟩
  have hc : X.c ≠ 0 := by intro h; have hs := X.scale; rw [h,abs_zero] at hs; linarith [ha.2]
  exact ⟨hS' X hX,X.hT,(periodic_actual_primitive_period_equations X.ht ha hc X.differential X.periodic).2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.core_compactness_implies_uniform_parameter_gap
#print axioms TwoAxisHelicoid.core_compactness_implies_finite_parameters
