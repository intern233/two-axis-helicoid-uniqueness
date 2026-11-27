import TwoAxisHelicoid.OpenCoreCompactnessParameterGap
import TwoAxisHelicoid.TorusGeneratorIntersections
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology Manifold ContDiff

/-- Local uniform convergence of the full spatial derivative on the core
gives uniform convergence of ordinary velocities around both compact
generator trajectories, by the chain rule on their fixed affine lifts. -/
theorem local_derivatives_control_core_trajectories {A : PeriodPair} (C : TorusGeneratingCoreModel A)
    (Z : ℕ → ℂ → EuclideanSpace ℝ (Fin 3)) (Z₀ : ℂ → EuclideanSpace ℝ (Fin 3))
    (hZ : ∀ n z, periodTorusProjection A z ∈ C.carrier → DifferentiableAt ℝ (Z n) z)
    (h₀ : ∀ z, periodTorusProjection A z ∈ C.carrier → ContDiffAt ℝ 1 Z₀ z)
    (hconv : TendstoLocallyUniformlyOn (fun n => fderiv ℝ (Z n)) (fderiv ℝ Z₀) atTop
      (periodTorusProjection A ⁻¹' C.carrier)) (i : Fin 2) :
    ContinuousOn (fun s => fderiv ℝ Z₀ (periodBasisLine A i s) (A.basis i)) (Icc (0:ℝ) 1) ∧
    TendstoUniformlyOn (fun n => deriv (Z n ∘ periodBasisLine A i))
      (fun s => fderiv ℝ Z₀ (periodBasisLine A i s) (A.basis i)) atTop (Icc 0 1) := by
  let r := periodBasisLine A i
  let K := r '' Icc 0 1
  have hr : Continuous r := continuous_iff_continuousAt.mpr fun s => (periodBasisLine_hasDerivAt A i s).continuousAt
  have hsub : K ⊆ periodTorusProjection A ⁻¹' C.carrier := by rintro _ ⟨s,_,rfl⟩; exact C.trajectory_mem i s
  have hK : IsCompact K := isCompact_Icc.image hr
  let E := ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3)) (A.basis i)
  have hlin := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (hconv.mono hsub)
  have hcomp := ((E.uniformContinuous.comp_tendstoUniformlyOn hlin).comp r).mono
    (show Icc (0:ℝ) 1 ⊆ r ⁻¹' K from fun _ hs => mem_image_of_mem r hs)
  constructor
  · intro s _
    exact (E.continuous.continuousAt.comp (((h₀ _ (C.trajectory_mem i s)).continuousAt_fderiv one_ne_zero).comp hr.continuousAt)).continuousWithinAt
  · apply hcomp.congr
    filter_upwards with n s _
    exact ((hZ n _ (C.trajectory_mem i s)).hasFDerivAt.comp_hasDerivAt s (periodBasisLine_hasDerivAt A i s)).deriv.symm

/-- Smooth convergence of graph parametrizations on compact subsets in
its usual chart form. Only the first derivative topology is needed. -/
def HasLocalC1CoreCompactness (S : Set PitchNormalizedBasicImmersion) : Prop :=
  ∀ x : ℕ → S, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (A : PeriodPair) (C : TorusGeneratingCoreModel A)
    (F : ∀ n, SmoothOpenTorusCoreMap C (rhombicPeriodPair (x (φ n)).1.t (x (φ n)).1.ht))
    (Z₀ : ℂ → EuclideanSpace ℝ (Fin 3)),
    let Z := fun n => (x (φ n)).1.torusPosition ∘ (F n).map ∘ periodTorusProjection A
    (∀ n z, periodTorusProjection A z ∈ C.carrier → DifferentiableAt ℝ (Z n) z) ∧
    (∀ z, periodTorusProjection A z ∈ C.carrier → ContDiffAt ℝ 1 Z₀ z) ∧
    TendstoLocallyUniformlyOn (fun n => fderiv ℝ (Z n)) (fderiv ℝ Z₀) atTop (periodTorusProjection A ⁻¹' C.carrier)

theorem local_C1_core_compactness_supplies_smooth_open_cores {S : Set PitchNormalizedBasicImmersion}
    (h : HasLocalC1CoreCompactness S) : HasSubsequentialSmoothOpenCore S := by
  intro x
  obtain ⟨φ,hφ,A,C,F,Z₀,hZ,h₀,hh⟩ := h x
  let Z := fun n => (x (φ n)).1.torusPosition ∘ (F n).map ∘ periodTorusProjection A
  have hc := local_derivatives_control_core_trajectories C Z Z₀ hZ h₀ hh
  exact ⟨φ,hφ,A,C,F,fun i s => fderiv ℝ Z₀ (periodBasisLine A i s) (A.basis i),fun i => (hc i).1,fun i => (hc i).2⟩

theorem local_C1_core_compactness_gives_gap_and_finite_images {S : Set PitchNormalizedBasicImmersion}
    (h : HasLocalC1CoreCompactness S) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ X ∈ S, ε ≤ X.t) ∧
    ((fun X : PitchNormalizedBasicImmersion => Quotient.mk (spatialSimilaritySetoid _) X.image) '' S).Finite :=
  smooth_open_cores_imply_gap_and_finitely_many_images (local_C1_core_compactness_supplies_smooth_open_cores h)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.local_C1_core_compactness_gives_gap_and_finite_images
