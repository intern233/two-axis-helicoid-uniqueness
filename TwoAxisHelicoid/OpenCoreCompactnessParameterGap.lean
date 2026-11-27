import TwoAxisHelicoid.OpenCoreSmoothTransport
import TwoAxisHelicoid.CompactCoreFiniteSimilarityClasses

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology Manifold ContDiff

noncomputable def PitchNormalizedBasicImmersion.torusPosition (X : PitchNormalizedBasicImmersion) :
    PeriodTorus (rhombicPeriodPair X.t X.ht) → EuclideanSpace ℝ (Fin 3) := fun q =>
  coordinateToEuclidean (X.position ((Quotient.mk_surjective :
    Function.Surjective (periodTorusProjection (rhombicPeriodPair X.t X.ht))) q).choose)

theorem PitchNormalizedBasicImmersion.torusPosition_projection (X : PitchNormalizedBasicImmersion)
    (z : ℂ) (hz : z ∉ (rhombicPeriodPair X.t X.ht).lattice) :
    X.torusPosition (periodTorusProjection (rhombicPeriodPair X.t X.ht) z) = coordinateToEuclidean (X.position z) := by
  let L := rhombicPeriodPair X.t X.ht
  let q := periodTorusProjection L z
  let h := (Quotient.mk_surjective : Function.Surjective (periodTorusProjection L)) q
  have hm : h.choose-z ∈ L.lattice := (periodTorusProjection_eq_iff L z h.choose).mp h.choose_spec.symm
  have hv := X.periodic z hz (h.choose-z) hm
  rw [add_sub_cancel] at hv
  exact congrArg coordinateToEuclidean hv

/-- Local smooth convergence on a marked open core supplies open maps
and convergence of the ordinary spatial velocities along its two fixed
reference curves. This formulation uses no approximating generator or
homology, no plane lifts, no length bounds and no period estimates. -/
def HasSubsequentialSmoothOpenCore (S : Set PitchNormalizedBasicImmersion) : Prop :=
  ∀ x : ℕ → S, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (A : PeriodPair) (C : TorusGeneratingCoreModel A)
    (F : ∀ n, SmoothOpenTorusCoreMap C (rhombicPeriodPair (x (φ n)).1.t (x (φ n)).1.ht))
    (v : Fin 2 → ℝ → EuclideanSpace ℝ (Fin 3)), (∀ i, ContinuousOn (v i) (Icc 0 1)) ∧
      ∀ i, TendstoUniformlyOn (fun n => deriv ((x (φ n)).1.torusPosition ∘ (F n).trajectory i))
        (v i) atTop (Icc 0 1)

theorem smooth_open_cores_supply_generating_curves {S : Set PitchNormalizedBasicImmersion}
    (hS : HasSubsequentialSmoothOpenCore S) : HasSubsequentialSmoothGeneratingCurves S := by
  classical
  intro x
  obtain ⟨φ,hφ,A,C,F,v,hv,hs⟩ := hS x
  choose D hD using fun n => (F n).lifted_generators
  refine ⟨φ,hφ,D,v,hv,fun i => ?_⟩
  have he (n : ℕ) : coordinateToEuclidean ∘ (x (φ n)).1.position ∘ ((D n).arc i).curve =
      (x (φ n)).1.torusPosition ∘ (F n).trajectory i := by
    funext s
    change coordinateToEuclidean ((x (φ n)).1.position (((D n).arc i).curve s)) = (x (φ n)).1.torusPosition ((F n).trajectory i s)
    rw [← hD n i s]
    apply ((x (φ n)).1.torusPosition_projection _ _).symm
    intro h
    exact (F n).avoids _ (C.trajectory_mem i s) ((hD n i s).symm.trans ((periodTorusProjection_eq_zero _ _).mpr h))
  simpa only [he] using hs i

/-- The original Appendix B conclusions in geometric image space, from a
subsequence of smooth local core charts. They do not use the horizontal
box certificates or a small-height horizontal sign estimate. -/
theorem smooth_open_cores_imply_gap_and_finitely_many_images {S : Set PitchNormalizedBasicImmersion}
    (hS : HasSubsequentialSmoothOpenCore S) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ X ∈ S, ε ≤ X.t) ∧
    ((fun X : PitchNormalizedBasicImmersion => Quotient.mk (spatialSimilaritySetoid _) X.image) '' S).Finite := by
  have h := smooth_open_cores_supply_generating_curves hS
  exact ⟨core_compactness_implies_uniform_parameter_gap (smooth_generating_curves_give_subsequential_bounded_cores h),
    smooth_generating_core_finite_similarity_classes h⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_open_cores_imply_gap_and_finitely_many_images
