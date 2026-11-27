import TwoAxisHelicoid.FixedCutoffOriginalGeometricProof
import TwoAxisHelicoid.UnmarkedChartPlaneLimit

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology RealInnerProductSpace

/-- Appendix B.3 with the smooth-subsequence conclusion of Hoffman–White
at one fixed cutoff. The compactness input concerns positions and ordinary
first derivatives on the local sheets. The proof transports the generating
curves and derives the flux gap, including exclusion of periodic limits. -/
theorem original_appendix_B_from_smooth_cutoff_subsequences {J : Type*}
    (η : ℝ) (eta : Real.pi/2 < η) (family : FixedAxisHelicoidNormalClass J)
    (both : ∀ m y ν, (y,ν) ∈ family.normal m → (y,-ν) ∈ family.normal m)
    (unit : ∀ m (q : PhysicalPositionNormal), q ∈ family.normal m → ‖q.2‖ = 1)
    (smooth : ∀ a : ℕ → J,
      (∀ n, (η : WithTop ℝ) ≤ physicalScrewHalfPeriod (physicalNormalPositions (family.normal (a n)))) →
      ∃ m, (η : WithTop ℝ) ≤ physicalScrewHalfPeriod (physicalNormalPositions (family.normal m)) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (B : Type) (X N : B → SurfaceEuclideanSpace),
          family.normal m = unorientedSurfaceNormals X N ∧
          LocalSpatialImageLimit (fun n => Prod.fst '' family.normal (a (φ n))) (range X) ∧
          ∀ b, ∃ T : ℂ →L[ℝ] SurfaceEuclideanSpace, Function.Injective T ∧
            (∀ v, ⟪T v, N b⟫ = 0) ∧ ∀ V ∈ 𝓝 T, ∃ W ∈ 𝓝 (X b),
              ∀ᶠ n in atTop, ∀ q ∈ family.normal (a (φ n)), q.1 ∈ W →
                ∃ (Y : ℂ → SurfaceEuclideanSpace) (w : ℂ), Y w = q.1 ∧ fderiv ℝ Y w ∈ V ∧
                  ∀ v, ⟪fderiv ℝ Y w v, q.2⟫ = 0)
    (slab : ∀ m (k : ℝ), η ≤ k →
      physicalScrewHalfPeriod (physicalNormalPositions (family.normal m)) = (k : WithTop ℝ) →
      (∀ b : ℝ, physicalNormalPositions (family.normal m) ≠ range (axisRuledHelicoid Complex.I 1 b)) →
      ∃ P : PeriodicSlabNormalMember (family.normal m), P.halfPeriod = k) :
    HasSubsequentialSmoothGeneratingCurves positiveUnitPitchFamily ∧
    (∃ ε : ℝ, 0 < ε ∧ (∀ W ∈ embeddedPitchFamily, ε ≤ W.t) ∧
      ∀ s : OriginalHelicoidRepresentative, ∃ W ∈ positiveUnitPitchFamily, ε ≤ W.t ∧
        (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalHelicoidRepresentative => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite := by
  apply original_graph_appendix_B_from_one_fixed_cutoff η eta
  apply point_normal_cutoff_subsequence_gives_handle_limit embedded_torus_disk_complement_has_open_handle η family
  · intro a cut
    obtain ⟨m, member, φ, inc, B, X, N, normal, positions, charts⟩ :=
      smooth a (fun n => (measured_physical_screw_infimum_cutoff _ η).mpr (cut n))
    refine ⟨m, (measured_physical_screw_infimum_cutoff _ η).mp member, φ, inc, ?_⟩
    change LocalSpatialImageLimit (fun n => family.normal (a (φ n))) (family.normal m)
    rw [normal]
    apply unmarked_chart_derivatives_give_normal_limit (X := X) (N := N)
      (S := fun n => family.normal (a (φ n))) (fun n => both (a (φ n)))
      (fun n => unit (a (φ n))) positions
    intro b
    obtain ⟨T, inj, orth, near⟩ := charts b
    have atPoint : (X b, N b) ∈ family.normal m := by
      rw [normal]
      exact ⟨b, rfl, Or.inl rfl⟩
    exact ⟨T, inj, unit m (X b, N b) atPoint, orth, near⟩
  · intro m cut present
    have positive := (half_pos Real.pi_pos).trans eta
    obtain ⟨k, lower, measured, _⟩ := positive_cutoff_attains_measured_screw_period positive cut present
    obtain ⟨P, _⟩ := slab m k lower measured (positive_cutoff_excludes_reference_helicoid positive cut)
    exact ⟨P⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.original_appendix_B_from_smooth_cutoff_subsequences
