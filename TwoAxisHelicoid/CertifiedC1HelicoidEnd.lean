import TwoAxisHelicoid.ActualTorusC1HelicoidEnd
import TwoAxisHelicoid.CertifiedGlobalImmersion

namespace TwoAxisHelicoid
open Complex Real Set Filter Bornology
open scoped Topology ContDiff

/-- The full single-sheeted C¹ asymptotic statement, including an actual
compact complement, the projection homeomorphism, and decay in the
induced helicoid metric. -/
def HasHelicoidC1End {M : Type*} [TopologicalSpace M] (Y : M → HelicoidTubeCoordinates) : Prop :=
  ∃ C : Set M, IsCompact C ∧ ∃ R : ℝ, 0 < R ∧
    IsCompact (helicoidProjectedEnd Y C (exteriorPlaneBase R))ᶜ ∧
    ∃ E : helicoidProjectedEnd Y C (exteriorPlaneBase R) ≃ₜ exteriorPlaneBase R,
      (E : helicoidProjectedEnd Y C (exteriorPlaneBase R) → exteriorPlaneBase R) =
        helicoidEndProjection Y C (exteriorPlaneBase R) ∧
      ∃ u : exteriorPlaneBase R → ℝ,
        ContDiffOn ℝ (∞ : WithTop ℕ∞) (extendOpenScalar u) (exteriorPlaneBase R) ∧
        (∀ b, |u b| ≤ 1/2 ∧ Y (E.symm b).1 = helicoidTubeMap ((u b,b.1.1),b.1.2)) ∧
        Tendsto (fun b : exteriorPlaneBase R => |u b|+
          helicoidGraphGradientNorm (extendOpenScalar u) b.1)
          (comap (Subtype.val : exteriorPlaneBase R → ℝ × ℝ) (cobounded (ℝ × ℝ))) (𝓝 0)

noncomputable def certifiedNormalizedTorusImmersion : PuncturedPeriodTorus certifiedPeriodPair → Fin 3 → ℝ :=
  fun q => axisNormalizedTorusPrimitive certifiedPeriodPair (2*(certifiedClosedParameters.a-1)/1)
    (actualGlobalImmersion certifiedClosedParameters.t certifiedClosedParameters.a 1
      certifiedClosedParameters.height_pos)
    (actualGlobalImmersion_add_lattice certifiedClosedParameters.height_pos
      certifiedClosedParameters.abscissa_mem (by norm_num : (1 : ℝ) ≠ 0)
      certifiedClosedParameters.vertical_closed certifiedClosedParameters.horizontal_closed) q.1

/-- Unconditional certified existence of the actual C¹ helicoidal end:
the closed parameters come from the exact period certificate. The spatial
normalization is the fixed similarity from `axisSpatialNormalization`. -/
theorem certifiedTorusImmersion_C1_helicoid_end :
    HasHelicoidC1End (coordinateToTube ∘ certifiedNormalizedTorusImmersion) := by
  let p := certifiedClosedParameters
  have hX : HasTwoAxisHelicoidCoordinateDifferential (actualGlobalImmersion p.t p.a 1 p.height_pos)
      p.t p.a 1 p.height_pos := fun z hz =>
    ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem
      (by norm_num : (1 : ℝ) ≠ 0) p.vertical_closed p.horizontal_closed).2.2.2 z hz).1
  exact actual_periodic_primitive_torus_C1_helicoid_end p.height_pos p.abscissa_mem
    (by norm_num : (1 : ℝ) ≠ 0) hX (actualGlobalImmersion_add_lattice p.height_pos p.abscissa_mem
      (by norm_num : (1 : ℝ) ≠ 0) p.vertical_closed p.horizontal_closed)

theorem certifiedNormalizedTorusImmersion_eq_fixed_similarity
    (hα : 2*(certifiedClosedParameters.a-1)/1 ≠ 0) (q : PuncturedPeriodTorus certifiedPeriodPair) :
    certifiedNormalizedTorusImmersion q =
      axisSpatialNormalization hα
        (actualGlobalImmersion certifiedClosedParameters.t certifiedClosedParameters.a 1
          certifiedClosedParameters.height_pos 1)
        (actualTorusImmersion certifiedClosedParameters.height_pos certifiedClosedParameters.abscissa_mem
          (by norm_num : (1 : ℝ) ≠ 0) certifiedClosedParameters.vertical_closed
          certifiedClosedParameters.horizontal_closed q.1) := by
  exact (axisSpatialNormalization_apply hα _ _).symm

theorem certified_normalization_scale_ne_zero : 2*(certifiedClosedParameters.a-1)/1 ≠ 0 :=
  div_ne_zero (mul_ne_zero (by norm_num)
    (sub_ne_zero.mpr (ne_of_lt certifiedClosedParameters.abscissa_mem.2))) one_ne_zero

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.certifiedTorusImmersion_C1_helicoid_end
