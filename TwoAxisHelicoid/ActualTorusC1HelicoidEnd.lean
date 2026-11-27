import TwoAxisHelicoid.ActualTorusHeightChart
import TwoAxisHelicoid.AnalyticEmbeddedEndC1Graph
import TwoAxisHelicoid.PeriodTorusComplexManifold

namespace TwoAxisHelicoid
open Complex Real Set Filter Bornology Topology
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

/-- The actual closed explicit immersion, after the fixed Euclidean
similarity already verified, has a smooth single-sheeted helicoidal
normal graph outside a compact set, with both graph height and gradient
tending to zero. Thinness, end injectivity, chart regularity, and unit
tangent curves are derived from the actual coordinate differential. -/
theorem actual_periodic_primitive_torus_C1_helicoid_end
    {X : ℂ → Fin 3 → ℝ} {t a c : ℝ}
    (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (hp : ∀ z ω₀ : ℂ, ω₀ ∈ (rhombicPeriodPair t ht).lattice → X (z+ω₀) = X z) :
    let Y : PuncturedPeriodTorus (rhombicPeriodPair t ht) → HelicoidTubeCoordinates :=
      fun q => coordinateToTube
        (axisNormalizedTorusPrimitive (rhombicPeriodPair t ht) (2*(a-1)/c) X hp q.1)
    ∃ C : Set (PuncturedPeriodTorus (rhombicPeriodPair t ht)), IsCompact C ∧ ∃ R : ℝ, 0 < R ∧
      IsCompact (helicoidProjectedEnd Y C (exteriorPlaneBase R))ᶜ ∧
      ∃ E : helicoidProjectedEnd Y C (exteriorPlaneBase R) ≃ₜ exteriorPlaneBase R,
        (E : helicoidProjectedEnd Y C (exteriorPlaneBase R) → exteriorPlaneBase R) =
          helicoidEndProjection Y C (exteriorPlaneBase R) ∧
        ∃ u : exteriorPlaneBase R → ℝ,
          ContDiffOn ℝ (∞ : WithTop ℕ∞) (extendOpenScalar u) (exteriorPlaneBase R) ∧
          (∀ b, |u b| ≤ 1/2 ∧ Y (E.symm b).1 = helicoidTubeMap ((u b,b.1.1),b.1.2)) ∧
          Tendsto (fun b : exteriorPlaneBase R => |u b|+
            helicoidGraphGradientNorm (extendOpenScalar u) b.1)
            (comap (Subtype.val : exteriorPlaneBase R → ℝ × ℝ) (cobounded (ℝ × ℝ))) (𝓝 0) := by
  let L := rhombicPeriodPair t ht
  let := periodTorus_compactSpace L
  let := periodTorus_t2Space L
  have hα : 2*(a-1)/c ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (ne_of_lt ha.2))) hc
  obtain ⟨e,f,R,hf,htail,hD,hthin⟩ := actual_periodic_primitive_torus_analytic_thin_chart ht ha hc hX hp
  obtain ⟨hproper,C,hC,hinj⟩ := axisNormalizedTorusPrimitive_proper_and_end_injective ht ha hc hα hX hp
  apply analytic_embedded_height_end_C1_normal_graph (0 : PeriodTorus L)
    hproper hC hinj e htail 1 R hf
  · intro ξ hξ
    simpa only [Complex.ofReal_one,mul_one,Function.comp_def] using hD ξ hξ
  · exact hthin

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_periodic_primitive_torus_C1_helicoid_end
