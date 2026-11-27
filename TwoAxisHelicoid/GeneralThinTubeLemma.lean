import TwoAxisHelicoid.GeneralOneEndThinTube
import TwoAxisHelicoid.EuclideanUnitChartNormal

namespace TwoAxisHelicoid
open Set Real Filter Bornology Topology
open scoped Topology ContDiff Manifold

/-- The manuscript's thin-tube lemma on an arbitrary smooth real surface.
The only curvature hypothesis bounds the ordinary shape operator of the actual
surface off a compact set, calculated from its coordinate tangent vectors. A
co-compact subend is contained in each geometric helicoid normal tube. -/
theorem general_thin_tube_lemma_4_3
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M]
    (F : M → Fin 3 → ℝ) (hp : IsProperMap F) (hinj : Function.Injective F)
    (hs : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F)
    (hi : ∀ q, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q))
    (tail : ∀ K : Set M, IsCompact K → ∃ U : Set M, IsConnected U ∧ IsCompact Uᶜ ∧ Disjoint U K)
    {K₀ : Set M} (hK : IsCompact K₀) {B : ℝ} (hB : 0 ≤ B)
    (hcurvature : ∀ q ∉ K₀, ∀ v : ℂ,
      ‖fderiv ℝ (euclideanUnitChartNormal (F ∘ (chartAt ℂ q).symm)) ((chartAt ℂ q) q) v‖ ≤
        B * ‖coordinateToEuclidean (fderiv ℝ (F ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q) v)‖)
    (hthin : ∀ ε : ℝ, 0 < ε → ∃ U : Set M, IsCompact Uᶜ ∧
      ∀ q ∈ U, ∃ s r θ : ℝ, |s| < ε ∧ coordinateToTube (F q) = helicoidTubeMap ((s,r),θ)) :
    ∃ K : Set M, IsCompact K ∧ ∃ R : ℝ, 0 < R ∧
      IsCompact (helicoidProjectedEnd (coordinateToTube ∘ F) K (exteriorPlaneBase R))ᶜ ∧
      ∃ e : helicoidProjectedEnd (coordinateToTube ∘ F) K (exteriorPlaneBase R) ≃ₜ exteriorPlaneBase R,
        (e : helicoidProjectedEnd (coordinateToTube ∘ F) K (exteriorPlaneBase R) → exteriorPlaneBase R) =
          helicoidEndProjection (coordinateToTube ∘ F) K (exteriorPlaneBase R) ∧
        ∃ u : exteriorPlaneBase R → ℝ,
          ContDiffOn ℝ (∞ : WithTop ℕ∞) (extendOpenScalar u) (exteriorPlaneBase R) ∧
          (∀ b, |u b| ≤ 1/2 ∧ (coordinateToTube ∘ F) (e.symm b).1 = helicoidTubeMap ((u b,b.1.1),b.1.2)) ∧
          Tendsto (fun b : exteriorPlaneBase R => |u b|+
            helicoidGraphGradientNorm (extendOpenScalar u) b.1)
            (comap (Subtype.val : exteriorPlaneBase R → ℝ × ℝ) (cobounded (ℝ × ℝ))) (𝓝 0) := by
  have hF : IsClosedEmbedding F := .of_continuous_injective_isClosedMap hp.continuous hinj hp.isClosedMap
  have hr := smooth_surface_regular_manifold_chart hs hi
  apply general_one_end_thin_C1_graph_of_bounded_weingarten F hF tail (chartAt ℂ)
    (mem_chart_source ℂ) hr hK hB (bounded_surface_weingarten_of_cross (mem_chart_source ℂ) hr hcurvature)
  intro ε hε
  obtain ⟨U,hU,hsub⟩ := hthin (min ε 1) (lt_min hε zero_lt_one)
  refine ⟨Uᶜ,hU,?_⟩
  intro q hq
  obtain ⟨s,r,θ,hs,heq⟩ := hsub q (not_not.mp hq)
  have hstrip : ((s,r),θ) ∈ helicoidTubeStrip := hs.trans_le (min_le_right _ _)
  rw [heq, helicoidSignedDistance_on_normal hstrip]
  exact ⟨helicoidTubeEquiv.map_source hstrip,hs.le.trans (min_le_left _ _)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.general_thin_tube_lemma_4_3
