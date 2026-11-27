import TwoAxisHelicoid.GeneralThinTubeLemma
import TwoAxisHelicoid.ChartSecondFundamentalWeingarten

namespace TwoAxisHelicoid
open Set Real Filter Bornology Topology
open scoped Topology ContDiff Manifold

/-- TwoAxisHelicoid Lemma 4.3 from an actual ambient-Hessian second fundamental form
bound off a compact set, measured in the induced metric. -/
theorem general_thin_tube_lemma_4_3_second_fundamental
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M]
    (F : M → Fin 3 → ℝ) (hp : IsProperMap F) (hinj : Function.Injective F)
    (hs : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F)
    (hi : ∀ q, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q))
    (tail : ∀ K : Set M, IsCompact K → ∃ U : Set M, IsConnected U ∧ IsCompact Uᶜ ∧ Disjoint U K)
    {K₀ : Set M} (hK : IsCompact K₀) {B : ℝ} (hB : 0 ≤ B)
    (hII : ∀ q ∉ K₀, ∀ v w : ℂ,
      |chartScalarSecondFundamentalForm (F ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q) v w| ≤
        B * ‖coordinateToEuclidean (fderiv ℝ (F ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q) v)‖ *
          ‖coordinateToEuclidean (fderiv ℝ (F ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q) w)‖)
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
  apply general_thin_tube_lemma_4_3 F hp hinj hs hi tail hK hB _ hthin
  intro q hq
  exact (chart_second_fundamental_bound_iff (smooth_surface_regular_manifold_chart hs hi q)
    ((chartAt ℂ q).map_source (mem_chart_source ℂ q)) hB).mp (hII q hq)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.general_thin_tube_lemma_4_3_second_fundamental
