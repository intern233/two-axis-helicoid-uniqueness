import TwoAxisHelicoid.SurfaceProjectedSegments
import TwoAxisHelicoid.OneEndThinGraph
import TwoAxisHelicoid.CoordinateTubeHomeomorph

namespace TwoAxisHelicoid
open Real Set Filter Bornology Topology
open scoped Topology ContDiff

/-- Lemma 4.3. For an arbitrary closed embedded smooth regular surface
with one end and uniformly bounded second fundamental form off a compact
set, containment of the end in arbitrarily thin helicoid tubes gives
one smooth normal graph with height and gradient tending to zero. -/
theorem general_one_end_thin_C1_graph_of_bounded_weingarten
    {M : Type*} [TopologicalSpace M] [T2Space M]
    (F : M → Fin 3 → ℝ) (hF : IsClosedEmbedding F)
    (tail : ∀ K : Set M, IsCompact K → ∃ U : Set M, IsConnected U ∧ IsCompact Uᶜ ∧ Disjoint U K)
    (e : M → OpenPartialHomeomorph M ℂ) (he : ∀ q, q ∈ (e q).source)
    (hr : ∀ q, RegularImmersionChart F (e q)) {K₀ : Set M} (hK : IsCompact K₀)
    {B : ℝ} (hB : 0 ≤ B) (hII : HasBoundedSurfaceWeingarten F e K₀ B)
    (hthin : ∀ ε : ℝ, 0 < ε → ∃ K : Set M, IsCompact K ∧
      ∀ q ∉ K, coordinateToTube (F q) ∈ helicoidTubeEquiv.target ∧
        |helicoidSignedDistance (coordinateToTube (F q))| ≤ ε) :
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
  let c := fun q => complexChartAsReal (e q)
  let X := coordinateToTube ∘ F
  have hp := coordinateToTube_isProperMap hF.isProperMap
  have hs (q : M) := (hr q _ ((e q).map_source (he q))).1
  have hd (q : M) := complex_chart_real_differential (e q)
    ((hs q).differentiableAt (by simp)).hasFDerivAt
  have hsm (q : M) : ContDiffAt ℝ (∞ : WithTop ℕ∞) (X ∘ (c q).symm) (c q q) := by
    let y := Complex.equivRealProdCLM (e q q)
    have hback : Complex.equivRealProdCLM.symm y = e q q := Complex.equivRealProdCLM.symm_apply_apply _
    have hparam : ContDiffAt ℝ (∞ : WithTop ℕ∞) (coordinateToTube ∘ (F ∘ (e q).symm)) (e q q) :=
      coordinateToTube.contDiff.contDiffAt.comp (e q q) (hs q)
    have hparam' : ContDiffAt ℝ (∞ : WithTop ℕ∞) (coordinateToTube ∘ (F ∘ (e q).symm))
        (Complex.equivRealProdCLM.symm y) := hback.symm ▸ hparam
    exact hparam'.comp y Complex.equivRealProdCLM.symm.contDiff.contDiffAt
  have hinj (q : M) : Function.Injective (fderiv ℝ (X ∘ (c q).symm) (c q q)) := by
    rw [(hd q).fderiv]
    exact (coordinateToTube_injective.comp (hr q _ ((e q).map_source (he q))).2).comp Complex.equivRealProdCLM.symm.injective
  apply one_end_thin_C1_graph tail hp (coordinateToTube_injective.comp hF.injective).injOn hK c
    (fun q _ => he q) (fun q _ => hsm q) (fun q _ => hinj q) hthin (show 0 ≤ 2*B by positivity)
  intro ε hε hsmall
  obtain ⟨L,hL,hcurve⟩ := unit_tangent_segments_controlled_on_thin_tails hp hK
    (actual_surface_unit_tangent_segments F hF e he hr hB hII) hthin ε hε hsmall
  refine ⟨L,hL,?_⟩
  intro q hq
  rw [(hd q).fderiv]
  exact (hcurve q hq).precomp Complex.equivRealProdCLM.symm.toContinuousLinearMap

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.general_one_end_thin_C1_graph_of_bounded_weingarten
