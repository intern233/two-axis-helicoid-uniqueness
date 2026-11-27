import TwoAxisHelicoid.UnmarkedHelicoidGraphDifferential
import TwoAxisHelicoid.MinimalHelicoidHeightGraphUpgrade

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology
open scoped Topology ContDiff Manifold
universe v

/-- With arbitrary placement and signed pitch, decay in height on a single
graph gives the C¹ end. Properness of the original embedding is derived
from the one-ended topology. -/
theorem placed_minimal_height_graph_C1 {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M] [NoncompactSpace M] (tail : HasConnectedCompactTails M)
    (X : M → Fin 3 → ℝ) (emb : IsEmbedding X) (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (imm : ∀ q, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X q))
    (minimal : ∀ q, coordinateMeanCurvature (X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q)=0)
    (F : HelicoidSpatialFrame) {α : ℝ} (ha : α≠0)
    (height : HasHelicoidHeightEnd (coordinateToTube ∘ axisSpatialNormalization ha ![0,0,0] ∘ F.homeo ∘ X)) :
    HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization ha ![0,0,0] ∘ F.homeo ∘ X) := by
  have zero : (![0,0,0] : Fin 3 → ℝ)=0 := by ext i; fin_cases i <;> rfl
  rw [zero] at height ⊢
  let R := centeredHelicoidNormalization ha
  let Y := R ∘ F.homeo ∘ X
  have cy : Continuous Y := R.continuous.comp (F.homeo.continuous.comp emb.continuous)
  have proper := height.proper_of_one_end (coordinateTubeHomeomorph.continuous.comp cy) tail
  have cancel : coordinateTubeHomeomorph.symm ∘ (coordinateToTube ∘ Y)=Y :=
    funext fun q => coordinateTubeHomeomorph.symm_apply_apply _
  have py : IsProperMap Y := cancel ▸ coordinateTubeHomeomorph.symm.isClosedEmbedding.isProperMap.comp proper
  have ey := IsClosedEmbedding.of_continuous_injective_isClosedMap cy
    (R.injective.comp (F.homeo.injective.comp emb.injective)) py.isClosedMap
  have metric (a b : Fin 3 → ℝ) : R a ⬝ᵥ R b=α^2*(a ⬝ᵥ b) := by
    change axisSpatialNormalization ha 0 a ⬝ᵥ axisSpatialNormalization ha 0 b=_
    simp only [axisSpatialNormalization_apply,map_zero,sub_zero,verticalRotation_preserves_dot (c:=I) (by simp),
      smul_dotProduct,dotProduct_smul,smul_eq_mul]
    ring
  have cf (w : Fin 3 → ℝ) : HasFDerivAt F.homeo F.linear.toContinuousLinearMap w :=
    F.linear.toContinuousLinearMap.hasFDerivAt.const_add F.offset
  have sf : ContDiff ℝ ∞ F.homeo := contDiff_const.add F.linear.contDiff
  have connectedTail (K : Set M) (hk : IsCompact K) :
      ∃ U : Set M, IsConnected U ∧ IsCompact Uᶜ ∧ Disjoint U K := by
    obtain ⟨U,hU,hc,dis⟩ := tail K hk
    have nonempty : U.Nonempty := by
      by_contra h
      have empty : U=∅ := Set.not_nonempty_iff_eq_empty.mp h
      exact noncompact_univ M (by simpa [empty] using hc)
    exact ⟨U,⟨nonempty,hU⟩,hc,dis⟩
  apply minimal_helicoid_height_graph_is_C1 Y ey _ _ connectedTail height
  · intro q z hz
    obtain ⟨s,i⟩ := smooth_surface_regular_manifold_chart sm imm q z hz
    have d := (R.toContinuousLinearMap.hasFDerivAt.comp z ((cf _).comp z
      (s.differentiableAt (by simp)).hasFDerivAt)).fderiv
    refine ⟨R.contDiff.contDiffAt.comp z (sf.contDiffAt.comp z s),?_⟩
    change Function.Injective (fderiv ℝ (R.toContinuousLinearMap ∘ (F.homeo ∘ (X ∘ (chartAt ℂ q).symm))) z)
    rw [d]
    exact R.injective.comp (F.linear.injective.comp i)
  · intro q
    exact coordinate_minimal_linear_similarity R metric
      (coordinate_minimal_orthogonal_affine F.linear F.orthogonal F.offset (minimal q))

/-- For arbitrary orientable finite genus a single normal graph with only
height decay yields the actual conformal compactification and Bernstein–
Breiner differential in the original specified spatial frame. -/
theorem unmarked_height_graph_gives_finite_end_differential {M : Type} {N : Type v}
    [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M]
    [TopologicalSpace N] [T2Space N] [CompactSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ,ℂ) ω N]
    (p : N) (top : M ≃ₜ {q : N // q≠p}) (X : M → Fin 3 → ℝ) (emb : IsEmbedding X)
    (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (imm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x))
    (min : ∀ x, coordinateMeanCurvature (X ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)=0)
    (F : HelicoidSpatialFrame) {α : ℝ} (ha : α≠0)
    (height : HasHelicoidHeightEnd (coordinateToTube ∘ axisSpatialNormalization ha ![0,0,0] ∘ F.homeo ∘ X)) :
    IsClosedEmbedding X ∧ Nonempty (PublishedConformalPoleModel X) ∧
      ∃ S : ChartedSpace ℂ M, let _ := S
        IsManifold 𝓘(ℂ,ℂ) ω M ∧ (∀ e∈atlas ℂ M, InducedIsothermalChart X e ∧ HarmonicImmersionChart X e) ∧
        ∃ A : GeometricExteriorInSomeFrame X, A.frame=F.linear.toLinearEquiv ∧ A.offset=F.offset ∧
          A.pitch=α ∧ A.exterior.pitch=α ∧ A.exterior.correction 0=0 ∧ Nonempty (FiniteTopologyExteriorDifferential (F.homeo ∘ X)) := by
  let _ := punctured_complex_curve_noncompact p
  let _ : NoncompactSpace M := ⟨fun h => noncompact_univ {q : N // q≠p} (by
    simpa only [image_univ,top.surjective.range_eq] using h.image top.continuous)⟩
  exact unmarked_graph_gives_finite_end_differential p top X emb sm imm min F ha
    (placed_minimal_height_graph_C1 (homeomorphic_punctured_surface_connected_tails p top) X emb sm imm min F ha height)
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.unmarked_height_graph_gives_finite_end_differential
