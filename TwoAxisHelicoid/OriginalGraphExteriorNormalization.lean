import TwoAxisHelicoid.PhysicalOneHandleExterior
import TwoAxisHelicoid.GeometricExteriorSimilarity
import TwoAxisHelicoid.OriginalGraphPoleModel
import TwoAxisHelicoid.ReferenceFrameHarmonic

namespace TwoAxisHelicoid
open Complex Set Filter Topology Bornology
open scoped Topology ContDiff Manifold

universe u

/-- Undo the spatial change of frame on a given genuine exterior
coordinate and select its additive and phase constants. -/
theorem physical_exterior_back_in_original_frame {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X) (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    {α : ℝ} (a : α≠0) (A : GeometricExteriorCoordinate (axisSpatialNormalization a ![0,0,0] ∘ X)) :
    ∃ C : GeometricExteriorCoordinate X, C.correction 0=0 := by
  let R := axisSpatialNormalization a ![0,0,0]
  let Y := R ∘ X
  have cy : ∀ e∈atlas ℂ M, HarmonicImmersionChart Y e :=
    fun e he z hz => reference_frame_harmonic_chart (charts e he z hz).1 (charts e he z hz).2.1 (charts e he z hz).2.2 a
  obtain ⟨B,_,_⟩ := A.scaled (exterior_immersion_eventually_differentiable Y cy A.holomorphic A.target) (inv_ne_zero a)
  let W := fun x => α⁻¹ • Y x
  have cw : ∀ e∈atlas ℂ M, HarmonicImmersionChart W e := fun e he z hz =>
    scalar_harmonic_conformal_chart (cy e he z hz).1 (cy e he z hz).2.1 (cy e he z hz).2.2 (inv_ne_zero a)
  obtain ⟨D,_⟩ := B.rotated (exterior_immersion_eventually_differentiable W cw B.holomorphic B.target) (q := -1) (by simp)
  have hzero : (![0,0,0] : Fin 3 → ℝ)=0 := by ext j; fin_cases j <;> rfl
  have eq : verticalRotation (-1) ∘ W=X := by
    funext x
    change verticalRotation (-1) (α⁻¹ • axisSpatialNormalization a ![0,0,0] (X x))=X x
    rw [hzero,axisSpatialNormalization_apply,map_zero,sub_zero]
    simp only [map_smul,inv_smul_smul₀ a]
    ext j
    fin_cases j <;> simp [verticalRotation_apply]
  obtain ⟨G,_,g⟩ := (eq ▸ D : GeometricExteriorCoordinate X).normalized closed.continuous
    (homeomorphic_punctured_surface_connected_tails (0:PeriodTorus L₀) top)
  exact ⟨G,g⟩

/-- The exterior chart and the convergent Gauss correction in the
physical coordinates of a surface of any nonzero helicoidal pitch.
The surface need not contain a straight line. -/
theorem one_handle_original_frame_exterior {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (uni : SimplyConnectedNoncompactUniformization.{u}) (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e) {α : ℝ} (a : α≠0)
    (graph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization a ![0,0,0] ∘ X)) :
    ∃ A : GeometricExteriorCoordinate X, A.correction 0=0 := by
  let R := axisSpatialNormalization a ![0,0,0]
  let Y := R ∘ X
  have cy : ∀ e∈atlas ℂ M, HarmonicImmersionChart Y e :=
    fun e he z hz => reference_frame_harmonic_chart (charts e he z hz).1 (charts e he z hz).2.1 (charts e he z hz).2.2 a
  obtain ⟨A⟩ := original_one_handle_physical_exterior top uni Y (R.isClosedEmbedding.comp closed) cy graph
  exact physical_exterior_back_in_original_frame top X closed charts a A

/-- The manuscript's normalized exterior form, on the original real
surface with its induced isothermal atlas. -/
theorem original_graph_normalized_exterior (s : OriginalHelicoidRepresentative) (uni : SimplyConnectedNoncompactUniformization.{0}) :
    ∃ S : ChartedSpace ℂ s.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧ (∀ e∈atlas ℂ s.carrier, HarmonicImmersionChart s.position e) ∧
      ∃ A : GeometricExteriorCoordinate s.position, A.correction 0=0 := by
  obtain ⟨S,man,charts⟩ := punctured_torus_minimal_induced_harmonic_atlas s.topologicalType s.smooth s.immersion s.minimal
  let _ := S
  let _ := man
  exact ⟨S,man,charts,one_handle_original_frame_exterior s.topologicalType uni s.position s.closedEmbedding charts s.axes.pitch_ne s.graphEnd⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.one_handle_original_frame_exterior
#print axioms TwoAxisHelicoid.original_graph_normalized_exterior
