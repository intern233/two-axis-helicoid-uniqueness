import TwoAxisHelicoid.OrientedMinimalHarmonicAtlas
import TwoAxisHelicoid.SimilarityNormalTangency
import TwoAxisHelicoid.TangentOrbitInvariance
import TwoAxisHelicoid.SimilarityFlowMetric

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology InnerProductSpace
open scoped Topology ContDiff

/-- A similarity velocity with vanishing normal component in an atlas
preserves the entire closed spatial image for every finite flow time. -/
theorem harmonic_atlas_tangent_flow_preserves {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (X N : M → Fin 3 → ℝ) (closed : IsClosed (range X))
    (charts : ∀ e ∈ atlas ℂ M, HarmonicImmersionChart X e)
    (normal : ∀ e ∈ atlas ℂ M, ∀ z ∈ e.target, N (e.symm z)=harmonicChartNormal (X ∘ e.symm) z)
    (a b : Fin 3 → ℝ) (d : ℝ) (zero : ∀ p, similarityNormal X N a b d p=0) :
    ∀ t : ℝ, MapsTo (affineAmbientFlow (similarityLinear b d) a t) (range X) (range X) := by
  let L := similarityLinear b d
  let V := fun x => a+L x
  have lip : LipschitzWith ‖L‖₊ V := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (a+L x) (a+L y) ≤ _
    rw [dist_add_left]
    exact L.lipschitzWith.dist_le_mul x y
  rintro t _ ⟨p,rfl⟩
  let γ := fun r : ℝ => affineAmbientFlow L a r (X p)
  have der (r : ℝ) : HasDerivAt γ (V (γ r)) r := affineAmbientFlow_deriv L a (X p) r
  let A := γ ⁻¹' range X
  have hc : IsClosed A := closed.preimage (continuous_iff_continuousAt.mpr fun r => (der r).continuousAt)
  have ho : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    rintro s ⟨q,hq⟩
    let e := chartAt ℂ q
    let Y := X ∘ e.symm
    have ep : q ∈ e.source := mem_chart_source ℂ q
    have eh : e ∈ atlas ℂ M := chart_mem_atlas ℂ q
    have reg := charts e eh
    have an (w : ℂ) (hw : w ∈ e.target) : AnalyticAt ℝ Y w :=
      analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt ((reg w hw).1 j)
    have tang (w : ℂ) (hw : w ∈ e.target) : ∃ v, fderiv ℝ Y w v=V (Y w) := by
      have val : similarityNormal Y (harmonicChartNormal Y) a b d w=0 := by
        change similarityField a b d (Y w) ⬝ᵥ harmonicChartNormal Y w=0
        rw [← normal e eh w hw]
        exact zero (e.symm w)
      obtain ⟨v,hv⟩ := similarity_normal_zero_is_tangent (an w hw) (reg _ hw).2.1 (reg _ hw).2.2 a b d val
      exact ⟨v,by simpa only [similarityField,V,L,similarityLinear_apply,add_assoc] using hv⟩
    have reach := tangent_ambient_orbit_locally_in_image e.open_target (e.map_source ep) (an _ (e.map_source ep))
      (reg _ (e.map_source ep)).2.2 (show AnalyticAt ℝ V (Y (e q)) from analyticAt_const.add (L.analyticAt _)) lip tang der
      (show γ s=Y (e q) from hq.symm.trans (congrArg X (e.left_inv ep).symm))
    exact reach.mono (fun r h => by obtain ⟨u,_,val⟩ := h; exact ⟨e.symm u,val⟩)
  have start : (0:ℝ) ∈ A := by
    change affineAmbientFlow L a 0 (X p) ∈ range X
    rw [affineAmbientFlow_zero]
    exact mem_range_self p
  have all := IsClopen.eq_univ ⟨hc,ho⟩ (show A.Nonempty from ⟨0,start⟩)
  exact (show t ∈ A by rw [all]; exact mem_univ _)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_atlas_tangent_flow_preserves
