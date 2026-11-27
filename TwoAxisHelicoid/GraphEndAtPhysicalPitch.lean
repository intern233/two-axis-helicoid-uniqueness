import TwoAxisHelicoid.GeometricGraphEndProposition
import TwoAxisHelicoid.GeometricExteriorSimilarity
import TwoAxisHelicoid.OriginalGraphExteriorNormalization
import TwoAxisHelicoid.ExteriorHeightGaussPoles

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology ContDiff Manifold
universe u

/-- Inverting a true height chart gives a puncture of the same surface.
Both double poles and the regular differential in that chart are obtained
by differentiating the physical height and the measured Gauss map. -/
theorem GeometricExteriorCoordinate.measured_puncture {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [NoncompactSpace M]
    {X : M → Fin 3 → ℝ} (D : GeometricExteriorCoordinate X) (cx : Continuous X)
    (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e) (tails : HasConnectedCompactTails M) :
    ∃ A : GeometricDoublePoleEnd X,
      (let _ := compactifiedEndAtlas A.endChart
       IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) ∧
         ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some : M → OnePoint M)) ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), immersionGaussLogDerivative (X ∘ A.endChart.coord.symm) z-
        I*(D.pitch:ℂ)*immersionComplexCoefficient (X ∘ A.endChart.coord.symm) z 2=deriv D.correction z := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℂ M
  have esc := true_exterior_height_coordinate_escapes tails D.chart D.target D.core _
    ((continuous_apply 2).comp cx) D.heightOffset D.height
  let E := exteriorCoordinateComplexEnd D.chart D.positive D.target D.core esc
  let Y := X ∘ D.chart.symm
  let Z := X ∘ E.coord.symm
  let k := I*(D.pitch:ℂ)
  have reg := exterior_immersion_eventually_differentiable X charts D.holomorphic D.target
  have height : ∀ᶠ w in cobounded ℂ, Y w 2=D.heightOffset+w.re := by
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop D.radius] with w hw
    have hit : w∈D.chart.target := D.target ▸ hw
    exact (D.height _ (D.chart.map_target hit)).trans (congrArg (fun z : ℂ => D.heightOffset+z.re) (D.chart.right_inv hit))
  obtain ⟨h,ho,g,go⟩ := actual_exterior_height_gauss_poles Y D.heightOffset D.pitch D.pitch_ne
    D.correction D.analytic reg height D.gauss
  let A : GeometricDoublePoleEnd X := ⟨E,reciprocalExteriorChart_mem_maximalAtlas D.chart D.positive D.target D.holomorphic,h,ho,g,go⟩
  refine ⟨A,exteriorCoordinate_fills_complex_manifold D.chart D.positive D.target D.core esc D.holomorphic,?_⟩
  have hh : (fun z => Z z 2) =ᶠ[𝓝[≠] (0:ℂ)] fun z => D.heightOffset+z⁻¹.re :=
    tendsto_inv₀_nhdsNE_zero.eventually height
  have gg : immersionGaussMap Z =ᶠ[𝓝[≠] (0:ℂ)] fun z => exp (k/z+D.correction z) := by
    filter_upwards [tendsto_inv₀_nhdsNE_zero.eventually D.gauss,tendsto_inv₀_nhdsNE_zero.eventually reg,
      self_mem_nhdsWithin] with z dg dr non
    change z≠0 at non
    have changeChart : immersionGaussMap Z z=immersionGaussMap Y z⁻¹ :=
      immersionGaussMap_comp_holomorphic dr (hasDerivAt_inv non) (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ non)))
    rw [changeChart,dg,inv_inv,div_eq_mul_inv]
  filter_upwards [punctured_germ_eventually_local hh,punctured_germ_eventually_local gg,
    D.analytic.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with z hloc gloc fa nz
  change z≠0 at nz
  have di : HasDerivAt (fun w : ℂ => w⁻¹) ((-1:ℂ)/z^2) z := by simpa only [neg_div,one_div] using! hasDerivAt_inv nz
  have hv : immersionComplexCoefficient Z z 2=(-1:ℂ)/z^2 := by
    change scalarComplexCoefficient (fun w => Z w 2) z=_
    have same : scalarComplexCoefficient (fun w => Z w 2) z=scalarComplexCoefficient (fun w : ℂ => D.heightOffset+w⁻¹.re) z := by
      unfold scalarComplexCoefficient
      rw [hloc.fderiv_eq]
    exact same.trans (scalarComplexCoefficient_of_real_part di D.heightOffset)
  have dz : HasDerivAt (fun w : ℂ => k/w) ((-k)/z^2) z := by
    simpa only [zero_mul,mul_one,zero_sub,id_eq,Pi.div_def] using! (hasDerivAt_const z k).div (hasDerivAt_id z) nz
  have de := (dz.add fa.differentiableAt.hasDerivAt).cexp.deriv
  dsimp only [Pi.add_def] at de
  change immersionGaussLogDerivative Z z-k*immersionComplexCoefficient Z z 2=_
  rw [hv,immersionGaussLogDerivative,gloc.deriv_eq,gloc.self_of_nhds,de]
  field_simp [exp_ne_zero,nz]
  ring

/-- Undo the signed pitch normalization on the original spatial immersion.
One-endedness throughout this argument is supplied by the constructed
puncture chart, for any genus. -/
theorem graph_end_at_physical_pitch {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [NoncompactSpace M]
    (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e) {α : ℝ} (nonzero : α≠0)
    (graph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization nonzero ![0,0,0] ∘ X)) :
    ∃ D : GeometricExteriorCoordinate X, D.pitch=α ∧ D.correction 0=0 ∧
      ∃ A : GeometricDoublePoleEnd X,
        (let _ := compactifiedEndAtlas A.endChart
         IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) ∧
           ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some : M → OnePoint M)) ∧
        ∀ᶠ z in 𝓝[≠] (0:ℂ), immersionGaussLogDerivative (X ∘ A.endChart.coord.symm) z-
          I*(α:ℂ)*immersionComplexCoefficient (X ∘ A.endChart.coord.symm) z 2=deriv D.correction z := by
  let R := axisSpatialNormalization nonzero ![0,0,0]
  let Y := R ∘ X
  have cy : ∀ e∈atlas ℂ M, HarmonicImmersionChart Y e := fun e he z hz =>
    reference_frame_harmonic_chart (charts e he z hz).1 (charts e he z hz).2.1 (charts e he z hz).2.2 nonzero
  obtain ⟨E,_,_,G,pitch,_⟩ := harmonic_graph_end_proposition Y (R.isClosedEmbedding.comp closed) cy graph
  have oneEnd := E.endChart.connected_tails
  obtain ⟨B,bp,_⟩ := G.scaled (exterior_immersion_eventually_differentiable Y cy G.holomorphic G.target) (inv_ne_zero nonzero)
  let W := fun x => α⁻¹ • Y x
  have cw : ∀ e∈atlas ℂ M, HarmonicImmersionChart W e := fun e he z hz =>
    scalar_harmonic_conformal_chart (cy e he z hz).1 (cy e he z hz).2.1 (cy e he z hz).2.2 (inv_ne_zero nonzero)
  obtain ⟨C,cp⟩ := B.rotated (exterior_immersion_eventually_differentiable W cw B.holomorphic B.target) (q:=-1) (by simp)
  have eq : verticalRotation (-1) ∘ W=X := by
    funext x
    change verticalRotation (-1) (α⁻¹ • axisSpatialNormalization nonzero ![0,0,0] (X x))=X x
    have zero : (![0,0,0] : Fin 3 → ℝ)=0 := by ext j; fin_cases j <;> rfl
    rw [zero,axisSpatialNormalization_apply,map_zero,sub_zero]
    simp only [map_smul,inv_smul_smul₀ nonzero]
    ext j
    fin_cases j <;> simp [verticalRotation_apply]
  have cpitch : C.pitch=α := by rw [cp,bp,pitch,div_inv_eq_mul,one_mul]
  obtain ⟨C',c'p⟩ : ∃ C' : GeometricExteriorCoordinate X, C'.pitch=α := eq ▸ (show ∃ V : GeometricExteriorCoordinate (verticalRotation (-1) ∘ W), V.pitch=α from ⟨C,cpitch⟩)
  obtain ⟨D,dp,d0⟩ := C'.normalized closed.continuous oneEnd
  have dα := dp.trans c'p
  obtain ⟨A,compactified,remaining⟩ := D.measured_puncture closed.continuous charts oneEnd
  exact ⟨D,dα,d0,A,compactified,by simpa only [dα] using remaining⟩

/-- Starting with the physical smooth minimal surface and a signed-pitch
graph at infinity, construct its complex structure and both measured
end differentials in the same puncture chart. -/
theorem oriented_graph_end_at_physical_pitch {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M] [NoncompactSpace M]
    (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (smooth : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (immersion : ∀ q, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X q))
    (orientation : PositiveSurfaceAtlas M)
    (minimal : ∀ q, coordinateMeanCurvature (X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q)=0)
    {α : ℝ} (nonzero : α≠0)
    (graph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization nonzero ![0,0,0] ∘ X)) :
    ∃ S : ChartedSpace ℂ M, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω M ∧ (∀ e∈atlas ℂ M, HarmonicImmersionChart X e) ∧
      ∃ D : GeometricExteriorCoordinate X, D.pitch=α ∧ D.correction 0=0 ∧
        ∃ A : GeometricDoublePoleEnd X,
          (let _ := compactifiedEndAtlas A.endChart
           IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) ∧
             ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some : M → OnePoint M)) ∧
          ∀ᶠ z in 𝓝[≠] (0:ℂ), immersionGaussLogDerivative (X ∘ A.endChart.coord.symm) z-
            I*(α:ℂ)*immersionComplexCoefficient (X ∘ A.endChart.coord.symm) z 2=deriv D.correction z := by
  obtain ⟨S,man,charts⟩ := oriented_minimal_induced_harmonic_atlas smooth immersion orientation minimal
  let _ := S
  let _ := man
  exact ⟨S,man,charts,graph_end_at_physical_pitch X closed charts nonzero graph⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.oriented_graph_end_at_physical_pitch
#print axioms TwoAxisHelicoid.GeometricExteriorCoordinate.measured_puncture
#print axioms TwoAxisHelicoid.graph_end_at_physical_pitch

