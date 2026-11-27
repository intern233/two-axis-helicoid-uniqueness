import TwoAxisHelicoid.ChartedSpatialAntiholomorphic
import TwoAxisHelicoid.TorusVerticalSchwarzSymmetry

namespace TwoAxisHelicoid
open Complex Set Filter Topology Metric
open scoped Topology ComplexConjugate ContDiff Manifold

/-- An antiholomorphic map between the given conformal atlases, tested
also in maximal charts such as the distinguished puncture coordinate. -/
def AntiholomorphicInSurfaceCharts {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] (f : M → M) : Prop :=
  ∀ (a b : OpenPartialHomeomorph M ℂ), a∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M →
    b∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M → ∀ x, x∈a.source → f x∈b.source →
    AnalyticAt ℂ (b ∘ f ∘ a.symm ∘ conj) (conj (a x))

/-- The ambient horizontal half turn acts by an antiholomorphic
involution on the original connected embedded Riemann surface. -/
theorem horizontal_schwarz_on_original_surface {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [PreconnectedSpace M] {X : M → Fin 3 → ℝ} (emb : IsClosedEmbedding X)
    (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d)
    (axis : ∀ s : ℝ, (![s,0,0] : Fin 3 → ℝ)∈range X) :
    ∃ f : M ≃ₜ M, AntiholomorphicInSurfaceCharts f ∧ Function.Involutive f ∧ ∀ x, X (f x)=halfTurnX (X x) := by
  obtain ⟨f,space,inv⟩ := charted_closed_surface_horizontal_half_turn emb charts axis
  obtain ⟨p,hp⟩ := axis 0
  have zero : X p=0 := by rw [hp]; ext j; fin_cases j <;> rfl
  have fixed : f p=p := emb.injective <| (space p).trans (by rw [zero]; ext j; fin_cases j <;> simp [halfTurnX])
  let e := chartAt ℂ p
  have ep : p∈e.source := mem_chart_source ℂ p
  have et := e.map_source ep
  have chart := charts e (chart_mem_atlas ℂ p)
  have realA : AnalyticAt ℝ (X ∘ e.symm) (e p) := analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt ((chart _ et).1 j))
  obtain ⟨S,analytic,_,germ⟩ := embedded_axis_local_reflection emb.isEmbedding e ep zero axis realA (chart _ et).2.2
    (by filter_upwards [e.open_target.mem_nhds et] with w hw using ⟨(chart w hw).1,(chart w hw).2.1⟩)
  refine ⟨f,charted_spatial_symmetry_antiholomorphic (p := p) charts halfTurnX_analyticAt f.continuous space ?_,inv,space⟩
  rw [fixed]
  apply analytic.congr
  have c : Tendsto conj (𝓝 (conj (e p))) (𝓝 (e p)) := by simpa using (Complex.continuous_conj.continuousAt (x := conj (e p))).tendsto
  filter_upwards [c.eventually germ] with z h
  simp only [starRingEnd_self_apply] at h
  have eq := emb.injective (h.2.trans (space _).symm)
  change S z=e (f (e.symm (conj z)))
  rw [← eq,e.right_inv h.1]

/-- The vertical half turn satisfies the same intrinsic Schwarz
principle, before choosing a conformal torus model. -/
theorem vertical_schwarz_on_original_surface {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [PreconnectedSpace M] {X : M → Fin 3 → ℝ} (emb : IsClosedEmbedding X)
    (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d)
    (axis : ∀ s : ℝ, (![0,0,s] : Fin 3 → ℝ)∈range X) :
    ∃ f : M ≃ₜ M, AntiholomorphicInSurfaceCharts f ∧ Function.Involutive f ∧ ∀ x, X (f x)=halfTurnZ (X x) := by
  let Z := schwarzSwapXZ ∘ X
  have embedding : IsClosedEmbedding Z := schwarzSwapXZ.toHomeomorph.isClosedEmbedding.comp emb
  have line (s : ℝ) : (![s,0,0] : Fin 3 → ℝ)∈range Z := by
    obtain ⟨q,e⟩ := axis s
    exact ⟨q,congrArg schwarzSwapXZ e⟩
  have reg (e : OpenPartialHomeomorph M ℂ) (he : e∈atlas ℂ M) : HarmonicImmersionChart Z e := by
    intro z hz
    obtain ⟨harm,co,inj⟩ := charts e he z hz
    let Y := X ∘ e.symm
    have sy : AnalyticAt ℝ Y z := analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (harm j))
    refine ⟨?_,conformalCoordinateDerivatives_swapXZ co,?_⟩
    · intro j
      fin_cases j
      · exact harm 2
      · exact harm 1
      · exact harm 0
    · have hd := schwarzSwapXZ.toContinuousLinearMap.hasFDerivAt.comp z sy.differentiableAt.hasFDerivAt
      change Function.Injective (fderiv ℝ (schwarzSwapXZ.toContinuousLinearMap ∘ Y) z)
      rw [hd.fderiv]
      exact schwarzSwapXZ.injective.comp inj
  obtain ⟨f,anti,inv,move⟩ := horizontal_schwarz_on_original_surface embedding reg line
  refine ⟨f,anti,inv,fun q => schwarzSwapXZ.injective ((move q).trans ?_)⟩
  ext j
  fin_cases j <;> rfl

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.horizontal_schwarz_on_original_surface
#print axioms TwoAxisHelicoid.vertical_schwarz_on_original_surface
