import TwoAxisHelicoid.AntiholomorphicChartGerms
import TwoAxisHelicoid.ChartedSurfaceReflectionImage

namespace TwoAxisHelicoid
open Complex Set Filter Topology Metric
open scoped Topology ComplexConjugate ContDiff Manifold

/-- Antiholomorphicity of the physical symmetry continues from one
source-target chart pair along the entire connected original surface.
Neither a universal cover nor a marked torus is used. -/
theorem charted_spatial_symmetry_antiholomorphic {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [PreconnectedSpace M] {X : M → Fin 3 → ℝ}
    (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d)
    {R : (Fin 3 → ℝ) → Fin 3 → ℝ} (ra : ∀ y, AnalyticAt ℝ R y)
    {f : M → M} (cf : Continuous f) (space : ∀ x, X (f x)=R (X x)) {p : M}
    (seed : AnalyticAt ℂ ((chartAt ℂ (f p)) ∘ f ∘ (chartAt ℂ p).symm ∘ conj) (conj (chartAt ℂ p p))) :
    ∀ (a b : OpenPartialHomeomorph M ℂ), a∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M →
      b∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M → ∀ x, x∈a.source → f x∈b.source →
      AnalyticAt ℂ (b ∘ f ∘ a.symm ∘ conj) (conj (a x)) := by
  let P : Set M := {x | AnalyticAt ℂ ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm ∘ conj) (conj (chartAt ℂ x x))}
  have preferred (x : M) := IsManifold.subset_maximalAtlas (I := 𝓘(ℂ,ℂ)) (n := ω) (chart_mem_atlas ℂ x)
  have realChart (i : M) (z : ℂ) (hz : z∈(chartAt ℂ i).target) : AnalyticAt ℝ (X ∘ (chartAt ℂ i).symm) z :=
    analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt ((charts _ (chart_mem_atlas ℂ i) z hz).1 j))
  have all : P=univ := by
    apply preconnected_local_propagation (show P.Nonempty from ⟨p,seed⟩)
    intro i
    let e := chartAt ℂ i
    let d := chartAt ℂ (f i)
    let z₀ := conj (e i)
    let F := d ∘ f ∘ e.symm ∘ conj
    have ei : i∈e.source := mem_chart_source ℂ i
    have di : f i∈d.source := mem_chart_source ℂ (f i)
    have cc : Tendsto conj (𝓝 z₀) (𝓝 (e i)) := by simpa only [z₀,starRingEnd_self_apply] using (Complex.continuous_conj.continuousAt (x := z₀)).tendsto
    have loc : Tendsto (e.symm ∘ conj) (𝓝 z₀) (𝓝 i) := by
      simpa only [e.left_inv ei] using (e.symm.continuousAt (e.map_source ei)).tendsto.comp cc
    have near := (cc.eventually (e.open_target.mem_nhds (e.map_source ei))).and
      ((cf.continuousAt.tendsto.comp loc).eventually (d.open_source.mem_nhds di))
    obtain ⟨r,rp,region⟩ := Metric.mem_nhds_iff.mp near
    let D := ball z₀ r
    let W := e.source ∩ e ⁻¹' (conj ⁻¹' D)
    have wo : IsOpen W := e.isOpen_inter_preimage (isOpen_ball.preimage Complex.continuous_conj)
    have target {x : M} (hx : x∈W) : f x∈d.source := by
      have t := (region hx.2).2
      change f (e.symm (conj (conj (e x))))∈d.source at t
      rwa [starRingEnd_self_apply,e.left_inv hx.1] at t
    have realF (z : ℂ) (hz : z∈D) : AnalyticAt ℝ F z := by
      have h := region hz
      have diff := regular_spatial_lift_chart_analytic cf space h.1 h.2 (ra _) (realChart i _ h.1)
        (realChart (f i) _ (d.map_source h.2)) (charts d (chart_mem_atlas ℂ (f i)) _ (d.map_source h.2)).2.2
      exact diff.comp (Complex.conjCLE.toContinuousLinearMap.analyticAt z)
    refine ⟨W,wo.mem_nhds ⟨ei,mem_ball_self rp⟩,?_⟩
    rintro ⟨q,hq,good⟩
    have start := antiholomorphic_germ_change_charts cf (preferred i) (preferred (f i)) (preferred q) (preferred (f q))
      hq.1 (target hq) (mem_chart_source ℂ q) (mem_chart_source ℂ (f q)) good
    have analytic := analytic_complex_of_open_patch (U := D) isOpen_ball (convex_ball _ _).isPreconnected realF hq.2 start
    intro x hx
    exact antiholomorphic_germ_change_charts cf (preferred x) (preferred (f x)) (preferred i) (preferred (f i))
      (mem_chart_source ℂ x) (mem_chart_source ℂ (f x)) hx.1 (target hx) (analytic _ hx.2)
  intro a b aa ab x xa xb
  have atx : x∈P := all ▸ mem_univ x
  exact antiholomorphic_germ_change_charts cf aa ab (preferred x) (preferred (f x)) xa xb
    (mem_chart_source ℂ x) (mem_chart_source ℂ (f x)) atx

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.charted_spatial_symmetry_antiholomorphic
