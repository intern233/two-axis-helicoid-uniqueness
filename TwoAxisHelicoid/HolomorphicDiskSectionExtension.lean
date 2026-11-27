import TwoAxisHelicoid.GenusOneCanonicalDivisor
import TwoAxisHelicoid.PlaneChartOrientationCocycle

namespace TwoAxisHelicoid
open Complex Set Filter Topology Metric
open scoped Topology ContDiff Manifold

private theorem chart_change_derivative_chain {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (i j k : M) {x : M} (hi : x∈(chartAt ℂ i).source)
    (hj : x∈(chartAt ℂ j).source) (hk : x∈(chartAt ℂ k).source) :
    deriv ((chartAt ℂ k) ∘ (chartAt ℂ i).symm) (chartAt ℂ i x)=
      deriv ((chartAt ℂ k) ∘ (chartAt ℂ j).symm) (chartAt ℂ j x) *
      deriv ((chartAt ℂ j) ∘ (chartAt ℂ i).symm) (chartAt ℂ i x) := by
  let a := chartAt ℂ i
  let b := chartAt ℂ j
  let c := chartAt ℂ k
  let f := b ∘ a.symm
  let g := c ∘ b.symm
  have ht (i j : M) (hi : x∈(chartAt ℂ i).source) (hj : x∈(chartAt ℂ j).source) :
      AnalyticAt ℂ ((chartAt ℂ j) ∘ (chartAt ℂ i).symm) (chartAt ℂ i x) :=
    (complexAtlas_realized_transition (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ i))
      (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ j)) (planeChart_transition_source hi hj)).analyticAt
  have hx : f (a x)=b x := congrArg b (a.left_inv hi)
  have gb : DifferentiableAt ℂ g (f (a x)) := hx ▸ (ht j k hj hk).differentiableAt
  have same : g ∘ f =ᶠ[𝓝 (a x)] c ∘ a.symm := by
    have near := a.symm.continuousAt (a.map_source hi)
    have inb : a.symm (a x)∈b.source := (a.left_inv hi).symm ▸ hj
    filter_upwards [near.eventually (b.open_source.mem_nhds inb)] with z hz
    exact congrArg c (b.left_inv hz)
  have chain := deriv_comp (a x) gb (ht i j hi hj).differentiableAt
  rw [hx] at chain
  exact same.deriv_eq.symm.trans chain

/-- Compatible local coefficients on any cover by preferred coordinate
disks extend to a global section of the holomorphic cotangent bundle. -/
theorem HolomorphicCoefficientDisks.exists_global_section {M : Type*} [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] (A : HolomorphicCoefficientDisks M) (comp : A.compatibleOneForm) :
    ∃ w : holomorphicCotangentSections M, ∀ i x, x∈A.primitives.domain i →
      w.1 i (chartAt ℂ i x)=A.coefficient i (chartAt ℂ i x) := by
  classical
  let G := fun (i : M) (z : ℂ) =>
    let e := chartAt ℂ i
    let x := e.symm z
    if z∈e.target then A.coefficient x (chartAt ℂ x x)*deriv ((chartAt ℂ x) ∘ e.symm) z else 0
  have atx (i x : M) (hi : x∈(chartAt ℂ i).source) :
      G i (chartAt ℂ i x)=A.coefficient x (chartAt ℂ x x)*deriv ((chartAt ℂ x) ∘ (chartAt ℂ i).symm) (chartAt ℂ i x) := by
    simp only [G,(chartAt ℂ i).map_source hi,ite_true,(chartAt ℂ i).left_inv hi]
  have agree (i j x : M) (hi : x∈(chartAt ℂ i).source) (hj : x∈A.primitives.domain j) :
      G i (chartAt ℂ i x)=A.coefficient j (chartAt ℂ j x)*deriv ((chartAt ℂ j) ∘ (chartAt ℂ i).symm) (chartAt ℂ i x) := by
    rw [atx i x hi,comp j x x ⟨hj,A.primitives.mem_domain x⟩,
      chart_change_derivative_chain i j x hi hj.1 (mem_chart_source ℂ x),mul_assoc]
  have hol (i : M) (z : ℂ) (hz : z∈(chartAt ℂ i).target) : AnalyticAt ℂ (G i) z := by
    let e := chartAt ℂ i
    let x := e.symm z
    let j := chartAt ℂ x
    let f := j ∘ e.symm
    have source : z∈(e.symm.trans j).source := ⟨hz,mem_chart_source ℂ x⟩
    have ha : AnalyticAt ℂ f z := (complexAtlas_realized_transition (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ i))
      (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ x)) source).analyticAt
    have ag := A.analytic x (f z) (mem_ball_self (A.radius_pos x))
    apply ((ag.comp ha).mul ha.deriv).congr
    filter_upwards [e.open_target.mem_nhds hz,(e.symm.continuousAt hz).eventually
      ((A.primitives.domain_isOpen x).mem_nhds (A.primitives.mem_domain x))] with v hv hw
    have eq := agree i x (e.symm v) (e.map_target hv) hw
    change G i (e (e.symm v))=A.coefficient x (f v)*deriv f (e (e.symm v)) at eq
    rw [e.right_inv hv] at eq
    exact eq.symm
  have gluing (i j x : M) (hx : x∈(chartAt ℂ i).source∩(chartAt ℂ j).source) :
      G i (chartAt ℂ i x)=G j (chartAt ℂ j x)*deriv ((chartAt ℂ j) ∘ (chartAt ℂ i).symm) (chartAt ℂ i x) := by
    rw [atx i x hx.1,atx j x hx.2,chart_change_derivative_chain i j x hx.1 hx.2 (mem_chart_source ℂ x),mul_assoc]
  refine ⟨⟨G,hol,gluing,fun i z hz => by simp [G,hz]⟩,?_⟩
  intro i x hx
  change G i (chartAt ℂ i x)=A.coefficient i (chartAt ℂ i x)
  rw [atx i x hx.1,comp i x x ⟨hx,A.primitives.mem_domain x⟩]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.exists_global_section
