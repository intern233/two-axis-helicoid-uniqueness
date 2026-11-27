import TwoAxisHelicoid.TorusHorizontalSchwarzSymmetry
import TwoAxisHelicoid.MaximalHarmonicImmersionChart

namespace TwoAxisHelicoid
open Complex Set Filter Topology Metric InnerProductSpace
open scoped Topology ContDiff Manifold ComplexConjugate

theorem preconnected_local_propagation {M : Type*} [TopologicalSpace M] [PreconnectedSpace M]
    {P : Set M} (seed : P.Nonempty) (spread : ∀ x, ∃ W∈𝓝 x, (W∩P).Nonempty → W⊆P) : P=univ := by
  have op : IsOpen P := isOpen_iff_mem_nhds.mpr (fun x hx => by
    obtain ⟨W,wn,rule⟩ := spread x
    exact mem_of_superset wn (rule ⟨x,mem_of_mem_nhds wn,hx⟩))
  have closed : IsOpen Pᶜ := isOpen_iff_mem_nhds.mpr (fun x outside => by
    obtain ⟨W,wn,rule⟩ := spread x
    apply mem_of_superset wn
    intro y hy inside
    exact outside (rule ⟨y,hy,inside⟩ (mem_of_mem_nhds wn)))
  exact (show IsClopen P from ⟨isOpen_compl_iff.mp closed,op⟩).eq_univ seed

/-- Analytic spatial image continuation on a connected charted surface
with arbitrary topology and conformal structure. -/
theorem charted_analytic_image_continuation {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [PreconnectedSpace M] {Y : M → Fin 3 → ℝ} {K : Set (Fin 3 → ℝ)} (closed : IsClosed K)
    (equation : ∀ p∈K, ∃ G : (Fin 3 → ℝ) → Fin 3 → ℝ, AnalyticAt ℝ G p ∧ ∀ᶠ v in 𝓝 p, v∈K ↔ G v=0)
    (charts : ∀ i z, z∈(chartAt ℂ i).target → AnalyticAt ℝ (Y ∘ (chartAt ℂ i).symm) z)
    {b : M} (initial : ∀ᶠ w in 𝓝 b, Y w∈K) : ∀ x, Y x∈K := by
  let P := interior (Y ⁻¹' K)
  have seed : b∈P := mem_interior_iff_mem_nhds.mpr initial
  have gross : P=univ := by
    apply preconnected_local_propagation ⟨b,seed⟩
    intro i
    let e := chartAt ℂ i
    have ei : i∈e.source := mem_chart_source ℂ i
    obtain ⟨r,rp,sub⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source ei))
    let D := ball (e i) r
    let W := e.source ∩ e ⁻¹' D
    have wo : IsOpen W := e.isOpen_inter_preimage isOpen_ball
    refine ⟨W,wo.mem_nhds ⟨ei,mem_ball_self rp⟩,?_⟩
    rintro ⟨q,hq,good⟩
    have hs : Tendsto e.symm (𝓝 (e q)) (𝓝 q) := by simpa only [e.left_inv hq.1] using (e.symm.continuousAt (e.map_source hq.1)).tendsto
    have atq : Y ⁻¹' K∈𝓝 q := mem_interior_iff_mem_nhds.mp good
    have all : MapsTo (Y ∘ e.symm) D K := analytic_image_continues_in_closed_hypersurface isOpen_ball
      (convex_ball _ _).isPreconnected (fun z hz => charts i z (sub hz)) closed equation hq.2 (hs.eventually atq)
    have inside : W ⊆ Y ⁻¹' K := fun w hw => by
      change Y w∈K
      simpa only [Function.comp_apply,e.left_inv hw.1] using all hw.2
    exact interior_maximal inside wo
  intro x
  exact interior_subset (s := Y ⁻¹' K) (show x∈P by rw [gross]; trivial)

/-- A complete horizontal line in any connected closed embedded
harmonic conformal surface forces a global spatial half turn. -/
theorem charted_closed_surface_horizontal_half_turn {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [PreconnectedSpace M] {X : M → Fin 3 → ℝ} (emb : IsClosedEmbedding X)
    (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d)
    (axis : ∀ s : ℝ, (![s,0,0] : Fin 3 → ℝ)∈range X) :
    ∃ f : M ≃ₜ M, (∀ x, X (f x)=halfTurnX (X x)) ∧ Function.Involutive f := by
  have analytic (i : M) (z : ℂ) (hz : z∈(chartAt ℂ i).target) : AnalyticAt ℝ (X ∘ (chartAt ℂ i).symm) z :=
    analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt ((charts _ (chart_mem_atlas ℂ i) _ hz).1 j))
  have equations (y : Fin 3 → ℝ) (hy : y∈range X) : ∃ G : (Fin 3 → ℝ) → Fin 3 → ℝ,
      AnalyticAt ℝ G y ∧ ∀ᶠ v in 𝓝 y, v∈range X ↔ G v=0 := by
    obtain ⟨x,rfl⟩ := hy
    let e := chartAt ℂ x
    have h := e.map_source (mem_chart_source ℂ x)
    exact embedded_analytic_surface_local_equation emb.isEmbedding e (mem_chart_source ℂ x) (analytic x _ h)
      (charts e (chart_mem_atlas ℂ x) _ h).2.2
  obtain ⟨p,hp⟩ := axis 0
  have zero : X p=0 := by rw [hp]; ext j; fin_cases j <;> rfl
  let e := chartAt ℂ p
  have ep : p∈e.source := mem_chart_source ℂ p
  have et := e.map_source ep
  obtain ⟨S,_,_,germ⟩ := embedded_axis_local_reflection emb.isEmbedding e ep zero axis (analytic p _ et)
    (charts e (chart_mem_atlas ℂ p) _ et).2.2
    (by filter_upwards [e.open_target.mem_nhds et] with w hw using ⟨(charts e (chart_mem_atlas ℂ p) _ hw).1,
      (charts e (chart_mem_atlas ℂ p) _ hw).2.1⟩)
  have init : ∀ᶠ x in 𝓝 p, halfTurnX (X x)∈range X := by
    filter_upwards [(e.continuousAt ep).eventually germ,e.open_source.mem_nhds ep] with x ex xs
    exact ⟨e.symm (S (conj (e x))),by simpa only [e.left_inv xs] using ex.2⟩
  have maps : ∀ x, halfTurnX (X x)∈range X := charted_analytic_image_continuation (Y := halfTurnX ∘ X)
    emb.isClosed_range equations (fun i z hz => (halfTurnX_analyticAt _).comp (analytic i z hz)) init
  let f := embeddedRangeInvolution emb.isEmbedding halfTurnX halfTurnX_continuous halfTurnX_involutive maps
  have eq := embeddedRangeInvolution_eq emb.isEmbedding halfTurnX halfTurnX_continuous halfTurnX_involutive maps
  exact ⟨f,eq,fun x => emb.injective ((eq (f x)).trans ((congrArg halfTurnX (eq x)).trans (halfTurnX_involutive _)))⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.charted_analytic_image_continuation
#print axioms TwoAxisHelicoid.charted_closed_surface_horizontal_half_turn
