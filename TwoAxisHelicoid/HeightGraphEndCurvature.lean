import TwoAxisHelicoid.HeightEndRegularParameter
import TwoAxisHelicoid.HelicoidHeightGraphDiskCurvature
import TwoAxisHelicoid.RegularChartShapeTransport
import TwoAxisHelicoid.MinimalManifoldComplexStructure

namespace TwoAxisHelicoid
open Complex Set Filter Metric Bornology Topology
open scoped Topology ContDiff Manifold

/-- Uniform end curvature on the actual surface in its originally given
real charts. In a single smooth normal graph, height decay suffices.
No bound on the derivative of its height, or on its conformal radius,
is included among the hypotheses. -/
theorem minimal_height_graph_end_shape_bound {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    (X : M → Fin 3 → ℝ) (proper : IsProperMap X)
    (regular : ∀ q, RegularImmersionChart X (chartAt ℂ q))
    (minimal : ∀ q, coordinateMeanCurvature (X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q)=0)
    (graph : HasHelicoidHeightEnd (coordinateToTube ∘ X)) :
    ∃ K : Set M, IsCompact K ∧ ∀ q∉K, ∀ v : ℂ,
      ‖fderiv ℝ (euclideanUnitChartNormal (X ∘ (chartAt ℂ q).symm)) ((chartAt ℂ q) q) v‖≤
        12288*‖coordinateToEuclidean (fderiv ℝ (X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q) v)‖ := by
  obtain ⟨e,u,tail,far,escape,shape⟩ := graph.physical_parameter proper
  let Y := helicoidHeightSurface u
  have germ (z : ℂ) (hz : z∈e.target) : X ∘ e.symm=ᶠ[𝓝 z] Y := by
    filter_upwards [e.open_target.mem_nhds hz] with w hw using (shape w hw).2.2
  have regY (z : ℂ) (hz : z∈e.target) : ContDiffAt ℝ ∞ Y z ∧ Function.Injective (fderiv ℝ Y z) :=
    ⟨helicoidHeightSurface_contDiffAt (shape z hz).1,helicoidHeightSurface_injective_derivative
      ((shape z hz).1.differentiableAt (by simp)) (shape z hz).2.1⟩
  have regE : RegularImmersionChart X e := by
    intro z hz
    exact ⟨(regY z hz).1.congr_of_eventuallyEq (germ z hz),by rw [(germ z hz).fderiv_eq (𝕜:=ℝ)];exact (regY z hz).2⟩
  have minY (z : ℂ) (hz : z∈e.target) : coordinateMeanCurvature Y z=0 := by
    rw [← coordinateMeanCurvature_congr (germ z hz)]
    exact minimal_surface_chart_meanCurvature_zero regular minimal regE hz
  obtain ⟨A,_,outer⟩ := hasBasis_cobounded_norm.eventually_iff.mp far
  have enough : {q : M | q∈e.source ∧ A+1<‖e q‖}∈cocompact M := by
    filter_upwards [tail,escape.eventually_gt_atTop (A+1)] with q hq he using And.intro hq he
  obtain ⟨K,compact,off⟩ := mem_cocompact'.mp enough
  refine ⟨K,compact,?_⟩
  intro q qK v
  have atq : q∈e.source ∧ A+1<‖e q‖ := by
    by_contra hn
    exact qK (off hn)
  have disk {w : ℂ} (hw : w∈ball (e q) (1/2)) : w∈e.target := by
    apply outer
    change A≤‖w‖
    have d := norm_sub_norm_le (e q) w
    rw [← dist_eq_norm,dist_comm] at d
    have lt := mem_ball.mp hw
    linarith [atq.2]
  have onDisk := helicoid_height_graph_disk_curvature (u:=u) (a:=e q)
    (fun _ h => (shape _ (disk h)).1) (fun _ h => (shape _ (disk h)).2.1) (fun _ h => minY _ (disk h))
  let a := chartAt ℂ q
  let k := a.symm.trans e
  have aq : q∈a.source := mem_chart_source ℂ q
  have source : a q∈k.source := by
    refine ⟨a.map_source aq,?_⟩
    change a.symm (a q)∈e.source
    rw [a.left_inv aq]
    exact atq.1
  have center : k (a q)=e q := congrArg e (a.left_inv aq)
  have comp : (X ∘ a.symm)=ᶠ[𝓝 (a q)] Y ∘ k := by
    filter_upwards [k.open_source.mem_nhds source] with w hw
    have eq := (shape (k w) (e.map_source hw.2)).2.2
    change X (a.symm w)=Y (k w)
    exact (congrArg X (e.left_inv hw.2)).symm.trans eq
  apply chart_normal_derivative_bound_of_change comp ((regularImmersionChart_transition (regular q) regE source).of_le (by norm_num))
  · filter_upwards [a.open_target.mem_nhds (a.map_source aq)] with w hw
    exact ⟨((regular q w hw).1.of_le (by norm_num)),(regular q w hw).2⟩
  · filter_upwards [e.open_target.mem_nhds (e.map_source source.2)] with w hw
    exact ⟨(regY w hw).1.of_le (by norm_num),(regY w hw).2⟩
  · rw [center]
    exact onDisk

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.minimal_height_graph_end_shape_bound
