import TwoAxisHelicoid.LogarithmicGaussShapeBound
import TwoAxisHelicoid.GeometricGraphEndProposition
import TwoAxisHelicoid.GeneralThinTubeLemma
import TwoAxisHelicoid.PositionalDistanceNormalTube

namespace TwoAxisHelicoid
open InnerProductSpace Complex Set Filter Topology
open scoped Topology ContDiff Manifold

/-- The pole orders of the measured height and logarithmic Gauss differential
bound the physical shape operator near the puncture, in the puncture chart. -/
theorem geometric_double_pole_end_shape_bound {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {X : M → Fin 3 → ℝ}
    (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e) (A : GeometricDoublePoleEnd X) :
    ∃ B : ℝ, 0≤B ∧ ∀ᶠ q in cocompact M, q∈A.endChart.coord.source ∧
      ∀ v : ℂ, ‖fderiv ℝ (euclideanUnitChartNormal (X ∘ A.endChart.coord.symm)) (A.endChart.coord q) v‖ ≤
        B*‖coordinateToEuclidean (fderiv ℝ (X ∘ A.endChart.coord.symm) (A.endChart.coord q) v)‖ := by
  let E := A.endChart
  let Y := X ∘ E.coord.symm
  have chart := harmonic_immersion_chart_maximal charts A.holomorphic
  have regular : ∀ᶠ z in 𝓝[≠] (0:ℂ), (∀ j, HarmonicAt (fun w => Y w j) z) ∧
      ConformalCoordinateDerivatives Y z := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0:ℂ) E.radius_pos)] with z nz near
    exact ⟨(chart z (E.mem_target_of_ball_ne near nz)).1,(chart z (E.mem_target_of_ball_ne near nz)).2.1⟩
  have order : meromorphicOrderAt (fun z => immersionComplexCoefficient Y z 2) 0 ≠ ⊤ := by rw [A.heightOrder]; decide
  have diff := height_pole_implies_regular_gauss_germ regular A.height order
  have nonzero := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero A.height).mp order
  have rg : ∀ᶠ w in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ Y w ∧ ConformalCoordinateDerivatives Y w ∧
      immersionComplexCoefficient Y w 2≠0 := by
    filter_upwards [diff,regular,nonzero] with z d r h
    exact ⟨d.1,r.2,h⟩
  obtain ⟨k,kp,bound⟩ := equal_pole_orders_logarithmic_bound (g:=immersionGaussMap Y)
    (n:=(-2:ℤ)) A.height A.gauss A.heightOrder A.gaussOrder
  have src : ∀ᶠ q in cocompact M, q∈E.coord.source := by
    change E.coord.source∈cocompact M
    simpa only [compl_compl] using E.compact_core.compl_mem_cocompact
  have toP : Tendsto E.coord (cocompact M) (𝓝[≠] (0:ℂ)) := tendsto_nhdsWithin_iff.mpr
    ⟨E.to_zero,src.mono fun _ h => E.coord_ne_zero h⟩
  have near : ∀ᶠ z in 𝓝[≠] (0:ℂ), ∀ v : ℂ, ‖fderiv ℝ (euclideanUnitChartNormal Y) z v‖≤
      4*k*‖coordinateToEuclidean (fderiv ℝ Y z v)‖ := by
    filter_upwards [eventually_eventually_nhdsWithin.mpr rg,self_mem_nhdsWithin,diff,bound] with z loc nz d b
    rw [isOpen_compl_singleton.nhdsWithin_eq nz] at loc
    exact logarithmic_gauss_controls_physical_shape loc d.2 kp b
  exact ⟨4*k,by positivity,src.and (toP.eventually near)⟩

/-- Once both geometric poles are known in the reference frame, one-sided
positional approach gives a single smooth graph with height and slope
decaying. No axis, winding, graph, or curvature assumption is required. -/
theorem positional_double_pole_end_is_C1 {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [NoncompactSpace M]
    (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e) (A : GeometricDoublePoleEnd X)
    (approach : ApproachesSetAtInfinity (range X) (range (fun z : ℂ => standardHelicoid z.re z.im))) :
    HasHelicoidC1End (coordinateToTube ∘ X) := by
  classical
  let E := A.endChart
  let e (q : M) := if q∈E.coord.source then E.coord else chartAt ℂ q
  have source (q : M) : q∈(e q).source := by
    by_cases h : q∈E.coord.source
    · simp [e,h]
    · simp [e,h]
  have hc (q : M) : HarmonicImmersionChart X (e q) := by
    by_cases h : q∈E.coord.source
    · simpa only [e,ite_eq_left h] using harmonic_immersion_chart_maximal charts A.holomorphic
    · simpa only [e,ite_eq_right h] using charts (chartAt ℂ q) (chart_mem_atlas ℂ q)
  have hr (q : M) : RegularImmersionChart X (e q) := by
    intro z hz
    obtain ⟨harm,_,inj⟩ := hc q z hz
    exact ⟨(analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (harm j))).contDiffAt,inj⟩
  obtain ⟨B,b,event⟩ := geometric_double_pole_end_shape_bound charts A
  obtain ⟨K,k,inc⟩ := mem_cocompact.mp event
  have shape := bounded_surface_weingarten_of_cross source hr (K:=K) (B:=B) (by
    intro q outside
    obtain ⟨h,eq⟩ := inc outside
    change q∈E.coord.source at h
    simpa only [e,ite_eq_left h] using eq)
  have tails (C : Set M) (c : IsCompact C) : ∃ U : Set M, IsConnected U ∧ IsCompact Uᶜ ∧ Disjoint U C := by
    obtain ⟨U,conn,comp,dis⟩ := E.connected_tails C c
    have ne : U.Nonempty := by
      by_contra empty
      rw [not_nonempty_iff_eq_empty.mp empty,compl_empty] at comp
      exact noncompact_univ M comp
    exact ⟨U,⟨ne,conn⟩,comp,dis⟩
  apply general_one_end_thin_C1_graph_of_bounded_weingarten X closed tails e source hr k b shape
  intro ε ep
  obtain ⟨U,compact,tube⟩ := positional_standard_end_actual_tubes closed.isProperMap approach (min ε 1) (lt_min ep zero_lt_one)
  refine ⟨Uᶜ,compact,?_⟩
  intro q hq
  obtain ⟨v,r,θ,small,eq⟩ := tube q (not_not.mp hq)
  have strip : ((v,r),θ)∈helicoidTubeStrip := small.trans_le (min_le_right _ _)
  rw [eq,helicoidSignedDistance_on_normal strip]
  exact ⟨helicoidTubeEquiv.map_source strip,small.le.trans (min_le_left _ _)⟩

/-- The reference pitch and the vanishing analytic Gauss correction follow
from the actual positional asymptote and the two poles alone. -/
theorem positional_double_pole_end_has_normalized_exterior {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [NoncompactSpace M]
    (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e) (A : GeometricDoublePoleEnd X)
    (approach : ApproachesSetAtInfinity (range X) (range (fun z : ℂ => standardHelicoid z.re z.im))) :
    ∃ D : GeometricExteriorCoordinate X, D.pitch=1 ∧ D.correction 0=0 :=
  (harmonic_graph_end_proposition X closed charts (positional_double_pole_end_is_C1 X closed charts A approach)).choose_spec.2.2
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.geometric_double_pole_end_shape_bound
#print axioms TwoAxisHelicoid.positional_double_pole_end_is_C1
#print axioms TwoAxisHelicoid.positional_double_pole_end_has_normalized_exterior
