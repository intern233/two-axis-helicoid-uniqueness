import TwoAxisHelicoid.HolomorphicSubdomainCoordinate
import TwoAxisHelicoid.RoundCylinderCollars
import TwoAxisHelicoid.HelicoidNaturalPuncture
import TwoAxisHelicoid.HelicoidAnnularCompactification
import TwoAxisHelicoid.MaximalHarmonicImmersionChart

namespace TwoAxisHelicoid
open Complex Set Filter Metric Topology
open scoped Topology ContDiff Manifold

/-- The two puncture limits of a topological chart provide arbitrarily
far connected tails with compact complement, independently of genus. -/
theorem PuncturedComplexEnd.connected_tails {M : Type*} [TopologicalSpace M] [T2Space M]
    (D : PuncturedComplexEnd M) : HasConnectedCompactTails M := by
  intro K hk
  let e := D.coord
  have ev := D.from_zero.eventually hk.compl_mem_cocompact
  obtain ⟨b,hb,ballSub⟩ := Metric.mem_nhdsWithin_iff.mp ev
  let r := min b D.radius
  have hr : 0<r := lt_min hb D.radius_pos
  let T := {w : ℂ | 0<‖w‖ ∧ ‖w‖<r}
  let U := e.source ∩ e ⁻¹' T
  have op : IsOpen T := (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have domain (z : ℂ) (hz : z∈T) : z∈e.target := D.mem_target_of_ball_ne
    (by simpa only [mem_ball,dist_zero_right] using hz.2.trans_le (min_le_right _ _)) (norm_pos_iff.mp hz.1)
  have eq : U=e.symm '' T := by
    ext x
    constructor
    · rintro ⟨s,t⟩
      exact ⟨e x,t,e.left_inv s⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨e.map_target (domain z hz),by change e (e.symm z)∈T; rw [e.right_inv (domain z hz)]; exact hz⟩
  have openU : IsOpen U := e.continuousOn.isOpen_inter_preimage e.open_source op
  have src : e.source∈cocompact M := by simpa only [compl_compl] using D.compact_core.compl_mem_cocompact
  have tail : U∈cocompact M := by
    filter_upwards [src,D.to_zero.eventually (ball_mem_nhds (0:ℂ) hr)] with x hx near
    exact ⟨hx,norm_pos_iff.mpr (D.coord_ne_zero hx),by simpa only [mem_ball,dist_zero_right] using near⟩
  obtain ⟨C,c,sub⟩ := mem_cocompact'.mp tail
  refine ⟨U,?_,c.of_isClosed_subset openU.isClosed_compl sub,?_⟩
  · rw [eq]
    exact (complex_open_annulus_isPreconnected (r := 0) (R := r) le_rfl).image _ (e.symm.continuousOn.mono domain)
  · apply disjoint_left.mpr
    intro x hx hK
    obtain ⟨z,hz,rfl⟩ := eq ▸ hx
    exact ballSub ⟨by simpa only [mem_ball,dist_zero_right] using hz.2.trans_le (min_le_left _ _),norm_pos_iff.mp hz.1⟩ hK

universe u

/-- A properly embedded harmonic conformal surface with a physical C¹
helicoidal graph end fills by a single complex point. Neither a genus
nor a straight line nor a meromorphic differential is required to
identify the conformal end. -/
theorem physical_helicoid_graph_holomorphic_filling {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [NoncompactSpace M]
    {X : M → Fin 3 → ℝ} (closed : IsClosedEmbedding X) (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (graph : HasHelicoidC1End (coordinateToTube ∘ X)) (uni : TopologicalPlaneUniformization.{u}) :
    ∃ E : PuncturedComplexEnd M, E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := by
  have loc : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℂ _
  obtain ⟨D,_⟩ := graph.natural_puncture_coordinate (coordinateToTube_isProperMap closed.isProperMap)
  obtain ⟨a,k,ah,round⟩ := puncture_topology_round_complex_chart D uni
  obtain ⟨e,r,R,hr,lt,hol,compact,tgt,radius⟩ := one_ended_round_chart_collar D.connected_tails a k ah round
  have harm := harmonic_immersion_chart_maximal charts hol
  have iso : InducedIsothermalChart X e := by
    refine ⟨fun z hz => ⟨?_,(harm z hz).2.2⟩,fun z hz => (harm z hz).2.1⟩
    exact (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt ((harm z hz).1 j)).contDiffAt
  obtain ⟨_,E,eq,_⟩ := helicoid_annular_chart_fills closed.isProperMap closed.injective graph e iso hr lt tgt compact radius
  exact ⟨E,by rw [eq]; exact hol⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_helicoid_graph_holomorphic_filling
