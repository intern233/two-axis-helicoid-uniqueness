import TwoAxisHelicoid.MarkedTorusPunctureCoordinate
import TwoAxisHelicoid.ProvedPlaneUniformization
import TwoAxisHelicoid.PhysicalAnnulusFilling

namespace TwoAxisHelicoid
open Set Filter Topology TopologicalSpace Metric
open scoped Topology ContDiff Manifold

/-- Transport the topological end coordinates and their two proper limits. -/
noncomputable def PuncturedComplexEnd.pullbackHomeomorph {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] (D : PuncturedComplexEnd N) (e : M ≃ₜ N) :
    PuncturedComplexEnd M where
  coord := e.transOpenPartialHomeomorph D.coord
  radius := D.radius
  radius_pos := D.radius_pos
  target_eq := D.target_eq
  compact_core := e.isCompact_preimage.mpr D.compact_core
  to_zero := D.to_zero.comp e.isClosedEmbedding.tendsto_cocompact
  from_zero := e.symm.isClosedEmbedding.tendsto_cocompact.comp D.from_zero

/-- An arbitrary complex surface of topological type once-punctured
torus has a holomorphic round end collar. Its inner radius may be
positive, and the physical end converges to that inner boundary. -/
theorem unmarked_analytic_handle_round_collar {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {L : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L) :
    ∃ (c : OpenPartialHomeomorph M ℂ) (r R : ℝ), 0≤r ∧ r<R ∧
      c∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M ∧ IsCompact c.sourceᶜ ∧
      c.target={z : ℂ | r<‖z‖ ∧ ‖z‖<R} ∧ Tendsto (fun x => ‖c x‖) (cocompact M) (𝓝 r) := by
  obtain ⟨D₀,_⟩ := marked_torus_puncture_coordinate L
  let D := D₀.pullbackHomeomorph top
  let S : Opens M := ⟨D.coord.source,D.coord.open_source⟩
  have target : D.coord.target={z : ℂ | 0<‖z‖ ∧ ‖z‖<D.radius} := by
    rw [D.target_eq]
    ext z
    change (dist z 0<D.radius ∧ z≠0) ↔ 0<‖z‖ ∧ ‖z‖<D.radius
    rw [dist_zero_right,norm_pos_iff,and_comm]
  let u := D.coord.toHomeomorphSourceTarget.trans (Homeomorph.setCongr target)
  have small := half_pos D.radius_pos
  have size : ‖((D.radius/2:ℝ):ℂ)‖=D.radius/2 := by rw [Complex.norm_real,Real.norm_of_nonneg small.le]
  have non : Nonempty S := ⟨u.symm ⟨(D.radius/2:ℝ), by
    change 0 < ‖((D.radius/2:ℝ):ℂ)‖ ∧ ‖((D.radius/2:ℝ):ℂ)‖ < D.radius
    rw [size]
    exact ⟨small,half_lt_self D.radius_pos⟩⟩⟩
  obtain ⟨T,round,⟨U⟩⟩ := annular_riemann_surface_uniformization_proved S D.radius D.radius_pos ⟨u⟩
  obtain ⟨c,cs,ct,hol⟩ := holomorphic_subdomain_coordinate S T non U
  exact one_ended_round_chart_collar D.connected_tails c (by rw [cs]; exact D.compact_core) hol (by rw [ct]; exact round)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.unmarked_analytic_handle_round_collar

