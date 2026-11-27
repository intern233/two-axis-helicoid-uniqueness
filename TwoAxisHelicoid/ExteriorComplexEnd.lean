import TwoAxisHelicoid.PuncturedEndInverseEscape
import TwoAxisHelicoid.ComplexEndCompactification
import Mathlib.Analysis.Normed.Field.Lemmas

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology Bornology
open scoped Topology ContDiff OnePoint Manifold
set_option maxHeartbeats 1400000

variable {M : Type*} [TopologicalSpace M]

theorem inverse_mem_punctured_disk_iff {R : ℝ} (hR : 0 < R) (z : ℂ) :
    z⁻¹ ∈ ball (0:ℂ) R⁻¹ \ {0} ↔ R < ‖z‖ := by
  simp only [Set.mem_sdiff,mem_ball,dist_zero_right,norm_inv,mem_singleton_iff,inv_eq_zero]
  by_cases hz : z = 0
  · simp [hz,hR.not_gt]
  · simp only [hz,not_false_eq_true,and_true]
    exact inv_lt_inv₀ (norm_pos_iff.mpr hz) hR

/-- Reciprocation converts an actual exterior height parameter into
the holomorphic puncture coordinate used for compactification. -/
noncomputable def reciprocalExteriorChart (e : OpenPartialHomeomorph M ℂ) {R : ℝ} (hR : 0 < R)
    (ht : e.target = {z : ℂ | R < ‖z‖}) : OpenPartialHomeomorph M ℂ where
  toFun x := (e x)⁻¹
  invFun w := e.symm w⁻¹
  source := e.source
  target := ball (0:ℂ) R⁻¹ \ {0}
  map_source' := by
    intro x hx
    apply (inverse_mem_punctured_disk_iff hR _).mpr
    exact (Set.ext_iff.mp ht (e x)).mp (e.map_source hx)
  map_target' := by
    intro w hw
    apply e.map_target
    rw [ht]
    exact (inverse_mem_punctured_disk_iff hR w⁻¹).mp (by simpa only [inv_inv] using hw)
  left_inv' := by intro x hx; simpa only [inv_inv] using e.left_inv hx
  right_inv' := by
    intro w hw
    have h : w⁻¹ ∈ e.target := ht ▸ (inverse_mem_punctured_disk_iff hR w⁻¹).mp (by simpa only [inv_inv] using hw)
    rw [e.right_inv h,inv_inv]
  open_source := e.open_source
  open_target := isOpen_ball.sdiff isClosed_singleton
  continuousOn_toFun := by
    intro x hx
    have hp : R < ‖e x‖ := (Set.ext_iff.mp ht (e x)).mp (e.map_source hx)
    exact ((e.continuousAt hx).inv₀ (norm_pos_iff.mp (hR.trans hp))).continuousWithinAt
  continuousOn_invFun := by
    intro w hw
    have h : w⁻¹ ∈ e.target := ht ▸ (inverse_mem_punctured_disk_iff hR w⁻¹).mp (by simpa only [inv_inv] using hw)
    exact ((e.symm.continuousAt h).comp (continuousAt_inv₀ hw.2)).continuousWithinAt

theorem reciprocalExteriorChart_mem_maximalAtlas [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    (e : OpenPartialHomeomorph M ℂ) {R : ℝ} (hR : 0 < R) (ht : e.target = {z : ℂ | R < ‖z‖})
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) :
    reciprocalExteriorChart e hR ht ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · intro x hx
    have hx' : x ∈ e.source := hx
    have hp : R < ‖e x‖ := (Set.ext_iff.mp ht (e x)).mp (e.map_source hx')
    have hn := norm_pos_iff.mp (hR.trans hp)
    have hc : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun z : ℂ => z⁻¹) (e x) :=
      contMDiffAt_iff_contDiffAt.mpr (analyticAt_id.inv hn).contDiffAt
    exact (hc.comp x (contMDiffAt_of_mem_maximalAtlas he hx')).contMDiffWithinAt
  · intro w hw
    have hw' : w ∈ ball (0 : ℂ) R⁻¹ \ {0} := hw
    have h : w⁻¹ ∈ e.target := ht ▸ (inverse_mem_punctured_disk_iff hR w⁻¹).mp (by simpa only [inv_inv] using hw')
    have hc : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun z : ℂ => z⁻¹) w :=
      contMDiffAt_iff_contDiffAt.mpr (analyticAt_id.inv hw'.2).contDiffAt
    exact ((contMDiffAt_symm_of_mem_maximalAtlas he h).comp w hc).contMDiffWithinAt

/-- The exterior chart and spatial escape of its height coordinate
supply all the topology needed to add a complex point. -/
noncomputable def exteriorCoordinateComplexEnd [T2Space M] [WeaklyLocallyCompactSpace M] [NoncompactSpace M]
    (e : OpenPartialHomeomorph M ℂ) {R : ℝ} (hR : 0 < R) (ht : e.target = {z : ℂ | R < ‖z‖})
    (hcore : IsCompact e.sourceᶜ) (hesc : Tendsto (fun x => ‖e x‖) (cocompact M) atTop) :
    PuncturedComplexEnd M :=
  puncturedComplexEndOfChart (reciprocalExteriorChart e hR ht) (inv_pos.mpr hR) rfl hcore
    (tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp hesc))

theorem exteriorCoordinate_fills_complex_manifold [T2Space M] [WeaklyLocallyCompactSpace M] [NoncompactSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    (e : OpenPartialHomeomorph M ℂ) {R : ℝ} (hR : 0 < R) (ht : e.target = {z : ℂ | R < ‖z‖})
    (hcore : IsCompact e.sourceᶜ) (hesc : Tendsto (fun x => ‖e x‖) (cocompact M) atTop)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) :
    let E := exteriorCoordinateComplexEnd e hR ht hcore hesc
    let _ := compactifiedEndAtlas E
    IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) ∧
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some : M → OnePoint M) := by
  let E := exteriorCoordinateComplexEnd e hR ht hcore hesc
  exact ⟨compactifiedEndAtlas_isManifold E (reciprocalExteriorChart_mem_maximalAtlas e hR ht he),
    compactifiedEnd_inclusion_contMDiff E⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exteriorCoordinate_fills_complex_manifold
