import TwoAxisHelicoid.AnnularHelicoidInnerRadius
import TwoAxisHelicoid.AnnularEndInverseEscape
import TwoAxisHelicoid.ComplexEndCompactification
import TwoAxisHelicoid.ConformalPlaneColumns
import TwoAxisHelicoid.CoordinateTubeHomeomorph
import TwoAxisHelicoid.UnorientedIsothermalChartHarmonic

namespace TwoAxisHelicoid
open Complex Set Filter Metric Matrix
open scoped Topology ContDiff Manifold

/-- In a proper embedded helicoidal C¹ end, an isothermal annulus
marking the infinite end must be a punctured disk. The marking need
only identify which circle the end approaches. -/
theorem helicoid_annular_chart_fills {M : Type*} [TopologicalSpace M] [T2Space M]
    [WeaklyLocallyCompactSpace M] [NoncompactSpace M]
    {X : M → Fin 3 → ℝ} (proper : IsProperMap X) (inj : Function.Injective X)
    (graph : HasHelicoidC1End (coordinateToTube ∘ X)) (e : OpenPartialHomeomorph M ℂ)
    (iso : InducedIsothermalChart X e) {r R : ℝ} (hr : 0≤r) (lt : r<R)
    (target : e.target={z : ℂ | r<‖z‖ ∧ ‖z‖<R}) (core : IsCompact e.sourceᶜ)
    (toRadius : Tendsto (fun x => ‖e x‖) (cocompact M) (𝓝 r)) :
    r=0 ∧ ∃ E : PuncturedComplexEnd M, E.coord=e ∧ E.radius=R := by
  let P := X ∘ e.symm
  let Y := coordinateToTube ∘ P
  let T := coordinateToTube ∘ X
  have hp : IsProperMap T := coordinateToTube_isProperMap proper
  have mem {z : ℂ} (lo : r<‖z‖) (hi : ‖z‖<R) : z∈e.target := target ▸ ⟨lo,hi⟩
  have dP {z : ℂ} (hz : z∈e.target) : DifferentiableAt ℝ P z := (iso.1 z hz).1.differentiableAt (by simp)
  have dY {z : ℂ} (hz : z∈e.target) : HasFDerivAt Y (coordinateToTube.comp (fderiv ℝ P z)) z :=
    coordinateToTube.hasFDerivAt.comp z (dP hz).hasFDerivAt
  have rz : r=0 := by
    apply graph.inner_radius_zero hp.continuous hr lt (Y := Y)
    · intro z lo hi
      exact (dY (mem lo hi)).differentiableAt
    · intro z _ _
      exact mem_range_self (f := T) (e.symm z)
    · intro z hz w hw he
      exact e.symm.injOn (mem hz.1 hz.2) (mem hw.1 hw.2) (inj (coordinateToTube_injective he))
    · intro z lo hi
      have hz := mem lo hi
      let D := fderiv ℝ P z
      obtain ⟨same,orth⟩ := (conformalCoordinateDerivatives_iff_dot (dP hz)).mp (iso.2 z hz)
      refine ⟨D 1 ⬝ᵥ D 1,fun v => ?_⟩
      rw [(dY hz).fderiv,ContinuousLinearMap.comp_apply,tubeCartesian_coordinateToTube]
      rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
      simpa only [dotProduct,sq] using
        spatial_conformal_pairing D same orth v v
    · intro B
      obtain ⟨s,hs,esc⟩ := annular_end_inverse_escapes e hr lt target core toRadius
        (hp.isCompact_preimage (isCompact_closedBall (0:HelicoidTubeCoordinates) B))
      refine ⟨s,hs,fun z lo hi => ?_⟩
      have outside : T (e.symm z)∉closedBall (0:HelicoidTubeCoordinates) B := esc z lo hi
      change B < ‖T (e.symm z)‖
      simpa only [mem_closedBall,dist_zero_right,not_le] using outside
  refine ⟨rz,?_⟩
  subst r
  have target' : e.target=ball (0:ℂ) R \ {0} := by
    rw [target]
    ext z
    change (0<‖z‖ ∧ ‖z‖<R) ↔ (dist z 0<R ∧ z≠0)
    rw [dist_zero_right,norm_pos_iff]
    exact and_comm
  exact ⟨puncturedComplexEndOfChart e lt target' core (tendsto_zero_iff_norm_tendsto_zero.mpr toRadius),rfl,rfl⟩

/-- A holomorphic marking of the annular end induces a complex atlas
on the actual one-point compactification, with a holomorphic inclusion
on the entire original surface. -/
theorem helicoid_annular_holomorphic_compactification {M : Type*} [TopologicalSpace M] [T2Space M]
    [WeaklyLocallyCompactSpace M] [NoncompactSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {X : M → Fin 3 → ℝ} (proper : IsProperMap X) (inj : Function.Injective X)
    (graph : HasHelicoidC1End (coordinateToTube ∘ X)) (e : OpenPartialHomeomorph M ℂ)
    (hol : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) (iso : InducedIsothermalChart X e)
    {r R : ℝ} (hr : 0≤r) (lt : r<R) (target : e.target={z : ℂ | r<‖z‖ ∧ ‖z‖<R})
    (core : IsCompact e.sourceᶜ) (toRadius : Tendsto (fun x => ‖e x‖) (cocompact M) (𝓝 r)) :
    r=0 ∧ ∃ E : PuncturedComplexEnd M, E.coord=e ∧ E.radius=R ∧
      let _ := compactifiedEndAtlas E
      IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some : M → OnePoint M) := by
  obtain ⟨hz,E,coord,rad⟩ := helicoid_annular_chart_fills proper inj graph e iso hr lt target core toRadius
  exact ⟨hz,E,coord,rad,compactifiedEndAtlas_isManifold E (coord ▸ hol),compactifiedEnd_inclusion_contMDiff E⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.helicoid_annular_holomorphic_compactification
