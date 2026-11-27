import TwoAxisHelicoid.UnmarkedPhysicalAxisPlacement
import TwoAxisHelicoid.OriginalGeometricPoleFrame
import TwoAxisHelicoid.NormalizedGeometricExteriorCoordinate
import TwoAxisHelicoid.PhysicalGraphPunctureFilling

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology
open scoped Topology ContDiff Manifold

/-- Align the physical poles in the original puncture chart by the two
actual positional asymptotes. No period torus and no uniformization of
the compactification are used. -/
theorem positional_double_pole_end_in_original_frame {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {X : M → Fin 3 → ℝ} (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d)
    (A : GeometricDoublePoleInSomeFrame X) {α : ℝ} (non : α≠0)
    (approaches : ApproachesSetAtInfinity (range X) (range (axisRuledHelicoid I α 0))) :
    Nonempty (GeometricDoublePoleEnd X) := by
  let Z := fun x => A.offset+A.frame (X x)
  let R := A.frame.symm
  let P := -(R A.offset)
  let U := A.exterior
  let d := U.endChart.coord
  have orth (u v : Fin 3 → ℝ) : R u ⬝ᵥ R v=u ⬝ᵥ v := by
    simpa only [R,LinearEquiv.apply_symm_apply] using (A.orthogonal (R u) (R v)).symm
  have identity (x : M) : P+R (Z x)=X x := by simp [P,R,Z]
  have image : (fun p => P+R p) '' range Z=range X := by
    rw [← range_comp]
    exact congrArg range (funext identity)
  have approach := A.approaching.affine_image R.toContinuousLinearEquiv.toContinuousLinearMap P
  change ApproachesSetAtInfinity ((fun p => P+R p) '' range (axisRuledHelicoid I A.pitch 0))
    ((fun p => P+R p) '' range Z) at approach
  rw [image] at approach
  have chart := harmonic_immersion_chart_maximal (orthogonal_affine_harmonic_charts X charts A.frame A.orthogonal A.offset) U.holomorphic
  have domain : d.target∈𝓝[≠] (0:ℂ) := by
    rw [show d.target=Metric.ball (0:ℂ) U.endChart.radius \ {0} from U.endChart.target_eq]
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ U.endChart.radius_pos)) self_mem_nhdsWithin
  have regular : ∀ᶠ w in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ (Z ∘ d.symm) w ∧
      ComplexNull (immersionComplexCoefficient (Z ∘ d.symm) w) ∧
      ∀ j, AnalyticAt ℂ (fun y => immersionComplexCoefficient (Z ∘ d.symm) y j) w := by
    filter_upwards [domain] with w hw
    obtain ⟨hh,hc,_⟩ := chart w hw
    exact ⟨(analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hh j)).differentiableAt,
      immersionComplexCoefficient_null hc,fun j => scalarComplexCoefficient_analyticAt (hh j)⟩
  have data := asymptotic_helicoid_actual_end_double_poles R.toLinearMap orth P α A.pitch non A.nonzero
    approach approaches (Z ∘ d.symm) 0 regular U.height U.heightOrder U.gauss U.gaussOrder
  let placed := fun x => P+R (Z x)
  let D : GeometricDoublePoleEnd placed := ⟨U.endChart,U.holomorphic,data.1,data.2.1,data.2.2.1,data.2.2.2⟩
  have eq : placed=X := funext identity
  exact ⟨eq ▸ D⟩

/-- A compactified physical end with the two pole orders in the frame
of its own helicoidal asymptote determines a normalized height chart
in the original frame of the axes, for every genus. -/
theorem external_frame_poles_give_physical_exterior {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [PreconnectedSpace M] {X : M → Fin 3 → ℝ}
    (emb : IsClosedEmbedding X) (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d)
    (axes : OriginalHelicoidAxes (range X)) (approaches : ApproachesSetAtInfinity (range X) (range (axisRuledHelicoid I axes.pitch 0)))
    (A : GeometricDoublePoleInSomeFrame X) :
    ∃ E : GeometricExteriorCoordinate X, E.correction 0=0 := by
  obtain ⟨U⟩ := positional_double_pole_end_in_original_frame charts A axes.pitch_ne approaches
  obtain ⟨D⟩ := original_positional_poles_give_exterior emb charts axes approaches U
  obtain ⟨G,_,zero⟩ := D.normalized emb.continuous U.endChart.connected_tails
  exact ⟨G,zero⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_double_pole_end_in_original_frame
#print axioms TwoAxisHelicoid.external_frame_poles_give_physical_exterior
