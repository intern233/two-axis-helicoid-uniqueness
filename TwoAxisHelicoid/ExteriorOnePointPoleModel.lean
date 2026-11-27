import TwoAxisHelicoid.RawPublishedConformalPoleReduction
import TwoAxisHelicoid.OriginalGeometricExteriorInput
import TwoAxisHelicoid.MaximalHarmonicImmersionChart
import TwoAxisHelicoid.ExteriorHeightGaussPoles

namespace TwoAxisHelicoid
open Complex Set Filter Metric Bornology Topology
open scoped Topology ContDiff Manifold

private theorem finite_part_isothermal {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {X : M → Fin 3 → ℝ}
    (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d) (E : PuncturedComplexEnd M)
    (hol : E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) :
    let _ := compactifiedEndAtlas E
    IsothermalAwayFromPoint (fun q : OnePoint M => q.elim 0 X) OnePoint.infty := by
  let _ := compactifiedEndAtlas E
  change IsothermalAwayFromPoint (fun q : OnePoint M => q.elim 0 X) OnePoint.infty
  intro c hc w hw finite
  change (∃ e∈atlas ℂ M, c=finiteOnePointChart e) ∨ c=E.filledChart at hc
  rcases hc with ⟨e,member,rfl⟩|rfl
  · obtain ⟨harm,conf,imm⟩ := charts e member w hw
    exact ⟨(analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (harm j)).contDiffAt,imm,conf⟩
  · have nz : w≠0 := fun zero => finite (by change E.filledInverse w=OnePoint.infty; simp [zero,PuncturedComplexEnd.filledInverse])
    obtain ⟨harm,conf,imm⟩ := harmonic_immersion_chart_maximal charts hol w (E.mem_target_of_ball_ne hw nz)
    let Z := (fun q : OnePoint M => q.elim 0 X) ∘ E.filledChart.symm
    have eq : Z=ᶠ[𝓝 w] X ∘ E.coord.symm := by
      filter_upwards [eventually_ne_nhds nz] with v hv
      change (E.filledInverse v).elim 0 X=X (E.coord.symm v)
      simp [PuncturedComplexEnd.filledInverse,hv]
    have sm : ContDiffAt ℝ ∞ (X ∘ E.coord.symm) w := (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (harm j)).contDiffAt
    have sZ := sm.congr_of_eventuallyEq eq
    refine ⟨sZ,?_,?_⟩
    · rw [show fderiv ℝ Z w=fderiv ℝ (X ∘ E.coord.symm) w from eq.fderiv_eq]
      exact imm
    · apply (conformalCoordinateDerivatives_iff_dot (sZ.differentiableAt (by simp))).mpr
      rw [eq.fderiv_eq (𝕜 := ℝ)]
      exact (conformalCoordinateDerivatives_iff_dot (sm.differentiableAt (by simp))).mp conf

/-- The analytic exterior in any rigid frame builds a compact Riemann
surface on the actual one-point compactification. Its finite marking
preserves the physical immersion, and its two order-minus-two germs are
the derivatives of that very map in the compactifying chart. -/
theorem exterior_frame_constructs_compact_pole_model {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {X : M → Fin 3 → ℝ} (cx : Continuous X)
    (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d) (tails : HasConnectedCompactTails M)
    (A : GeometricExteriorInSomeFrame X) : Nonempty (PublishedConformalPoleModel X) := by
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℂ M
  let Y := fun x => A.offset+A.frame (X x)
  have cy : Continuous Y := continuous_const.add (A.frame.toContinuousLinearEquiv.continuous.comp cx)
  let G := A.exterior
  have height : Continuous (fun x => Y x 2) := (continuous_apply _).comp cy
  let _ : NoncompactSpace M := noncompact_of_exterior_height G.chart G.target _ height G.heightOffset G.height
  have esc := true_exterior_height_coordinate_escapes tails G.chart G.target G.core _ height G.heightOffset G.height
  let E := exteriorCoordinateComplexEnd G.chart G.positive G.target G.core esc
  let _ := compactifiedEndAtlas E
  let _ : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) :=
    (exteriorCoordinate_fills_complex_manifold G.chart G.positive G.target G.core esc G.holomorphic).1
  let inc := fun x : M => (⟨(x : OnePoint M),OnePoint.coe_ne_infty x⟩ : {q : OnePoint M // q≠OnePoint.infty})
  have onto : Function.Surjective inc := by
    intro q
    obtain ⟨x,h⟩ := OnePoint.ne_infty_iff_exists.mp q.2
    exact ⟨x,Subtype.ext h⟩
  let mark := (OnePoint.isOpenEmbedding_coe.isEmbedding.codRestrict _ OnePoint.coe_ne_infty).toHomeomorphOfSurjective onto
  have ycharts := orthogonal_affine_harmonic_charts X charts A.frame A.orthogonal A.offset
  have reg := exterior_immersion_eventually_differentiable Y ycharts G.holomorphic G.target
  have hh : ∀ᶠ ζ in cobounded ℂ, Y (G.chart.symm ζ) 2=G.heightOffset+ζ.re := by
    filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop G.radius)] with ζ hz
    have inside : ζ∈G.chart.target := G.target ▸ hz
    change (A.offset+A.frame (X (G.chart.symm ζ))) 2=_
    rw [G.height _ (G.chart.map_target inside),G.chart.right_inv inside]
  obtain ⟨h,ho,g,go⟩ := compactified_exterior_surface_end_poles Y G.chart G.positive G.target G.core esc
    G.heightOffset G.pitch G.pitch_ne G.correction G.analytic reg hh G.gauss (A.offset+A.frame 0)
  let S := fun q : OnePoint M => q.elim 0 X
  have frame : (fun q => A.offset+A.frame (S q))=(fun q : OnePoint M => q.elim (A.offset+A.frame 0) Y) := by
    funext q
    cases q using OnePoint.rec <;> rfl
  refine ⟨{
    model := OnePoint M
    point := OnePoint.infty
    marking := mark
    spatial := S
    agrees := fun _ => rfl
    isothermal := finite_part_isothermal charts E (reciprocalExteriorChart_mem_maximalAtlas G.chart G.positive G.target G.holomorphic)
    frame := A.frame
    orthogonal := A.orthogonal
    offset := A.offset
    chart := E.filledChart
    holomorphic := IsManifold.subset_maximalAtlas (show E.filledChart∈atlas ℂ (OnePoint M) from Or.inr rfl)
    end_mem := ?_
    centered := rfl
    height := ?_
    heightOrder := ?_
    gauss := ?_
    gaussOrder := ?_
    pitch := A.pitch
    pitch_ne := A.nonzero
    asymptote := A.approaching }⟩
  · rintro ⟨x,_,eq⟩
    exact OnePoint.coe_ne_infty x eq
  all_goals rw [frame]
  · exact h
  · exact ho
  · exact g
  · exact go

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exterior_frame_constructs_compact_pole_model
