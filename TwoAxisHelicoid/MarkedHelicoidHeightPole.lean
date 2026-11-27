import TwoAxisHelicoid.MarkedTorusPunctureCoordinate
import TwoAxisHelicoid.HelicoidIntrinsicHeightOrders
import TwoAxisHelicoid.HarmonicTorusComplexHeights
import TwoAxisHelicoid.HarmonicTorusC1Normalization
import TwoAxisHelicoid.CoordinateTubeHomeomorph
import TwoAxisHelicoid.TorusEndScalingOrders

namespace TwoAxisHelicoid
open Complex Set Filter InnerProductSpace
open scoped Topology

theorem TwoAxisHarmonicConformalImmersion.standard_end_chart {L : PeriodPair}
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion L X) :
    ∃ E : PuncturedComplexEnd (PuncturedPeriodTorus L),
    let Y := coordinateToTube ∘ harmonicTorusImmersion hX
    (Y ∘ E.coord.symm =ᶠ[𝓝[≠] (0:ℂ)] coordinateToTube ∘ X) ∧
    (∀ᶠ z in 𝓝[≠] (0:ℂ), ContDiffAt ℝ 1 (Y ∘ E.coord.symm) z) ∧
    ∀ᶠ z in 𝓝[≠] (0:ℂ), ∃ c : ℝ, 0<c ∧ ∀ v : ℂ,
      (∑ j, (tubeCartesian (fderiv ℝ (Y ∘ E.coord.symm) z v) j)^2)=c*‖v‖^2 := by
  obtain ⟨E,proj⟩ := marked_torus_puncture_coordinate L
  let Y := coordinateToTube ∘ harmonicTorusImmersion hX
  have eq : Y ∘ E.coord.symm =ᶠ[𝓝[≠] (0:ℂ)] coordinateToTube ∘ X := by
    filter_upwards [punctured_lattice_regular_near_zero L,self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0:ℂ) E.radius_pos)] with z reg nz small
    have e : E.coord.symm z=⟨periodTorusProjection L z,(periodTorusProjection_eq_zero L z).not.mpr reg⟩ :=
      Subtype.ext (proj z (E.mem_target_of_ball_ne small nz))
    change coordinateToTube (harmonicTorusImmersion hX (E.coord.symm z))=coordinateToTube (X z)
    rw [e,harmonicTorusImmersion_projection hX reg]
  refine ⟨E,eq,?_⟩
  apply Filter.eventually_and.mp
  filter_upwards [punctured_lattice_regular_near_zero L,punctured_germ_eventually_local eq] with z hz same
  have sg : ContDiffAt ℝ 1 X z := (analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (hX.harmonic z hz j))).contDiffAt
  let p := immersionComplexCoefficient X z
  have dn := immersionComplexCoefficient_hasFDerivAt (hX.differentiable z hz)
  have hd := coordinateToTube.hasFDerivAt.comp z dn
  have hp : ComplexNull p := immersionComplexCoefficient_null (hX.conformal z hz)
  have hn := immersionComplexCoefficient_regular (hX.differentiable z hz) (hX.immersion z hz)
  refine ⟨(coordinateToTube.contDiff.contDiffAt.comp z sg).congr_of_eventuallyEq same,
    nullMetric p,nullMetric_pos hp hn,?_⟩
  intro v
  rw [same.fderiv_eq,hd.fderiv,ContinuousLinearMap.comp_apply,tubeCartesian_coordinateToTube]
  have n := nullRealDerivative_euclidean_norm_sq hp v
  rwa [EuclideanSpace.real_norm_sq_eq] at n

/-- The physical C¹ graph and proper harmonic marked immersion force the
actual coefficient of dh to have a double pole. All local primitives,
isothermal factors, growth estimates and the exact pole order are
derived from the given surface. -/
theorem marked_helicoid_height_double_pole {t : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (proper : IsProperMap (harmonicTorusImmersion hX))
    (graph : HasHelicoidC1End (coordinateToTube ∘ harmonicTorusImmersion hX)) :
    MeromorphicAt (fun z => puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2) 0 ∧
      meromorphicOrderAt (fun z => puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2) 0=((-2:ℤ):WithTop ℤ) := by
  let L := rhombicPeriodPair t ht
  let := punctured_complex_curve_noncompact (0:PeriodTorus L)
  let : LocallyCompactSpace (PuncturedPeriodTorus L) := ChartedSpace.locallyCompactSpace ℂ _
  obtain ⟨E,eq,sm,iso⟩ := hX.standard_end_chart
  obtain ⟨H,d⟩ := hX.complex_coordinate_primitive ht 2
  have ev := (punctured_lattice_regular_near_zero L).mono d
  have height : ∀ᶠ z in 𝓝[≠] (0:ℂ), ((coordinateToTube ∘ harmonicTorusImmersion hX) (E.coord.symm z)).2=(H z).re+0 := by
    filter_upwards [eq,ev] with z c h
    exact (congrArg Prod.snd c).trans (by change X z 2=(H z).re+0; rw [h.2,add_zero])
  obtain ⟨_,_,mer,order⟩ := graph.intrinsic_height_orders (coordinateToTube_isProperMap proper) E sm iso height
    (ev.mono fun _ h => h.1.differentiableAt)
  have de := ev.mono fun z h => h.1.deriv
  exact ⟨mer.congr de,(meromorphicOrderAt_congr de).symm.trans order⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_helicoid_height_double_pole
