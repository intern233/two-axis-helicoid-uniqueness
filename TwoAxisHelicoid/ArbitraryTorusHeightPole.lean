import TwoAxisHelicoid.PeriodicPuncturePrimitive
import TwoAxisHelicoid.MarkedHelicoidHeightPole
import TwoAxisHelicoid.AnnularEndSeparation

namespace TwoAxisHelicoid
open Complex Set Filter Metric InnerProductSpace
open scoped Topology

/-- Each physical coordinate of any harmonic torus map admits a
single-valued complex primitive at the puncture with the correct
real part. Neither reflection invariance nor meromorphicity is used. -/
theorem torus_coordinate_puncture_primitive (L : PeriodPair) (Y : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hh : ∀ z∉L.lattice, ∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) (j : Fin 3) :
    ∃ H : ℂ → ℂ, ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt H (torusImmersionForms L Y z j) z ∧ (H z).re=puncturedTorusPullback L Y z j := by
  let X := puncturedTorusPullback L Y
  let f := fun z => torusImmersionForms L Y z j
  obtain ⟨F,ev⟩ := single_lattice_puncture_local_primitive L f (fun z hz => (scalarComplexCoefficient_analyticAt (hh z hz j)).differentiableAt)
    (fun z v h => congrFun (torusImmersionForms_periodic L Y z v h) j)
  obtain ⟨r,hr,sub⟩ := Metric.mem_nhdsWithin_iff.mp (ev.and (punctured_lattice_regular_near_zero L))
  let V := {z : ℂ | 0<‖z‖ ∧ ‖z‖<r}
  have op : IsOpen V := (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have atV (z : ℂ) (hz : z∈V) := sub (show z∈ball (0:ℂ) r ∩ {0}ᶜ from
    ⟨by simpa only [mem_ball,dist_zero_right] using hz.2,norm_pos_iff.mp hz.1⟩)
  have dX (z : ℂ) (hz : z∈V) : HasFDerivAt (fun w => X w j) (realCoefficientDerivative (f z)) z :=
    scalarComplexCoefficient_hasFDerivAt ((hh z (atV z hz).2 j).1.differentiableAt two_ne_zero)
  have dF (z : ℂ) (hz : z∈V) : HasFDerivAt (fun w => (F w).re) (realCoefficientDerivative (f z)) z :=
    Complex.reCLM.hasFDerivAt.comp z ((atV z hz).1.hasFDerivAt.restrictScalars ℝ)
  obtain ⟨b,eq⟩ := op.exists_eq_add_of_fderiv_eq (complex_open_annulus_isPreconnected (r := 0) (R := r) le_rfl)
    (fun z hz => (dX z hz).differentiableAt.differentiableWithinAt) (fun z hz => (dF z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (dX z hz).fderiv.trans (dF z hz).fderiv.symm)
  refine ⟨fun z => F z+(b:ℂ),?_⟩
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) hr)] with z n h
  have hz : z∈V := ⟨norm_pos_iff.mpr n,by simpa only [mem_ball,dist_zero_right] using h⟩
  exact ⟨((atV z hz).1).add_const _,(eq hz).symm⟩

theorem arbitrary_torus_isothermal_end_chart (L : PeriodPair) (Y : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (reg : ∀ z∉L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z ∧ Function.Injective (fderiv ℝ (puncturedTorusPullback L Y) z)) :
    ∃ E : PuncturedComplexEnd (PuncturedPeriodTorus L), let X := coordinateToTube ∘ Y
      (X ∘ E.coord.symm =ᶠ[𝓝[≠] (0:ℂ)] coordinateToTube ∘ puncturedTorusPullback L Y) ∧
      (∀ᶠ z in 𝓝[≠] (0:ℂ), ContDiffAt ℝ 1 (X ∘ E.coord.symm) z) ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), ∃ c : ℝ, 0<c ∧ ∀ v : ℂ,
        (∑ j, (tubeCartesian (fderiv ℝ (X ∘ E.coord.symm) z v) j)^2)=c*‖v‖^2 := by
  let X := puncturedTorusPullback L Y
  obtain ⟨E,proj⟩ := marked_torus_puncture_coordinate L
  have eq : (coordinateToTube ∘ Y) ∘ E.coord.symm =ᶠ[𝓝[≠] (0:ℂ)] coordinateToTube ∘ X := by
    filter_upwards [punctured_lattice_regular_near_zero L,self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) E.radius_pos)] with z reg nz small
    have e : E.coord.symm z=puncturedPlaneProjection L ⟨z,reg⟩ := Subtype.ext (proj z (E.mem_target_of_ball_ne small nz))
    change coordinateToTube (Y (E.coord.symm z))=coordinateToTube (puncturedTorusPullback L Y z)
    rw [e]
    simp [puncturedTorusPullback,reg]
  refine ⟨E,eq,?_⟩
  apply Filter.eventually_and.mp
  filter_upwards [punctured_lattice_regular_near_zero L,punctured_germ_eventually_local eq] with z hz same
  have analytic : AnalyticAt ℝ X z := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt ((reg z hz).1 j)
  let p := immersionComplexCoefficient X z
  have diff := immersionComplexCoefficient_hasFDerivAt analytic.differentiableAt
  have hD := coordinateToTube.hasFDerivAt.comp z diff
  have null := immersionComplexCoefficient_null (reg z hz).2.1
  have non := immersionComplexCoefficient_regular analytic.differentiableAt (reg z hz).2.2
  refine ⟨(coordinateToTube.contDiff.contDiffAt.comp z analytic.contDiffAt).congr_of_eventuallyEq same,
    nullMetric p,nullMetric_pos null non,?_⟩
  intro v
  rw [same.fderiv_eq,hD.fderiv,ContinuousLinearMap.comp_apply,tubeCartesian_coordinateToTube]
  have n := nullRealDerivative_euclidean_norm_sq null v
  rwa [EuclideanSpace.real_norm_sq_eq] at n

/-- For any one-handled helicoidal normal graph, the height form has
a double pole in a marked compact torus. There are no straight-line,
involution or interior embeddedness assumptions. -/
theorem arbitrary_torus_graph_height_pole (L : PeriodPair) (Y : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (proper : IsProperMap Y) (graph : HasHelicoidC1End (coordinateToTube ∘ Y))
    (reg : ∀ z∉L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z ∧ Function.Injective (fderiv ℝ (puncturedTorusPullback L Y) z)) :
    MeromorphicAt (fun z => torusImmersionForms L Y z 2) 0 ∧
      meromorphicOrderAt (fun z => torusImmersionForms L Y z 2) 0=(-2:ℤ) := by
  let := punctured_complex_curve_noncompact (0:PeriodTorus L)
  let : LocallyCompactSpace (PuncturedPeriodTorus L) := ChartedSpace.locallyCompactSpace ℂ _
  obtain ⟨E,eq,sm,iso⟩ := arbitrary_torus_isothermal_end_chart L Y reg
  obtain ⟨H,ev⟩ := torus_coordinate_puncture_primitive L Y (fun z hz => (reg z hz).1) 2
  have height : ∀ᶠ z in 𝓝[≠] (0:ℂ), ((coordinateToTube ∘ Y) (E.coord.symm z)).2=(H z).re+0 := by
    filter_upwards [eq,ev] with z c h
    exact (congrArg Prod.snd c).trans (by change puncturedTorusPullback L Y z 2=(H z).re+0; rw [h.2,add_zero])
  obtain ⟨_,_,mer,ord⟩ := graph.intrinsic_height_orders (coordinateToTube_isProperMap proper) E sm iso height (ev.mono fun _ h => h.1.differentiableAt)
  have de := ev.mono fun _ h => h.1.deriv
  exact ⟨mer.congr de,(meromorphicOrderAt_congr de).symm.trans ord⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.arbitrary_torus_graph_height_pole
