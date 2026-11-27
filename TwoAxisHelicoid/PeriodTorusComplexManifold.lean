import TwoAxisHelicoid.PeriodTorusTopology
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.DiscreteSubset

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold
set_option maxHeartbeats 1000000

theorem periodTorus_exists_inverse_chart (L : PeriodPair) (q : PeriodTorus L) :
    ∃ e : OpenPartialHomeomorph ℂ (PeriodTorus L),
      (e : ℂ → PeriodTorus L) = periodTorusProjection L ∧ q ∈ e.target := by
  obtain ⟨z,hz⟩ := Quotient.exists_rep q
  obtain ⟨e,hze,he⟩ := periodTorusProjection_isLocalHomeomorph L z
  refine ⟨e,he.symm,?_⟩
  have hq : e z = q := by rw [← he]; exact hz
  exact hq ▸ e.map_source hze

noncomputable def periodTorusInverseChart (L : PeriodPair) (q : PeriodTorus L) :
    OpenPartialHomeomorph ℂ (PeriodTorus L) :=
  (periodTorus_exists_inverse_chart L q).choose

theorem periodTorusInverseChart_eq (L : PeriodPair) (q : PeriodTorus L) :
    (periodTorusInverseChart L q : ℂ → PeriodTorus L) = periodTorusProjection L :=
  (periodTorus_exists_inverse_chart L q).choose_spec.1

theorem periodTorusInverseChart_target (L : PeriodPair) (q : PeriodTorus L) :
    q ∈ (periodTorusInverseChart L q).target :=
  (periodTorus_exists_inverse_chart L q).choose_spec.2

/-- The quotient's genuine complex atlas consists of local inverses of the
lattice projection. Its transition functions will be proved translations. -/
noncomputable instance periodTorusChartedSpace (L : PeriodPair) : ChartedSpace ℂ (PeriodTorus L) where
  atlas := {e | (e.symm : ℂ → PeriodTorus L) = periodTorusProjection L}
  chartAt q := (periodTorusInverseChart L q).symm
  mem_chart_source q := periodTorusInverseChart_target L q
  chart_mem_atlas q := periodTorusInverseChart_eq L q

theorem periodTorus_chart_symm_eq_projection (L : PeriodPair) (q : PeriodTorus L) :
    ((chartAt ℂ q).symm : ℂ → PeriodTorus L) = periodTorusProjection L :=
  chart_mem_atlas ℂ q

theorem periodTorus_chart_transition_lattice (L : PeriodPair)
    (e e' : OpenPartialHomeomorph (PeriodTorus L) ℂ)
    (he : (e.symm : ℂ → PeriodTorus L) = periodTorusProjection L)
    (he' : (e'.symm : ℂ → PeriodTorus L) = periodTorusProjection L)
    {z : ℂ} (hz : z ∈ (e.symm.trans e').source) :
    (e.symm.trans e') z-z ∈ L.lattice := by
  apply (periodTorusProjection_eq_zero L _).mp
  change (↑((e.symm.trans e') z-z) : PeriodTorus L) = 0
  rw [QuotientAddGroup.mk_sub]
  have hp : periodTorusProjection L ((e.symm.trans e') z) = periodTorusProjection L z := by
    change periodTorusProjection L (e' (e.symm z)) = periodTorusProjection L z
    have hz' : e.symm z ∈ e'.source := hz.2
    calc
      _ = e'.symm (e' (e.symm z)) := by rw [he']
      _ = e.symm z := e'.left_inv hz'
      _ = _ := congrFun he z
  change periodTorusProjection L ((e.symm.trans e') z)-periodTorusProjection L z = 0
  rw [hp,sub_self]

theorem periodTorus_chart_transition_translation (L : PeriodPair)
    (e e' : OpenPartialHomeomorph (PeriodTorus L) ℂ)
    (he : (e.symm : ℂ → PeriodTorus L) = periodTorusProjection L)
    (he' : (e'.symm : ℂ → PeriodTorus L) = periodTorusProjection L)
    {z : ℂ} (hz : z ∈ (e.symm.trans e').source) :
    ∀ᶠ w in 𝓝 z, (e.symm.trans e') w = w+((e.symm.trans e') z-z) := by
  let T := e.symm.trans e'
  have hm := periodTorus_chart_transition_lattice L e e' he he' hz
  have hd : IsDiscrete (L.lattice : Set ℂ) :=
    isDiscrete_iff_discreteTopology.mpr (inferInstanceAs (DiscreteTopology L.lattice))
  have ht : Tendsto (fun w : ℂ => T w-w) (𝓝 z) (𝓝[L.lattice] (T z-z)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(T.continuousAt hz).sub continuousAt_id,?_⟩
    filter_upwards [T.open_source.mem_nhds hz] with w hw
    exact periodTorus_chart_transition_lattice L e e' he he' hw
  rw [hd.nhdsWithin _ hm] at ht
  filter_upwards [tendsto_pure.mp ht] with w hw
  dsimp only [T] at hw ⊢
  linear_combination hw

theorem periodTorus_chart_transition_analytic (L : PeriodPair)
    (e e' : OpenPartialHomeomorph (PeriodTorus L) ℂ)
    (he : e ∈ atlas ℂ (PeriodTorus L)) (he' : e' ∈ atlas ℂ (PeriodTorus L))
    {z : ℂ} (hz : z ∈ (e.symm.trans e').source) : AnalyticAt ℂ (e.symm.trans e') z := by
  apply (analyticAt_id.add (analyticAt_const (v := (e.symm.trans e') z-z))).congr
  filter_upwards [periodTorus_chart_transition_translation L e e' he he' hz] with w hw
  exact hw.symm

noncomputable instance periodTorusComplexManifold (L : PeriodPair) :
    IsManifold 𝓘(ℂ) ω (PeriodTorus L) := by
  apply isManifold_of_contDiffOn
  intro e e' he he' z hz
  have h := (periodTorus_chart_transition_analytic L e e' he he' hz.1).contDiffAt (n := ω)
  exact h.contDiffWithinAt

noncomputable instance periodTorusRealAnalyticManifold (L : PeriodPair) :
    IsManifold 𝓘(ℝ, ℂ) ω (PeriodTorus L) := by
  apply isManifold_of_contDiffOn
  intro e e' he he' z hz
  have h := ((periodTorus_chart_transition_analytic L e e' he he' hz.1).restrictScalars
    (𝕜 := ℝ)).contDiffAt (n := ω)
  exact h.contDiffWithinAt

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.periodTorusComplexManifold
#print axioms TwoAxisHelicoid.periodTorusRealAnalyticManifold
