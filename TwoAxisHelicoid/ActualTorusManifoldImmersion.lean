import TwoAxisHelicoid.PeriodTorusComplexManifold
import TwoAxisHelicoid.ActualTorusImmersion
import Mathlib.Geometry.Manifold.ContMDiff.Basic

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold
set_option maxHeartbeats 1000000

noncomputable instance periodTorusManifoldT2Space (L : PeriodPair) : T2Space (PeriodTorus L) := by
  let : T1Space (PeriodTorus L) := QuotientAddGroup.t1Space_iff.mpr L.isClosed_lattice
  infer_instance

noncomputable instance periodTorusManifoldCompactSpace (L : PeriodPair) : CompactSpace (PeriodTorus L) :=
  periodTorus_compactSpace L

def puncturedPeriodTorusOpen (L : PeriodPair) : TopologicalSpace.Opens (PeriodTorus L) :=
  ⟨{q | q ≠ 0},isOpen_ne⟩

noncomputable instance puncturedPeriodTorusChartedSpace (L : PeriodPair) :
    ChartedSpace ℂ (PuncturedPeriodTorus L) :=
  inferInstanceAs (ChartedSpace ℂ (puncturedPeriodTorusOpen L))

noncomputable instance puncturedPeriodTorusComplexManifold (L : PeriodPair) :
    IsManifold 𝓘(ℂ) ω (PuncturedPeriodTorus L) :=
  inferInstanceAs (IsManifold 𝓘(ℂ) ω (puncturedPeriodTorusOpen L))

noncomputable instance puncturedPeriodTorusRealAnalyticManifold (L : PeriodPair) :
    IsManifold 𝓘(ℝ, ℂ) ω (PuncturedPeriodTorus L) :=
  inferInstanceAs (IsManifold 𝓘(ℝ, ℂ) ω (puncturedPeriodTorusOpen L))

theorem periodTorus_chart_representative (L : PeriodPair) (q : PeriodTorus L) :
    periodTorusProjection L (chartAt ℂ q q) = q := by
  rw [← periodTorus_chart_symm_eq_projection L q]
  exact (chartAt ℂ q).left_inv (mem_chart_source ℂ q)

/-- The descended coordinate map is real analytic in the actual quotient
manifold structure, rather than only in an existential coordinate chart. -/
theorem actualTorusImmersion_contMDiffAt {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0)
    {q : PeriodTorus (rhombicPeriodPair t ht)} (hq : q ≠ 0) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 3 → ℝ) ω (actualTorusImmersion ht ha hc hG hH) q := by
  let L := rhombicPeriodPair t ht
  let z := chartAt ℂ q q
  have hp : periodTorusProjection L z = q := periodTorus_chart_representative L q
  have hz : z ∉ L.lattice := fun h => hq (hp.symm.trans ((periodTorusProjection_eq_zero L z).mpr h))
  have hF := (actual_global_conformal_harmonic_immersion ht ha hc hG hH).2.1 z hz
  have hcomp : actualTorusImmersion ht ha hc hG hH ∘ (chartAt ℂ q).symm =
      actualGlobalImmersion t a c ht := by
    rw [periodTorus_chart_symm_eq_projection L q]
    rfl
  apply contMDiffAt_iff.mpr
  refine ⟨?_,?_⟩
  · rw [← hp]
    exact periodTorusLift_continuousAt L (actualGlobalImmersion t a c ht)
      (actualGlobalImmersion_add_lattice ht ha hc hG hH) hF.continuousAt
  · have hh : ContDiffAt ℝ ω (actualTorusImmersion ht ha hc hG hH ∘ (chartAt ℂ q).symm) z := by
      rw [hcomp]
      exact hF.contDiffAt
    simpa only [mfld_simps] using! hh.contDiffWithinAt (s := range 𝓘(ℝ, ℂ))

theorem actualPuncturedTorusImmersion_contMDiff {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 3 → ℝ) ω
      (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) => actualTorusImmersion ht ha hc hG hH q.1) := by
  intro q
  exact (actualTorusImmersion_contMDiffAt ht ha hc hG hH q.2).comp q
    (contMDiff_subtype_val (U := puncturedPeriodTorusOpen (rhombicPeriodPair t ht))).contMDiffAt

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualPuncturedTorusImmersion_contMDiff
