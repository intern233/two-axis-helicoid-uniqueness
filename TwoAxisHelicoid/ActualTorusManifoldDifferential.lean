import TwoAxisHelicoid.ActualTorusManifoldImmersion
import Mathlib.Geometry.Manifold.ImmersionDiff

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold
set_option maxHeartbeats 1000000

theorem puncturedPeriodTorus_chart_representative (L : PeriodPair) (q : PuncturedPeriodTorus L) :
    periodTorusProjection L (chartAt ℂ q q) = q.1 :=
  periodTorus_chart_representative L q.1

theorem puncturedPeriodTorus_chart_not_lattice (L : PeriodPair) (q : PuncturedPeriodTorus L) :
    chartAt ℂ q q ∉ L.lattice := by
  intro h
  exact q.2 ((puncturedPeriodTorus_chart_representative L q).symm.trans
    ((periodTorusProjection_eq_zero L _).mpr h))

/-- Compute the actual manifold derivative of the descended immersion in
the chosen quotient atlas. -/
theorem actualPuncturedTorusImmersion_hasMFDerivAt {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0)
    (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) :
    HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 3 → ℝ)
      (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) => actualTorusImmersion ht ha hc hG hH q.1) q
      (nullRealDerivative (coordinateData t a c ht (chartAt ℂ q q))) := by
  let L := rhombicPeriodPair t ht
  let z := chartAt ℂ q q
  have hz : z ∉ L.lattice := puncturedPeriodTorus_chart_not_lattice L q
  have hcharts := TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq
    (H := ℂ) (puncturedPeriodTorusOpen L) (x := q)
  have he : (fun w : ℂ => actualTorusImmersion ht ha hc hG hH ((chartAt ℂ q).symm w).1) =ᶠ[𝓝 z]
      actualGlobalImmersion t a c ht := by
    filter_upwards [hcharts] with w hw
    dsimp only [Function.comp_def] at hw
    calc
      _ = actualTorusImmersion ht ha hc hG hH ((chartAt ℂ q.1).symm w) := by
        simpa only using! congrArg (actualTorusImmersion ht ha hc hG hH) hw.symm
      _ = _ := by
        rw [periodTorus_chart_symm_eq_projection L q.1]
        rfl
  have hd := (((actual_global_conformal_harmonic_immersion ht ha hc hG hH).2.2.2 z hz).1).congr_of_eventuallyEq he
  refine ⟨(actualPuncturedTorusImmersion_contMDiff ht ha hc hG hH).continuous.continuousAt,?_⟩
  simpa only [writtenInExtChartAt,mfld_simps] using! hd.hasFDerivWithinAt (s := range 𝓘(ℝ, ℂ))

theorem actualPuncturedTorusImmersion_mfderiv_injective {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0)
    (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) :
    Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 3 → ℝ)
      (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) => actualTorusImmersion ht ha hc hG hH q.1) q) := by
  rw [(actualPuncturedTorusImmersion_hasMFDerivAt ht ha hc hG hH q).mfderiv]
  have hz := puncturedPeriodTorus_chart_not_lattice (rhombicPeriodPair t ht) q
  exact nullRealDerivative_injective (coordinateData_null ht ha hz) (coordinateData_ne_zero ht ha hc hz)

theorem actualPuncturedTorusImmersion_isDiffImmersionAt {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0)
    (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) :
    IsDiffImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 3 → ℝ)
      (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) => actualTorusImmersion ht ha hc hG hH q.1) q := by
  apply IsDiffImmersionAt.of_injective_of_finiteDimensional
  exact actualPuncturedTorusImmersion_mfderiv_injective ht ha hc hG hH q

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualPuncturedTorusImmersion_hasMFDerivAt
#print axioms TwoAxisHelicoid.actualPuncturedTorusImmersion_isDiffImmersionAt
