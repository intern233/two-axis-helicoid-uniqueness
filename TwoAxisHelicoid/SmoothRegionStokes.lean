import TwoAxisHelicoid.SmoothRegionChartPartition
import TwoAxisHelicoid.FiniteRegionChartLocalization

namespace TwoAxisHelicoid
open Complex MeasureTheory Filter Set Topology Function
open scoped Topology ContDiff Manifold Interval

namespace CurveRegionPartition
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {Ω : Set M}

/-- Integrate a real coordinate area density using the actual compact
chart cutoffs on the specified physical region. -/
noncomputable def areaIntegral (Q : CurveRegionPartition Ω) (A : Q.indices → ℂ → ℝ) : ℝ :=
  ∑ i, ∫ z in curveChartRegion (Q.chart i) Ω, Q.weight i ((Q.chart i).symm z)*A i z

/-- The chart sum of oriented integrals on the physical boundary. Each
interior chart contributes zero, while a boundary chart integrates along
its genuine defining curve with its surface cutoff. -/
noncomputable def boundaryIntegral (Q : CurveRegionPartition Ω) (a : Q.indices → ℂ → ℂ) : ℝ :=
  ∑ i, (Q.patch i).flux (fun z => (Q.weight i ((Q.chart i).symm z):ℂ)*a i z)

/-- Stokes' formula on an arbitrary relatively compact smooth region of
a Riemann surface, with its induced boundary orientation. Regularity of
the coefficients and their holomorphic transition rule are the only
differential assumptions on the one-form. -/
theorem imaginary_stokes [IsManifold 𝓘(ℂ,ℂ) ω M] (Q : CurveRegionPartition Ω) (op : IsOpen Ω)
    (a : Q.indices → ℂ → ℂ) (smooth : ∀ i z, z∈(Q.chart i).target → ContDiffAt ℝ 1 (a i) z)
    (changeChart : ∀ i j z, z∈((Q.chart i).symm.trans (Q.chart j)).source →
      a i z=a j (((Q.chart i).symm.trans (Q.chart j)) z)*deriv ((Q.chart i).symm.trans (Q.chart j)) z) :
    Q.areaIntegral (fun i z => (complexFormExteriorCoefficient (a i) z).im)=Q.boundaryIntegral a := by
  classical
  have sub i := (Q.supported i).trans (Q.patch i).carrier_subset_source
  have cut i j z (hz : z∈(Q.chart i).target) := real_cutoff_in_complex_chart (Q.weight j)
    (Q.smooth j) (Q.member i) hz
  have localized := finite_region_exterior_localization op Q.chart Q.weight a
    (fun x hx => Q.unity x (subset_closure hx)) (fun i => (Q.smooth i).continuous)
    Q.compact sub cut smooth
    (fun i j z hz => (complexAtlas_realized_transition (Q.member i) (Q.member j) hz).analyticAt)
    changeChart
  have integ i := (chart_weighted_density_integrable (Q.chart i) (Q.smooth i).continuous (Q.compact i)
    (sub i) (complexFormExteriorCoefficient_continuousOn (smooth i))).mono_set
    (show curveChartRegion (Q.chart i) Ω⊆(Q.chart i).target from inter_subset_left)
  calc
    _=(∑ i, ∫ z in curveChartRegion (Q.chart i) Ω,
      Q.weight i ((Q.chart i).symm z) • complexFormExteriorCoefficient (a i) z).im := by
        rw [Complex.im_sum]
        apply Finset.sum_congr rfl
        intro i _
        simpa only [Function.comp_def,Complex.imCLM_apply,Complex.smul_im,smul_eq_mul] using
          Complex.imCLM.integral_comp_comm (integ i)
    _=Q.boundaryIntegral a := by
      rw [localized,Complex.im_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (Q.patch i).cutoff_flux op (Q.compact i) (Q.supported i)
        (fun z hz => (cut i i z hz).mul (smooth i z hz))

end CurveRegionPartition
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.CurveRegionPartition.imaginary_stokes

