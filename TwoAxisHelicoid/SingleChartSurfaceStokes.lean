import TwoAxisHelicoid.FiniteChartPartitionStokes
import TwoAxisHelicoid.ComplexEndCompactification

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory Topology Function
open scoped Topology Manifold ContDiff

/-- When the exterior derivative of a global one-form is supported in
a compact subset of one complex chart, its total integral is exactly
the ordinary plane integral in that chart. -/
theorem exterior_integral_in_one_chart {M ι : Type*} [TopologicalSpace M] [Fintype ι]
    (e : ι → OpenPartialHomeomorph M ℂ) (d : OpenPartialHomeomorph M ℂ)
    (ρ : ι → M → ℝ) (a : ι → ℂ → ℂ) (b : ℂ → ℂ)
    (unity : ∀ x, ∑ i, ρ i x=1) (cρ : ∀ i, Continuous (ρ i))
    (inside : ∀ i, tsupport (ρ i)⊆(e i).source)
    (hol : ∀ i z, z∈((e i).symm.trans d).source → AnalyticAt ℂ ((e i).symm.trans d) z)
    (coeff : ∀ i z, z∈((e i).symm.trans d).source →
      a i z=b (((e i).symm.trans d) z)*deriv ((e i).symm.trans d) z)
    (reg : ∀ z∈d.target, ContDiffAt ℝ 1 b z)
    (off : ∀ i z, z∈(e i).target → (e i).symm z∉d.source → complexFormExteriorCoefficient (a i) z=0)
    {K : Set ℂ} (compact : IsCompact K) (sub : K⊆d.target)
    (supp : ∀ z∈d.target, z∉K → complexFormExteriorCoefficient b z=0) :
    (∑ i, ∫ z in (e i).target, ρ i ((e i).symm z) • complexFormExteriorCoefficient (a i) z)=
      ∫ z in d.target, complexFormExteriorCoefficient b z := by
  classical
  let W := fun i z => ρ i (d.symm z) • complexFormExteriorCoefficient b z
  have swap (i : ι) : (∫ z in (e i).target, ρ i ((e i).symm z) • complexFormExteriorCoefficient (a i) z)=
      ∫ z in d.target, W i z := by
    let u := (e i).symm.trans d
    have eq := complex_form_integral_on_overlap (e i) d (a i) b (ρ i) u.open_source.measurableSet
      (Subset.rfl : u.source⊆u.source) (hol i) (coeff i)
      (fun z hz => (reg _ (d.map_source hz.2)).differentiableAt one_ne_zero)
    rw [show (e i).symm.trans d '' u.source=u.target from u.image_source_eq_target] at eq
    calc
      _=∫ z in u.source, ρ i ((e i).symm z) • complexFormExteriorCoefficient (a i) z := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (e i).open_target.measurableSet (fun z hz => hz.1)
        intro z hz
        change ρ i ((e i).symm z) • complexFormExteriorCoefficient (a i) z=0
        rw [off i z hz.1 (fun h => hz.2 ⟨hz.1,h⟩),smul_zero]
      _=∫ z in u.target, W i z := eq.symm
      _=_ := by
        symm
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero d.open_target.measurableSet (fun z hz => hz.1)
        intro z hz
        have outside : d.symm z∉tsupport (ρ i) := fun h => hz.2 ⟨hz.1,inside i h⟩
        have zero : ρ i (d.symm z)=0 := (notMem_tsupport_iff_eventuallyEq.mp outside).self_of_nhds
        simp only [W,zero,zero_smul]
  have integ (i : ι) : IntegrableOn (W i) d.target := by
    have cont : ContinuousOn (W i) d.target :=
      ((cρ i).comp_continuousOn d.continuousOn_symm).smul (complexFormExteriorCoefficient_continuousOn reg)
    apply ((cont.mono sub).integrableOn_compact compact).of_forall_sdiff_eq_zero d.open_target.measurableSet
    intro z hz
    simp only [W,supp z hz.1 hz.2,smul_zero]
  rw [Finset.sum_congr rfl (fun i _ => swap i)]
  rw [← integral_finsetSum _ (fun i _ => integ i)]
  apply setIntegral_congr_fun d.open_target.measurableSet
  intro z _
  simp only [W,← Finset.sum_smul,unity,one_smul]

/-- Stokes for an actual compact Riemann surface in one specified chart.
Only C¹ chart coefficients and their holomorphic overlap law are needed.
The finite coordinate cover and smooth partition are obtained internally. -/
theorem compact_curve_stokes_in_chart {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    (a : OpenPartialHomeomorph M ℂ → ℂ → ℂ)
    (reg : ∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M, ∀ z∈e.target, ContDiffAt ℝ 1 (a e) z)
    (coeff : ∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M, ∀ d∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M,
      ∀ z∈(e.symm.trans d).source, a e z=a d ((e.symm.trans d) z)*deriv (e.symm.trans d) z)
    (d : OpenPartialHomeomorph M ℂ) (hd : d∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    (off : ∀ i z, z∈(chartAt ℂ i).target → (chartAt ℂ i).symm z∉d.source →
      complexFormExteriorCoefficient (a (chartAt ℂ i)) z=0)
    {K : Set ℂ} (compact : IsCompact K) (sub : K⊆d.target)
    (supp : ∀ z∈d.target, z∉K → complexFormExteriorCoefficient (a d) z=0) :
    (∫ z in d.target, complexFormExteriorCoefficient (a d) z)=0 := by
  classical
  let _ := complex_curve_underlying_real_manifold M
  obtain ⟨C,ρ,unity,_,smooth,supports⟩ := compact_curve_chart_partition M
  let e := fun i : C => chartAt ℂ i.1
  have chart (i : C) : e i∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := IsManifold.chart_mem_maximalAtlas _
  have cut (i j : C) (z : ℂ) (hz : z∈(e i).target) : ContDiffAt ℝ 1 (fun w => (ρ j ((e i).symm w):ℂ)) z := by
    have inv : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (e i).symm z :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas _) hz
    have v := ((smooth j).contMDiffAt.comp z inv).contDiffAt
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z (v.of_le (by simp))
  have analytic := fun (i j : C) z (hz : z∈((e i).symm.trans (e j)).source) =>
    (complexAtlas_realized_transition (chart i) (chart j) hz).analyticAt
  have zero := finite_chart_partition_stokes e ρ (fun i => a (e i)) unity (fun i => (smooth i).continuous)
    (fun i => (supports i).1) (fun i => (supports i).2) cut (fun i => reg _ (chart i))
    analytic (fun i j => coeff _ (chart i) _ (chart j))
  have eq := exterior_integral_in_one_chart e d ρ (fun i => a (e i)) (a d) unity
    (fun i => (smooth i).continuous) (fun i => (supports i).2)
    (fun i z hz => (complexAtlas_realized_transition (chart i) hd hz).analyticAt)
    (fun i => coeff _ (chart i) _ hd) (reg _ hd) (fun i => off i.1) compact sub supp
  exact eq.symm.trans zero

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_curve_stokes_in_chart
