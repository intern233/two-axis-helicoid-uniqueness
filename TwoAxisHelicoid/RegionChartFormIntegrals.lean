import TwoAxisHelicoid.LocalizedComplexChartIntegrals
import TwoAxisHelicoid.ChartCutoffStokes

namespace TwoAxisHelicoid
open Complex MeasureTheory Filter Set Topology Function
open scoped Topology ContDiff

/-- The part of a physical open region in one of its complex coordinates. -/
def curveChartRegion {M : Type*} [TopologicalSpace M] (e : OpenPartialHomeomorph M ℂ) (Ω : Set M) : Set ℂ :=
  e.target ∩ e.symm ⁻¹' Ω

theorem isOpen_curveChartRegion {M : Type*} [TopologicalSpace M] (e : OpenPartialHomeomorph M ℂ)
    {Ω : Set M} (op : IsOpen Ω) : IsOpen (curveChartRegion e Ω) := e.isOpen_inter_preimage_symm op

/-- Restricting an actual surface weight to an open region amounts to
restricting the integration domain in each chart. -/
theorem indicator_weight_chart_integral {M : Type*} [TopologicalSpace M] (e : OpenPartialHomeomorph M ℂ)
    {Ω : Set M} (op : IsOpen Ω) (w : M → ℝ) (f : ℂ → ℂ) :
    (∫ z in e.target, Ω.indicator w (e.symm z) • f z)=
      ∫ z in curveChartRegion e Ω, w (e.symm z) • f z := by
  classical
  let D := curveChartRegion e Ω
  calc
    _=∫ z in e.target, D.indicator (fun y => w (e.symm y) • f y) z := by
      apply setIntegral_congr_fun e.open_target.measurableSet
      intro z hz
      change Ω.indicator w (e.symm z) • f z=D.indicator (fun y => w (e.symm y) • f y) z
      by_cases inside : e.symm z∈Ω
      · rw [indicator_of_mem inside,indicator_of_mem (show z∈D from ⟨hz,inside⟩)]
      · rw [indicator_of_notMem inside,indicator_of_notMem (show z∉D from fun h => inside h.2),zero_smul]
    _=_ := by rw [setIntegral_indicator (isOpen_curveChartRegion e op).measurableSet,
        inter_eq_right.mpr (show D⊆e.target from inter_subset_left)]

/-- The localized area integral of an exterior derivative is invariant
under holomorphic coordinate changes on the given physical region. -/
theorem localized_form_region_integrals {M : Type*} [TopologicalSpace M]
    (e d : OpenPartialHomeomorph M ℂ) {Ω : Set M} (op : IsOpen Ω)
    (a b : ℂ → ℂ) (weight cut : M → ℝ)
    (first : tsupport weight⊆e.source) (second : tsupport cut⊆d.source)
    (hol : ∀ z∈(e.symm.trans d).source, AnalyticAt ℂ (e.symm.trans d) z)
    (coeff : ∀ z∈(e.symm.trans d).source, a z=b ((e.symm.trans d) z)*deriv (e.symm.trans d) z)
    (reg : ∀ z∈d.target, DifferentiableAt ℝ b z)
    (dc : ∀ z∈d.target, DifferentiableAt ℝ (fun w => (cut (d.symm w):ℂ)) z) :
    (∫ z in curveChartRegion e Ω, weight (e.symm z) • complexFormExteriorCoefficient (fun w => (cut (e.symm w):ℂ)*a w) z)=
      ∫ z in curveChartRegion d Ω, weight (d.symm z) • complexFormExteriorCoefficient (fun w => (cut (d.symm w):ℂ)*b w) z := by
  classical
  have bound : tsupport (Ω.indicator weight) ⊆ tsupport weight := by
    apply closure_mono
    intro x hit zero
    apply hit
    by_cases hx : x∈Ω
    · exact (indicator_of_mem hx weight).trans zero
    · exact indicator_of_notMem hx weight
  have eq := localized_form_chart_integrals e d a b (Ω.indicator weight) cut (bound.trans first) second hol coeff reg dc
  simpa only [indicator_weight_chart_integral _ op] using eq

/-- A localized differential has integrable exterior coefficient after
multiplication by an arbitrary continuous chart weight, even when that
weight is supported in a different chart. -/
theorem chart_cutoff_exterior_weight_integrable {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) (weight cut : M → ℝ)
    (cw : Continuous weight) (compact : IsCompact (tsupport cut)) (inside : tsupport cut⊆e.source)
    (a : ℂ → ℂ) (sm : ∀ z∈e.target, ContDiffAt ℝ 1 (fun w => (cut (e.symm w):ℂ)*a w) z) :
    IntegrableOn (fun z => weight (e.symm z) • complexFormExteriorCoefficient (fun w => (cut (e.symm w):ℂ)*a w) z) e.target := by
  let K := e '' tsupport cut
  let A := fun w => (cut (e.symm w):ℂ)*a w
  have ck : IsCompact K := compact.image_of_continuousOn (e.continuousOn.mono inside)
  have sub : K⊆e.target := by
    rintro _ ⟨x,hx,rfl⟩
    exact e.map_source (inside hx)
  have cont : ContinuousOn (fun z => weight (e.symm z) • complexFormExteriorCoefficient A z) e.target :=
    (cw.comp_continuousOn e.continuousOn_symm).smul (complexFormExteriorCoefficient_continuousOn sm)
  apply ((cont.mono sub).integrableOn_compact ck).of_forall_sdiff_eq_zero e.open_target.measurableSet
  intro z hz
  have absent : e.symm z∉tsupport cut := fun h => hz.2 ⟨_,h,e.right_inv hz.1⟩
  have germ : A =ᶠ[𝓝 z] 0 := by
    filter_upwards [(e.continuousAt_symm hz.1).eventually (notMem_tsupport_iff_eventuallyEq.mp absent)] with w hw
    dsimp only [A]
    rw [show cut (e.symm w)=0 from hw,Complex.ofReal_zero,zero_mul]
    rfl
  simp [complexFormExteriorCoefficient,germ.fderiv_eq]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.localized_form_region_integrals
#print axioms TwoAxisHelicoid.chart_cutoff_exterior_weight_integrable
