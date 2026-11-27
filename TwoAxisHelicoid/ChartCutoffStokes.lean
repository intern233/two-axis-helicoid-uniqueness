import TwoAxisHelicoid.ComplexCurveLocalStokes
import TwoAxisHelicoid.CompactCurveChartPartition

namespace TwoAxisHelicoid
open Complex Set MeasureTheory Filter Topology Function
open scoped Topology ContDiff

/-- A weight with compact support in an actual coordinate chart makes any
continuous density integrable over the full coordinate domain. -/
theorem chart_weighted_density_integrable {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) {ρ : M → ℝ} (cρ : Continuous ρ)
    (compact : IsCompact (tsupport ρ)) (inside : tsupport ρ⊆e.source)
    {g : ℂ → ℂ} (cg : ContinuousOn g e.target) :
    IntegrableOn (fun z => ρ (e.symm z) • g z) e.target := by
  let K := e '' tsupport ρ
  have ck : IsCompact K := compact.image_of_continuousOn (e.continuousOn.mono inside)
  have sub : K⊆e.target := by
    rintro _ ⟨x,hx,rfl⟩
    exact e.map_source (inside hx)
  have cont : ContinuousOn (fun z => ρ (e.symm z) • g z) K :=
    (((cρ.comp_continuousOn e.continuousOn_symm).smul cg).mono sub)
  apply (cont.integrableOn_compact ck).of_forall_sdiff_eq_zero e.open_target.measurableSet
  intro z hz
  have out : e.symm z∉tsupport ρ := fun h => hz.2 ⟨e.symm z,h,e.right_inv hz.1⟩
  rw [show ρ (e.symm z)=0 from (notMem_tsupport_iff_eventuallyEq.mp out).self_of_nhds,zero_smul]

theorem complexFormExteriorCoefficient_continuousOn {D : Set ℂ} {a : ℂ → ℂ}
    (sm : ∀ z∈D, ContDiffAt ℝ 1 a z) : ContinuousOn (complexFormExteriorCoefficient a) D := by
  intro z hz
  have der : ContinuousAt (fderiv ℝ a) z := (sm z hz).continuousAt_fderiv (by simp)
  exact (continuousAt_const.mul (der.clm_apply (continuousAt_const (y:=(1:ℂ)))) |>.sub
    (der.clm_apply (continuousAt_const (y:=I)))).continuousWithinAt

/-- A chart-supported one-form has total exterior integral zero on this
chart even when its originally given coefficient is smooth only there. -/
theorem chart_cutoff_stokes {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) {ρ : M → ℝ}
    (compact : IsCompact (tsupport ρ)) (inside : tsupport ρ⊆e.source)
    {a : ℂ → ℂ} (sm : ∀ z∈e.target, ContDiffAt ℝ 1 (fun w => (ρ (e.symm w):ℂ)*a w) z) :
    (∫ z in e.target, complexFormExteriorCoefficient (fun w => (ρ (e.symm w):ℂ)*a w) z)=0 := by
  let K := e '' tsupport ρ
  have ck : IsCompact K := compact.image_of_continuousOn (e.continuousOn.mono inside)
  have sub : K⊆e.target := by
    rintro _ ⟨x,hx,rfl⟩
    exact e.map_source (inside hx)
  obtain ⟨g,sg,gk,_,agree,off⟩ := extend_compact_chart_coefficient e.open_target ck sub sm (by
    intro z hz out
    have h : e.symm z∉tsupport ρ := fun h => out ⟨_,h,e.right_inv hz⟩
    rw [show ρ (e.symm z)=0 from (notMem_tsupport_iff_eventuallyEq.mp h).self_of_nhds,
      Complex.ofReal_zero,zero_mul])
  have zeroOff (z : ℂ) (hz : z∉e.target) : complexFormExteriorCoefficient g z=0 := by
    have eq := (off z (fun h => hz (sub h))).fderiv_eq (𝕜:=ℝ)
    simp [complexFormExteriorCoefficient,eq]
  calc
    _=∫ z in e.target, complexFormExteriorCoefficient g z := by
      apply setIntegral_congr_fun e.open_target.measurableSet
      intro z hz
      simp only [complexFormExteriorCoefficient,(agree z hz).fderiv_eq]
    _=∫ z, complexFormExteriorCoefficient g z := by
      apply Eq.symm
      rw [← setIntegral_univ]
      exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ (subset_univ _)
        (fun z hz => zeroOff z hz.2)
    _=0 := compact_complex_form_stokes sg gk

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.chart_weighted_density_integrable
#print axioms TwoAxisHelicoid.chart_cutoff_stokes
