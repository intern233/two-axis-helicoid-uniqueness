import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace TwoAxisHelicoid
open Complex Filter Set
open scoped Topology

theorem analyticAt_dslope_center {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    AnalyticAt ℂ (dslope f p) p := by
  let U : Set ℂ := {z | AnalyticAt ℂ f z}
  have hU : IsOpen U := isOpen_analyticAt ℂ f
  have hd : DifferentiableOn ℂ f U := fun _ hz => hz.differentiableAt.differentiableWithinAt
  exact ((Complex.differentiableOn_dslope (hU.mem_nhds hf)).mpr hd).analyticOnNhd hU p hf

/-- An actual meromorphic double pole of an even function has no residue.
The nonzero leading coefficient and analytic remainder are constructed,
rather than supplied as a Laurent expansion hypothesis. -/
theorem even_meromorphic_double_pole_principal_part {f : ℂ → ℂ}
    (hf : MeromorphicAt f 0) (ho : meromorphicOrderAt f 0 = (-2 : ℤ))
    (heven : ∀ᶠ z in 𝓝[≠] (0 : ℂ), f (-z) = f z) :
    ∃ (A : ℂ) (r : ℂ → ℂ), A ≠ 0 ∧ AnalyticAt ℂ r 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z = A/z^2+r z := by
  obtain ⟨u,hu,hu0,hfac⟩ := (meromorphicOrderAt_eq_int_iff hf).mp ho
  have hfac' : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → f z = u z/z^2 := by
    have hh : ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z = u z/z^2 := by
      filter_upwards [hfac] with z hz
      simpa [sub_zero,smul_eq_mul,zpow_neg,div_eq_mul_inv,mul_comm] using hz
    simpa only [eventually_nhdsWithin_iff,mem_compl_iff,mem_singleton_iff] using hh
  have hev : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → f (-z) = f z := by
    simpa only [eventually_nhdsWithin_iff,mem_compl_iff,mem_singleton_iff] using heven
  have hneg : Tendsto (fun z : ℂ => -z) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.continuousAt : ContinuousAt (fun z : ℂ => -z) 0).tendsto
  have hue : (fun z => u (-z)) =ᶠ[𝓝 (0 : ℂ)] u := by
    filter_upwards [hfac',hneg.eventually hfac',hev] with z hz hn he
    by_cases hzero : z = 0
    · simp [hzero]
    · have h := (hn (neg_ne_zero.mpr hzero)).symm.trans ((he hzero).trans (hz hzero))
      simpa only [neg_sq,div_left_inj' (pow_ne_zero 2 hzero)] using h
  have hdu : deriv u 0 = 0 := by
    have hd : HasDerivAt (fun z : ℂ => u (-z)) (-(deriv u 0)) 0 := by
      have hd0 : HasDerivAt u (deriv u 0) (-(0 : ℂ)) := by
        simpa using hu.differentiableAt.hasDerivAt
      simpa using! hd0.comp (0 : ℂ) (hasDerivAt_id (0 : ℂ)).neg
    have hh := (hd.congr_of_eventuallyEq hue.symm).unique hu.differentiableAt.hasDerivAt
    linear_combination -hh/2
  have hv := analyticAt_dslope_center hu
  have hw := analyticAt_dslope_center hv
  refine ⟨u 0,dslope (dslope u 0) 0,hu0,hw,?_⟩
  filter_upwards [hfac'.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with z hz hnz
  rw [hz hnz]
  have huq := sub_smul_dslope u 0 z
  have hvq := sub_smul_dslope (dslope u 0) 0 z
  simp only [sub_zero,smul_eq_mul,dslope_same,hdu,sub_zero] at huq hvq
  have hnz' : z ≠ 0 := hnz
  field_simp [hnz']
  linear_combination -huq-z*hvq

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.even_meromorphic_double_pole_principal_part
