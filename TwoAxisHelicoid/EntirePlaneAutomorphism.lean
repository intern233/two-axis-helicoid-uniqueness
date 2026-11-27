import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Algebra.Group.Basic

namespace TwoAxisHelicoid
open Complex Filter Set Bornology
open scoped Topology

/-- The reciprocal chart at infinity for a plane homeomorphism fixing zero
is analytic there if the map is analytic at all finite points. -/
theorem reciprocal_plane_automorphism_analytic (e : ℂ ≃ₜ ℂ) (h0 : e 0 = 0)
    (he : Differentiable ℂ e) : AnalyticAt ℂ (fun w : ℂ => (e w⁻¹)⁻¹) 0 := by
  have hp : Tendsto e (cobounded ℂ) (cobounded ℂ) := by
    rw [Metric.cobounded_eq_cocompact]
    exact e.map_cocompact.le
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [self_mem_nhdsWithin] with w hw
    change w ≠ 0 at hw
    have hn : e w⁻¹ ≠ 0 := fun h => inv_ne_zero hw (e.injective (h.trans h0.symm))
    exact ((he w⁻¹).comp w (differentiableAt_inv hw)).inv hn
  · rw [continuousAt_iff_punctured_nhds]
    simpa only [inv_zero,h0,Function.comp_def] using
      (tendsto_inv₀_cobounded (α := ℂ)).comp (hp.comp tendsto_inv₀_nhdsNE_zero)

/-- A biholomorphic automorphism fixing zero is multiplication by a nonzero
constant. The proof extends its reciprocal germ at infinity and applies
Liouville to the filled divided difference. -/
theorem entire_plane_automorphism_fix_zero (e : ℂ ≃ₜ ℂ) (h0 : e 0 = 0)
    (he : Differentiable ℂ e) (hi : Differentiable ℂ e.symm) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z, e z = c*z := by
  let F := fun w : ℂ => (e w⁻¹)⁻¹
  let G := fun w : ℂ => (e.symm w⁻¹)⁻¹
  have hF := reciprocal_plane_automorphism_analytic e h0 he
  have hG := reciprocal_plane_automorphism_analytic e.symm (e.symm_apply_eq.mpr h0.symm) hi
  have hF0 : F 0 = 0 := by simp [F,h0]
  have hGF : G ∘ F = id := by ext w; simp [G,F]
  have hGn : DifferentiableAt ℂ G (F 0) := hF0.symm ▸ hG.differentiableAt
  have hz : deriv G (F 0) * deriv F 0 = 1 := by
    rw [← deriv_comp 0 hGn hF.differentiableAt,hGF,deriv_id]
  have hn : deriv F 0 ≠ 0 := fun h => by simp [h] at hz
  have ht : Tendsto (fun w : ℂ => F w/w) (𝓝[≠] 0) (𝓝 (deriv F 0)) := by
    have hs := (show DifferentiableAt ℂ F 0 from hF.differentiableAt).hasDerivAt.tendsto_slope
    exact hs.congr fun w => by rw [slope_def_field,hF0,sub_zero,sub_zero]
  have hinf : Tendsto (dslope (e:ℂ → ℂ) 0) (cobounded ℂ) (𝓝 ((deriv F 0)⁻¹)) := by
    have hl := ((continuousAt_inv₀ hn).tendsto.comp ht).comp (tendsto_inv₀_cobounded' (α := ℂ))
    apply hl.congr'
    have hne : ({(0:ℂ)}ᶜ : Set ℂ) ∈ cobounded ℂ := by
      rw [Metric.cobounded_eq_cocompact]
      exact isCompact_singleton.compl_mem_cocompact
    filter_upwards [hne] with w hw
    change w ≠ 0 at hw
    rw [dslope_of_ne _ hw,slope_def_field,h0,sub_zero,sub_zero]
    simp [F,Function.comp_def,div_eq_mul_inv,mul_comm]
  have hd : Differentiable ℂ (dslope (e : ℂ → ℂ) 0) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope (s := univ) univ_mem).mpr he.differentiableOn)
  have hconst := hd.eq_const_of_tendsto_cocompact (Metric.cobounded_eq_cocompact (α := ℂ) ▸ hinf)
  refine ⟨_,inv_ne_zero hn,fun z => ?_⟩
  by_cases h : z = 0
  · simpa [h] using h0
  · have hh := congrFun hconst z
    rw [dslope_of_ne _ h,slope_def_field,h0,sub_zero,sub_zero] at hh
    exact (div_eq_iff h).mp hh

theorem entire_plane_automorphism_affine (e : ℂ ≃ₜ ℂ) (he : Differentiable ℂ e)
    (hi : Differentiable ℂ e.symm) : ∃ c : ℂ, c ≠ 0 ∧ ∀ z, e z = c*z + e 0 := by
  let h := e.trans (Homeomorph.addRight (-e 0))
  have h0 : h 0 = 0 := add_neg_cancel _
  have hh : Differentiable ℂ h := he.add_const _
  have hh' : Differentiable ℂ h.symm := hi.comp (differentiable_id.sub_const _)
  obtain ⟨c,hc,hcz⟩ := entire_plane_automorphism_fix_zero h h0 hh hh'
  refine ⟨c,hc,fun z => ?_⟩
  have := hcz z
  change e z + -e 0 = c*z at this
  linear_combination this

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.entire_plane_automorphism_affine
