import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Complex.Basic

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology

/-- Two genuine inverse germs at a puncture and at infinity determine an
open coordinate chart. Both its source and target contain full tails. -/
theorem puncture_inverse_open_chart {H K : ℂ → ℂ}
    (hH : Tendsto H (𝓝[≠] 0) (cobounded ℂ))
    (hK : Tendsto K (cobounded ℂ) (𝓝[≠] 0))
    (hL : ∀ᶠ z in 𝓝[≠] (0 : ℂ), K (H z) = z)
    (hR : ∀ᶠ ξ : ℂ in cobounded ℂ, H (K ξ) = ξ)
    (hHc : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ContinuousAt H z)
    (hKc : ∀ᶠ ξ : ℂ in cobounded ℂ, ContinuousAt K ξ) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      (e : ℂ → ℂ) = H ∧ (e.symm : ℂ → ℂ) = K ∧
      e.source ∈ 𝓝[≠] (0 : ℂ) ∧ e.target ∈ cobounded ℂ := by
  have he := hL.and hHc
  simp only [nhdsWithin,eventually_inf_principal] at he
  obtain ⟨V,hV,hVo,hV0⟩ := mem_nhds_iff.mp he
  let U : Set ℂ := V \ {0}
  have hUo : IsOpen U := hVo.inter isOpen_compl_singleton
  have hUn : U ∈ 𝓝[≠] (0 : ℂ) :=
    inter_mem (nhdsWithin_le_nhds (hVo.mem_nhds hV0)) self_mem_nhdsWithin
  have hU z (hz : z ∈ U) : K (H z) = z ∧ ContinuousAt H z := hV hz.1 hz.2
  have ht := hR.and ((hK.eventually hUn).and hKc)
  obtain ⟨R,_hR,hRt⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp ht
  let T : Set ℂ := {ξ | R < ‖ξ‖}
  let S : Set ℂ := U ∩ H ⁻¹' T
  have hTo : IsOpen T := isOpen_lt continuous_const continuous_norm
  have hSo : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    exact inter_mem (hUo.mem_nhds hz.1) ((hU z hz.1).2 (hTo.mem_nhds hz.2))
  let e : OpenPartialHomeomorph ℂ ℂ :=
    { toFun := H
      invFun := K
      source := S
      target := T
      map_source' := fun _ hz => hz.2
      map_target' := fun ξ hξ => ⟨(hRt (show R ≤ ‖ξ‖ from hξ.le)).2.1,by
        change H (K ξ) ∈ T
        rw [(hRt (show R ≤ ‖ξ‖ from hξ.le)).1]
        exact hξ⟩
      left_inv' := fun z hz => (hU z hz.1).1
      right_inv' := fun ξ hξ => (hRt (show R ≤ ‖ξ‖ from hξ.le)).1
      open_source := hSo
      open_target := hTo
      continuousOn_toFun := fun z hz => (hU z hz.1).2.continuousWithinAt
      continuousOn_invFun := fun ξ hξ => (hRt (show R ≤ ‖ξ‖ from hξ.le)).2.2.continuousWithinAt }
  refine ⟨e,rfl,rfl,?_,?_⟩
  · exact inter_mem hUn (hH.eventually
      (tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)))
  · exact tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.puncture_inverse_open_chart
