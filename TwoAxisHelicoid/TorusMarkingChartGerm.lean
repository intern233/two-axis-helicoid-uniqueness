import TwoAxisHelicoid.PointedTorusUniformization

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold

/-- In any honest holomorphic surface chart a torus marking pulls the covering
parameter back by a regular holomorphic coordinate germ. This applies at
arbitrary finite points as well as above the puncture. -/
theorem torus_marking_local_coordinate {N : Type*} [TopologicalSpace N] [ChartedSpace ℂ N]
    {L : PeriodPair} (H : N ≃ₜ PeriodTorus L)
    (hH : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H) (hi : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm)
    (χ : OpenPartialHomeomorph N ℂ) (hχ : χ ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω N) (z : ℂ)
    (hp : H.symm (periodTorusProjection L z) ∈ χ.source) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u z ∧ u z = χ (H.symm (periodTorusProjection L z)) ∧ deriv u z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, χ.symm (u w) = H.symm (periodTorusProjection L w) := by
  let π := periodTorusProjection L
  let p := H.symm (π z)
  let u := fun w => χ (H.symm (π w))
  have hχ' := contMDiffAt_of_mem_maximalAtlas hχ hp
  have hux := hχ'.comp z ((hi.comp (periodTorusProjection_contMDiff L)).contMDiffAt)
  have hau : AnalyticAt ℂ u z := hux.contDiffAt.analyticAt
  have hs : ContinuousAt (fun w => H.symm (π w)) z :=
    (hi.continuous.comp (periodTorusProjection_contMDiff L).continuous).continuousAt
  have hu : ∀ᶠ w in 𝓝 z, χ.symm (u w) = H.symm (π w) :=
    (hs.eventually (χ.open_source.mem_nhds hp)).mono fun _ hw => χ.left_inv hw
  obtain ⟨d,hd,he⟩ := periodTorusProjection_isLocalHomeomorph L z
  have ha : d.symm ∈ atlas ℂ (PeriodTorus L) := he.symm
  have hsrc : H (χ.symm (u z)) ∈ d.target := by
    change H (χ.symm (χ p)) ∈ d.target
    rw [χ.left_inv hp]
    change H (H.symm (π z)) ∈ d.target
    rw [H.apply_symm_apply,show π z = d z from congrFun he z]
    exact d.map_source hd
  let v := fun w => d.symm (H (χ.symm w))
  have hdv := (contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℂ,ℂ)) (n := ω)
    (IsManifold.subset_maximalAtlas ha) hsrc).comp (u z)
    (hH.contMDiffAt.comp (u z) (contMDiffAt_symm_of_mem_maximalAtlas hχ (χ.map_source hp)))
  have hav : AnalyticAt ℂ v (u z) := hdv.contDiffAt.analyticAt
  have heq : v ∘ u =ᶠ[𝓝 z] id := by
    filter_upwards [hu,d.open_source.mem_nhds hd] with w hw hdw
    change d.symm (H (χ.symm (u w))) = w
    rw [hw,H.apply_symm_apply,show π w = d w from congrFun he w,d.left_inv hdw]
  have hchain := deriv_comp z hav.differentiableAt hau.differentiableAt
  have hone : deriv v (u z)*deriv u z = 1 := hchain.symm.trans (heq.deriv_eq.trans (deriv_id z))
  exact ⟨u,hau,rfl,fun h => by simp [h] at hone,hu⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.torus_marking_local_coordinate
