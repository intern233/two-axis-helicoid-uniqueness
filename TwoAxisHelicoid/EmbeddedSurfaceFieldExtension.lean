import TwoAxisHelicoid.BoundedSurfaceFieldExtension
import TwoAxisHelicoid.SmoothSurfaceOrbit

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff

/-- A bounded smooth field on an embedded surface has an ambient extension
with the same convex range constraint. Local inverse charts come from
regularity of the actual spatial map. -/
theorem embedded_surface_field_extension {M F : Type*} [TopologicalSpace M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (X : M → Fin 3 → ℝ) (he : IsClosedEmbedding X)
    {C : Set F} (hC : Convex ℝ C) (hzero : (0:F) ∈ C) (v : (Fin 3 → ℝ) → F)
    (hb : ∀ q, v (X q) ∈ C)
    (localChart : ∀ q : M, ∃ e : OpenPartialHomeomorph M ℂ, q ∈ e.source ∧
      ContDiffAt ℝ 2 (X ∘ e.symm) (e q) ∧ Function.Injective (fderiv ℝ (X ∘ e.symm) (e q)) ∧
      ContDiffAt ℝ 1 (v ∘ X ∘ e.symm) (e q)) :
    ∃ V : (Fin 3 → ℝ) → F, ContDiff ℝ 1 V ∧ (∀ x, V x ∈ C) ∧ ∀ q, V (X q) = v (X q) := by
  obtain ⟨V,hV,hall,heq⟩ := bounded_surface_field_extension he.isClosed_range hC hzero v (by
    rintro _ ⟨q,rfl⟩
    obtain ⟨e,hq,hs,hi,hv⟩ := localChart q
    obtain ⟨τ,hτ,hleft⟩ := regular_smooth_surface_local_inverse hs hi
    have eq : (X ∘ e.symm) (e q) = X q := congrArg X (e.left_inv hq)
    have hτx : ContDiffAt ℝ 2 τ (X q) := eq ▸ hτ
    have hτq : τ (X q) = e q := eq ▸ hleft.self_of_nhds
    let g := (v ∘ X ∘ e.symm) ∘ τ
    have hg : ContDiffAt ℝ 1 g (X q) := (hτq.symm ▸ hv).comp _ (hτx.of_le (by norm_num))
    have same : ∀ᶠ y in 𝓝[range X] (X q), g y = v y := by
      rw [← he.isEmbedding.map_nhds_eq q]
      change ∀ᶠ r in 𝓝 q, g (X r) = v (X r)
      filter_upwards [e.open_source.mem_nhds hq,(e.continuousAt hq).eventually hleft] with r hr hl
      have hv' : (X ∘ e.symm) (e r) = X r := congrArg X (e.left_inv hr)
      have hτr : τ (X r) = e r := hv' ▸ hl
      change v (X (e.symm (τ (X r)))) = v (X r)
      rw [hτr,e.left_inv hr]
    rw [eventually_nhdsWithin_iff] at same
    obtain ⟨U,hu,hsmooth⟩ := hg.contDiffOn le_rfl (by simp)
    refine ⟨U ∩ {y | y ∈ range X → g y = v y},inter_mem hu same,g,hsmooth.mono inter_subset_left,?_⟩
    intro y hy
    exact ⟨hb _,hy.2⟩)
  exact ⟨V,hV,hall,fun q => heq (mem_range_self q)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.embedded_surface_field_extension
