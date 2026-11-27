import TwoAxisHelicoid.ExteriorComplexEnd
import TwoAxisHelicoid.ComplexPunctureTail

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped Topology ContDiff Manifold

/-- The topological one-endedness used below means that, off any compact set,
one connected subset still contains the complement of a compact set. -/
def HasConnectedCompactTails (M : Type*) [TopologicalSpace M] : Prop :=
  ∀ K : Set M, IsCompact K → ∃ U : Set M, IsPreconnected U ∧ IsCompact Uᶜ ∧ Disjoint U K

theorem homeomorphic_punctured_surface_connected_tails {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] [CompactSpace N] [T2Space N] [ChartedSpace ℂ N]
    (p : N) (h : M ≃ₜ {q : N // q ≠ p}) : HasConnectedCompactTails M := by
  intro K hK
  obtain ⟨S,_,hc,hS,hd⟩ := compact_complex_puncture_connected_tail p (hK.image h.continuous)
  refine ⟨h ⁻¹' S,?_,?_,?_⟩
  · exact hc.preimage_of_isOpenMap h.injective h.isOpenMap (by simp)
  · change IsCompact (h ⁻¹' Sᶜ)
    exact h.isCompact_preimage.mpr hS
  · exact disjoint_left.mpr fun x hx hk => disjoint_left.mp hd hx (mem_image_of_mem h hk)

/-- On a one-ended surface a true exterior chart with compact complementary
core escapes toward the unbounded coordinate end if a continuous unbounded
height is the real part of its parameter. This proves forward escape without
an independent properness hypothesis on the exterior coordinate. -/
theorem exterior_coordinate_escapes_of_height {M : Type*} [TopologicalSpace M]
    (hEnd : HasConnectedCompactTails M) (e : OpenPartialHomeomorph M ℂ)
    {R : ℝ} (ht : e.target = {ζ : ℂ | R < ‖ζ‖}) (hcore : IsCompact e.sourceᶜ)
    (h : M → ℝ) (hh : Continuous h) (b : ℝ) (hheight : ∀ x ∈ e.source, h x = b+(e x).re)
    (hunb : ∀ A : ℝ, ∃ x : M, A < h x) :
    Tendsto (fun x => ‖e x‖) (cocompact M) atTop := by
  apply Filter.tendsto_atTop.mpr
  intro A
  let ρ := max A R + 1
  have hR : R < ρ := by dsimp [ρ]; linarith [le_max_right A R]
  have hA : A < ρ := by dsimp [ρ]; linarith [le_max_left A R]
  have hS : sphere (0:ℂ) ρ ⊆ e.target := by
    rw [ht]
    intro z hz
    change R < ‖z‖
    have he : ‖z‖ = ρ := by simpa only [mem_sphere,dist_zero_right] using hz
    rwa [he]
  let C := e.symm '' sphere (0:ℂ) ρ
  have hC : IsCompact C := (isCompact_sphere _ _).image_of_continuousOn (e.symm.continuousOn.mono hS)
  obtain ⟨U,hU,hK,hdis⟩ := hEnd _ (hcore.union hC)
  have hsrc (x : M) (hx : x ∈ U) : x ∈ e.source := by
    by_contra hn
    exact disjoint_left.mp hdis hx (Or.inl hn)
  have hne (x : M) (hx : x ∈ U) : ‖e x‖ ≠ ρ := by
    intro he
    apply disjoint_left.mp hdis hx (Or.inr ?_)
    exact ⟨e x,by simpa only [mem_sphere,dist_zero_right] using he,e.left_inv (hsrc x hx)⟩
  let T := (fun x => ‖e x‖) '' U
  have hT : IsPreconnected T := hU.image _ (e.continuousOn.norm.mono (fun x hx => hsrc x hx))
  have hsub : T ⊆ Iio ρ ∪ Ioi ρ := by
    rintro _ ⟨x,hx,rfl⟩
    exact lt_or_gt_of_ne (hne x hx)
  have hbig : ∃ v ∈ T, ρ < v := by
    obtain ⟨B,hB⟩ := hK.bddAbove_image hh.continuousOn
    obtain ⟨x,hx⟩ := hunb (max B (b+ρ))
    have hxU : x ∈ U := by
      by_contra hn
      exact ((le_max_left B (b+ρ)).trans_lt hx).not_ge (hB (mem_image_of_mem h hn))
    refine ⟨‖e x‖,mem_image_of_mem _ hxU,?_⟩
    have hb := (le_max_right B (b+ρ)).trans_lt hx
    rw [hheight x (hsrc x hxU)] at hb
    linarith [(e x).re_le_norm]
  rcases hT.subset_or_subset isOpen_Iio isOpen_Ioi (disjoint_left.mpr fun _ h₁ h₂ => (h₁ : _ < ρ).asymm h₂) hsub with hsmall | hlarge
  · obtain ⟨v,hv,hv'⟩ := hbig
    exact ((hsmall hv : v < ρ).asymm hv').elim
  · have htail : U ∈ cocompact M := by simpa only [compl_compl] using hK.compl_mem_cocompact
    filter_upwards [htail] with x hx
    exact hA.le.trans (hlarge (mem_image_of_mem _ hx) : ρ < ‖e x‖).le

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exterior_coordinate_escapes_of_height
