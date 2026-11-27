import TwoAxisHelicoid.SurfaceFrameRemovableBasis
import TwoAxisHelicoid.NormalFieldFrameCharts

namespace TwoAxisHelicoid
open Set Topology Matrix
open scoped Matrix

/-- The removable-cover condition can be checked in arbitrary local open
neighborhoods of each point. -/
theorem hasRemovableCoverBasis_of_open_cover {X : Type*} [TopologicalSpace X] {D : Set X}
    (h : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ HasRemovableCoverBasis ((Subtype.val : U → X) ⁻¹' D)) :
    HasRemovableCoverBasis D := by
  intro x W hW hx
  obtain ⟨U,hU,hxU,hD⟩ := h x
  obtain ⟨V,hV,hxV,hVW,hs,hl,hc⟩ := hD ⟨x,hxU⟩ (Subtype.val ⁻¹' W) (hW.preimage continuous_subtype_val) hx
  let _ := hs
  let _ := hl
  let T := (Subtype.val : U → X) '' V
  let J : V ≃ₜ T := IsEmbedding.subtypeVal.homeomorphImage V
  refine ⟨T,hU.isOpenMap_subtype_val V hV,⟨⟨x,hxU⟩,hxV,rfl⟩,?_,
    J.symm.toHomotopyEquiv.simplyConnectedSpace,J.isQuotientMap.locallyPathConnectedSpace,?_⟩
  · rintro _ ⟨v,hv,rfl⟩
    exact hVW hv
  · apply J.isConnected_preimage.mp
    exact hc

/-- The puncture deletion in the full actual oriented tangent frame bundle
of a surface is removable for covering-map morphisms and isomorphisms.
The normal may be nontrivial and the bundle has no chosen global framing. -/
theorem normal_field_frames_puncture_removable {M : Type*} [TopologicalSpace M] [T1Space M] [ChartedSpace ℂ M]
    (p : M) (n : C(M,Fin 3 → ℝ)) (hn : ∀ b, n b ⬝ᵥ n b = 1) :
    HasRemovableCoverBasis {s : NormalFieldFrames n | s.1.1 ≠ p} := by
  apply hasRemovableCoverBasis_of_open_cover
  intro x
  obtain ⟨U,hU,hxU,f,hf⟩ := normal_field_local_reference n hn x
  let W := {s : NormalFieldFrames n | s.1.1 ∈ U}
  have hW : IsOpen W := hU.preimage continuous_subtype_val.fst
  let j := normalFrameChart f hf
  have hj : IsLocalHomeomorph (Prod.map (Subtype.val : U → M) (id : Circle → Circle)) :=
    (hU.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id).isLocalHomeomorph
  exact ⟨W,hW,hxU,((punctured_surface_times_circle_removable p).preimage hj).preimage j.isLocalHomeomorph⟩

/-- Any specified isomorphism of two covering spaces on the punctured actual
frame bundle extends uniquely across the complete missing frame circle. -/
theorem actual_surface_spin_cover_extension_unique {M E F : Type*} [TopologicalSpace M] [T1Space M]
    [ChartedSpace ℂ M] [TopologicalSpace E] [TopologicalSpace F]
    (p : M) (n : C(M,Fin 3 → ℝ)) (hn : ∀ b, n b ⬝ᵥ n b = 1)
    (a : E → NormalFieldFrames n) (b : F → NormalFieldFrames n) (ha : IsCoveringMap a) (hb : IsCoveringMap b)
    (i : {x : E // (a x).1.1 ≠ p} ≃ₜ {y : F // (b y).1.1 ≠ p}) (hi : ∀ x, b (i x).1 = a x.1) :
    ∃! H : E ≃ₜ F, (∀ x, b (H x) = a x) ∧ ∀ x : {e : E // (a e).1.1 ≠ p}, H x.1 = (i x).1 :=
  (normal_field_frames_puncture_removable p n hn).extends_isomorphism ha hb i hi

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_surface_spin_cover_extension_unique
