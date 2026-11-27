import TwoAxisHelicoid.HelicoidCompactCap
import TwoAxisHelicoid.FlatCapSmoothAtlas
import TwoAxisHelicoid.ImmersionAmbientDiffeomorph

namespace TwoAxisHelicoid
open Real Set Topology
open scoped ContDiff Manifold
set_option maxHeartbeats 1000000

/-- The concrete cap of a proper embedded helicoidal end has a full
smooth immersion atlas and fixes any prescribed compact core. The
finite-point chart hypotheses concern the original immersion only. -/
theorem HasHelicoidC1End.exists_smooth_compact_cap_fixing_core
    {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    {p : M} {X₀ : M → HelicoidTubeCoordinates}
    (hEnd : HasHelicoidC1End (fun q : {q : M // q ≠ p} => X₀ q.1))
    (hX : IsProperMap (fun q : {q : M // q ≠ p} => X₀ q.1))
    (hXi : Function.Injective (fun q : {q : M // q ≠ p} => X₀ q.1))
    (hfinite : ∀ x ≠ p, ∃ e : OpenPartialHomeomorph M (ℝ × ℝ),
      RegularImmersionChart X₀ e ∧ p ∉ e.source ∧ x ∈ e.source)
    {C : Set {q : M // q ≠ p}} (hC : IsCompact C) :
    ∃ (D : HelicoidTubeCoordinates ≃ₜ HelicoidTubeCoordinates) (R : ℝ)
      (cs : ChartedSpace (ℝ × ℝ) M), let _ := cs
      let F := helicoidCompactCap p D R (fun q : {q : M // q ≠ p} => X₀ q.1)
      0 < R ∧ IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ M ∧ IsClosedEmbedding F ∧
      ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ F ∧
      (∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) F x)) ∧
      ∀ q ∈ C, F q.1 = X₀ q.1 := by
  let X : {q : M // q ≠ p} → HelicoidTubeCoordinates := fun q => X₀ q.1
  obtain ⟨D,R,hR,hD,hDi,hclosed,hcore,hexact,_⟩ :=
    hEnd.exists_compact_cap_fixing_core hX hXi hC
  let Y₀ := D.symm ∘ X₀
  have hY : IsProperMap (fun q : {q : M // q ≠ p} => Y₀ q.1) :=
    D.symm.isProperMap.comp hX
  have hYi : Function.Injective (fun q : {q : M // q ≠ p} => Y₀ q.1) :=
    D.symm.injective.comp hXi
  have hfiniteY : ∀ x ≠ p, ∃ e : OpenPartialHomeomorph M (ℝ × ℝ),
      RegularImmersionChart Y₀ e ∧ p ∉ e.source ∧ x ∈ e.source := by
    intro x hx
    obtain ⟨e,he,hpe,hxe⟩ := hfinite x hx
    exact ⟨e,regularImmersionChart_ambient_comp he D.symm hDi hD,hpe,hxe⟩
  obtain ⟨cs,hm,_,hf,hfi⟩ := punctured_flat_cap_has_smooth_atlas
    hY hYi hR (le_max_left 1 (4*R^2)) (le_max_right 1 (4*R^2)) le_rfl hexact hfiniteY
  let _ := cs
  let _ := hm
  let F₀ := puncturedCapMap p (max 1 (4*R^2)) (4*R)
    (fun q : {q : M // q ≠ p} => Y₀ q.1)
  have hf₀ : ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ F₀ := hf
  have hsm : ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ (D ∘ F₀) :=
    hD.contMDiff.comp hf₀
  refine ⟨D,R,cs,hR,hm,hclosed,hsm,?_,hcore⟩
  intro x
  change Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) (D ∘ F₀) x)
  rw [mfderiv_comp x (hD.contMDiff.mdifferentiable (by simp) _)
    (hf₀.mdifferentiable (by simp) x), mfderiv_eq_fderiv]
  exact (smooth_homeomorph_fderiv_injective D hD hDi _).comp (hfi x)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HasHelicoidC1End.exists_smooth_compact_cap_fixing_core
