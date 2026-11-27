import TwoAxisHelicoid.HelicoidCompactCap
import TwoAxisHelicoid.FlatCapAtlasCompatibility
import TwoAxisHelicoid.ImmersionAmbientDiffeomorph

namespace TwoAxisHelicoid
open Set Topology
open scoped ContDiff Manifold
set_option maxHeartbeats 1000000

theorem ambient_diffeomorph_preserves_manifold_immersion
    {M E A : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [ChartedSpace E M]
    {F : M → A} {x : M}
    (hF : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,A) ∞ F x)
    (hi : Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,A) F x))
    (D : A ≃ₜ A) (hD : ContDiff ℝ ∞ D) (hDi : ContDiff ℝ ∞ D.symm) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,A) ∞ (D ∘ F) x ∧
      Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,A) (D ∘ F) x) := by
  refine ⟨hD.contMDiff.contMDiffAt.comp x hF,?_⟩
  rw [mfderiv_comp x (hD.contMDiff.mdifferentiable (by simp) _)
    (hF.mdifferentiableAt (by simp)),mfderiv_eq_fderiv]
  exact (smooth_homeomorph_fderiv_injective D hD hDi _).comp hi

/-- The helicoidal cap has the original smooth structure at every finite
point of the punctured surface. The new chart is only needed at the
added point. -/
theorem HasHelicoidC1End.exists_cap_atlas_compatible_on_puncture
    {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M]
    {p : M} {X₀ : M → HelicoidTubeCoordinates}
    (hEnd : HasHelicoidC1End (fun q : {q : M // q ≠ p} => X₀ q.1))
    (hX : IsProperMap (fun q : {q : M // q ≠ p} => X₀ q.1))
    (hXi : Function.Injective (fun q : {q : M // q ≠ p} => X₀ q.1))
    (hsm : ∀ x ≠ p, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ X₀ x)
    (hi : ∀ x ≠ p, Function.Injective
      (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,HelicoidTubeCoordinates) X₀ x))
    {C : Set {q : M // q ≠ p}} (hC : IsCompact C) :
    ∃ (D : HelicoidTubeCoordinates ≃ₜ HelicoidTubeCoordinates) (R : ℝ)
      (cs : ChartedSpace (ℝ × ℝ) M), let _ := cs
      let F := helicoidCompactCap p D R (fun q : {q : M // q ≠ p} => X₀ q.1)
      0 < R ∧ IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ M ∧ IsClosedEmbedding F ∧
      ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ F ∧
      (∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) F x)) ∧
      (∀ q ∈ C, F q.1 = X₀ q.1) ∧
      ∀ x ≠ p, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ F x ∧
        Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,HelicoidTubeCoordinates) F x) ∧
        ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ × ℝ) ∞ (@id M) x ∧
        ContMDiffAt 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℂ) ∞ (@id M) x := by
  obtain ⟨D,R,hR,hD,hDi,hclosed,hcore,hexact,_⟩ :=
    hEnd.exists_compact_cap_fixing_core hX hXi hC
  let Y₀ := D.symm ∘ X₀
  have hY : IsProperMap (fun q : {q : M // q ≠ p} => Y₀ q.1) := D.symm.isProperMap.comp hX
  have hYi : Function.Injective (fun q : {q : M // q ≠ p} => Y₀ q.1) :=
    D.symm.injective.comp hXi
  have hYreg (x : M) (hx : x ≠ p) :
      ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ Y₀ x ∧
      Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,HelicoidTubeCoordinates) Y₀ x) :=
    ambient_diffeomorph_preserves_manifold_immersion (hsm x hx) (hi x hx) D.symm hDi hD
  obtain ⟨cs,hm,_,hf,hfi,hcompat⟩ := punctured_flat_cap_smooth_atlas_compatible
    hY hYi hR (le_max_left 1 (4*R^2)) (le_max_right 1 (4*R^2)) le_rfl hexact
      (fun x hx => (hYreg x hx).1) (fun x hx => (hYreg x hx).2)
  let _ := cs
  let _ := hm
  let F₀ := puncturedCapMap p (max 1 (4*R^2)) (4*R)
    (fun q : {q : M // q ≠ p} => Y₀ q.1)
  have hreg (x : M) :
      ContMDiffAt 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ (D ∘ F₀) x ∧
      Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) (D ∘ F₀) x) :=
    ambient_diffeomorph_preserves_manifold_immersion (hf x) (hfi x) D hD hDi
  refine ⟨D,R,cs,hR,hm,hclosed,(fun x => (hreg x).1),(fun x => (hreg x).2),hcore,?_⟩
  intro x hx
  obtain ⟨ho,hoi,hid,hid'⟩ := hcompat x hx
  obtain ⟨hDo,hDoi⟩ := ambient_diffeomorph_preserves_manifold_immersion ho hoi D hD hDi
  exact ⟨hDo,hDoi,hid,hid'⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HasHelicoidC1End.exists_cap_atlas_compatible_on_puncture
