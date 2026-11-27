import TwoAxisHelicoid.EntirePlaneAutomorphism
import TwoAxisHelicoid.TorusActualLifts
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

namespace TwoAxisHelicoid
open Complex Filter Set Topology
open scoped Topology ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- A holomorphic covering by the ordinary complex plane. Every inverse branch
is expressed by a compatible complex coordinate chart on the original surface. -/
structure HolomorphicPlaneCover (p : ℂ → M) : Prop where
  covering : IsCoveringMap p
  onto : Function.Surjective p
  local_chart : ∀ z : ℂ, ∃ e : OpenPartialHomeomorph M ℂ,
    e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M ∧ z ∈ e.target ∧ e.symm =ᶠ[𝓝 z] p

theorem HolomorphicPlaneCover.contMDiff {p : ℂ → M} (hp : HolomorphicPlaneCover p) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω p := by
  intro z
  obtain ⟨e,he,hz,hl⟩ := hp.local_chart z
  exact (contMDiffAt_symm_of_mem_maximalAtlas he hz).congr_of_eventuallyEq hl.symm

theorem HolomorphicPlaneCover.deck_differentiable {p : ℂ → M} (hp : HolomorphicPlaneCover p)
    {F : ℂ → ℂ} (hF : Continuous F) (h : p ∘ F = p) : Differentiable ℂ F := by
  intro z
  obtain ⟨e,he,hz,hl⟩ := hp.local_chart (F z)
  have hz' : e.symm (F z) = p z := hl.self_of_nhds.trans (congrFun h z)
  have hs : p z ∈ e.source := hz' ▸ e.map_target hz
  have hd := (contMDiffAt_of_mem_maximalAtlas he hs).comp z hp.contMDiff.contMDiffAt
  apply (contMDiffAt_iff_contDiffAt.mp hd).differentiableAt (by simp) |>.congr_of_eventuallyEq
  filter_upwards [hF.continuousAt.eventually hl,hF.continuousAt.eventually (e.open_target.mem_nhds hz)]
    with w hw hew
  change F w = e (p w)
  rw [← show p (F w) = p w from congrFun h w,← hw]
  exact (e.right_inv hew).symm

/-- Each deck transformation of a holomorphic plane covering is a translation.
Any other affine automorphism would fix a point and hence be the identity. -/
theorem HolomorphicPlaneCover.deck_translation {p : ℂ → M} (hp : HolomorphicPlaneCover p)
    (F : ℂ ≃ₜ ℂ) (h : p ∘ F = p) : ∀ z, F z = z+F 0 := by
  have hi : p ∘ F.symm = p := funext fun z => by
    have hh := congrFun h (F.symm z)
    simpa only [Function.comp_apply,F.apply_symm_apply] using hh.symm
  obtain ⟨c,_,hc⟩ := entire_plane_automorphism_affine F (hp.deck_differentiable F.continuous h)
    (hp.deck_differentiable F.symm.continuous hi)
  by_cases one : c = 1
  · simpa [one] using hc
  · let w := F 0 / (1-c)
    have hne : 1-c ≠ 0 := sub_ne_zero.mpr (Ne.symm one)
    have hw : F w = w := by
      rw [hc]
      dsimp only [w]
      field_simp
      ring
    have hf : (F : ℂ → ℂ) = id := hp.covering.eq_of_comp_eq F.continuous continuous_id h w hw
    intro z
    simp [hf]

/-- Any two points in one fiber of the plane covering are related by an
actual deck homeomorphism. Both it and its inverse come from lift uniqueness. -/
theorem plane_cover_deck_transitive {N : Type*} [TopologicalSpace N] {p : ℂ → N}
    (hp : IsCoveringMap p) {x y : ℂ} (hxy : p x = p y) :
    ∃ F : ℂ ≃ₜ ℂ, F x = y ∧ p ∘ F = p := by
  let P : C(ℂ,N) := ⟨p,hp.continuous⟩
  obtain ⟨F,⟨hF,hpF⟩,_⟩ := hp.existsUnique_continuousMap_lifts P x y hxy.symm
  obtain ⟨G,⟨hG,hpG⟩,_⟩ := hp.existsUnique_continuousMap_lifts P y x hxy
  have hl : (G ∘ F : ℂ → ℂ) = id := by
    exact hp.eq_of_comp_eq (G.continuous.comp F.continuous) continuous_id
      (funext fun z => (congrFun hpG (F z)).trans (congrFun hpF z)) x ((congrArg G hF).trans hG)
  have hr : (F ∘ G : ℂ → ℂ) = id := by
    exact hp.eq_of_comp_eq (F.continuous.comp G.continuous) continuous_id
      (funext fun z => (congrFun hpF (G z)).trans (congrFun hpG z)) y ((congrArg F hG).trans hF)
  exact ⟨⟨⟨F,G,congrFun hl,congrFun hr⟩,F.continuous,G.continuous⟩,hF,hpF⟩

theorem HolomorphicPlaneCover.fiber_translations {p : ℂ → M} (hp : HolomorphicPlaneCover p)
    {x y : ℂ} (hxy : p x = p y) (z : ℂ) : p (z+(y-x)) = p z := by
  obtain ⟨F,hF,he⟩ := plane_cover_deck_transitive hp.covering hxy
  have hw := hp.deck_translation F he
  have hx : y = x+F 0 := hF.symm.trans (hw x)
  have hv : y-x = F 0 := by rw [hx]; ring
  rw [hv,← hw]
  exact congrFun he z

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HolomorphicPlaneCover.fiber_translations
