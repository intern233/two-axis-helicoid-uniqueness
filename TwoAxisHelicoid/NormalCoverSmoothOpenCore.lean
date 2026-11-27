import TwoAxisHelicoid.OrderedGenusOneCoreMultiplicity
import TwoAxisHelicoid.OpenCoreSmoothTransport

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold

/-- Local inverses of the normal projection give a single smooth open
parametrization on the whole marked genus-one core. Smoothness is used
only through ordinary inverse germs on individual sheets; multiplicity,
the global inverse and torus generators are conclusions. -/
theorem normal_cover_gives_smooth_open_core {A L : PeriodPair} (C : TorusGeneratingCoreModel A)
    {E : Type*} [TopologicalSpace E] [T2Space E] (j : E → PeriodTorus L) (hj : IsOpenEmbedding j)
    (hn : ∀ e, j e ≠ 0) {p : E → C.carrier} (hp : IsProperMap p) (hl : IsLocalHomeomorph p)
    (hs : Function.Surjective p) {h : E → ℝ} (hh : Continuous h)
    (hsep : ∀ a b, p a = p b → h a = h b → a = b)
    (hlocal : ∀ e, ∃ f : PeriodTorus A → PeriodTorus L, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) 1 f (p e).1 ∧
      ∀ᶠ y in 𝓝 e, f (p y).1 = j y) :
    ∃ F : SmoothOpenTorusCoreMap C L, ∀ y, F.map (p y).1 = j y := by
  classical
  have H := ordered_normal_cover_of_genus_one_core_is_homeomorphism C j hj hp hl hs hh hsep
  let e := (Equiv.ofBijective p H.bijective).toHomeomorphOfContinuousOpen H.continuous H.isOpenMap
  let g := j ∘ e.symm
  let f := Function.extend ((↑) : C.carrier → PeriodTorus A) g (fun _ => 0)
  have hf (x : C.carrier) : f x.1 = g x := Subtype.val_injective.extend_apply ..
  have he (y : E) : f (p y).1 = j y := by
    rw [hf]
    exact congrArg j (e.symm_apply_apply y)
  let π := fun y : E => (p y).1
  have hπ : IsOpenEmbedding π := C.isOpen_carrier.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
  have hsmooth : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) 1 f C.carrier := by
    intro x hx
    obtain ⟨y,hy⟩ := hs ⟨x,hx⟩
    have hy' : π y = x := congrArg Subtype.val hy
    obtain ⟨b,hb,hfb⟩ := hlocal y
    have hnear : f =ᶠ[𝓝 (π y)] b := by
      rw [← hπ.map_nhds_eq]
      change ∀ᶠ u in 𝓝 y, f (p u).1 = b (p u).1
      exact hfb.mono (fun u hu => (he u).trans hu.symm)
    rw [← hy']
    exact (hb.congr_of_eventuallyEq hnear).contMDiffWithinAt
  refine ⟨⟨f,?_,hsmooth,?_⟩,he⟩
  · have hfun : (fun q : C.carrier => f q.1) = g := funext hf
    rw [hfun]
    exact hj.comp e.symm.isOpenEmbedding
  · intro x hx
    obtain ⟨y,hy⟩ := hs ⟨x,hx⟩
    have hy' : (p y).1 = x := congrArg Subtype.val hy
    rw [← hy',he]
    exact hn y

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.normal_cover_gives_smooth_open_core
