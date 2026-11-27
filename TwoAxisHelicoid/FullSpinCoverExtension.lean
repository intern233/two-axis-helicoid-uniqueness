import TwoAxisHelicoid.FullSpinCoverMapExtension
import TwoAxisHelicoid.CoverFiberTransport

namespace TwoAxisHelicoid
open Set Topology

/-- Uniqueness of the compact extension as a covering of the entire
oriented frame bundle. An isomorphism on the punctured torus is the
only input comparing the two covers. -/
theorem punctured_full_spin_homeomorph_extends (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    {E : Type*} [TopologicalSpace E] {p : E → PeriodTorus L × Circle} (hp : IsCoveringMap p)
    (h : RestrictedCompactMultiplierSpin L χ ≃ₜ {e : E // (p e).1 ≠ 0})
    (hh : ∀ s, p (h s).1 = compactMultiplierSpinProjection L χ s.1) :
    ∃! H : CompactMultiplierSpinBundle L χ ≃ₜ E,
      (∀ s, p (H s) = compactMultiplierSpinProjection L χ s) ∧
      ∀ s : RestrictedCompactMultiplierSpin L χ, H s.1 = (h s).1 := by
  let : PathConnectedSpace (PeriodTorus L) :=
    (Quotient.mk_surjective : Function.Surjective (periodTorusProjection L)).pathConnectedSpace
      QuotientAddGroup.continuous_mk
  let f : C(RestrictedCompactMultiplierSpin L χ,E) := ⟨fun s => (h s).1,
    continuous_subtype_val.comp h.continuous⟩
  obtain ⟨F,⟨hFp,hFr⟩,hFu⟩ := punctured_full_spin_map_extends L χ hp f hh
  let b : PeriodTorus L × Circle := ((puncturedTorusCenter L).1,1)
  have hb : b.1 ≠ 0 := (puncturedTorusCenter L).2
  let π := compactMultiplierSpinProjection L χ
  have hbij : Function.Bijective (coverFiberMap F hFp b) := by
    constructor
    · intro x y hxy
      let x' : RestrictedCompactMultiplierSpin L χ :=
        ⟨x.1,fun he => hb ((congrArg Prod.fst x.2).symm.trans he)⟩
      let y' : RestrictedCompactMultiplierSpin L χ :=
        ⟨y.1,fun he => hb ((congrArg Prod.fst y.2).symm.trans he)⟩
      have he : h x' = h y' := by
        apply Subtype.ext
        exact (hFr x').symm.trans ((congrArg Subtype.val hxy).trans (hFr y'))
      exact Subtype.ext (congrArg (fun v : RestrictedCompactMultiplierSpin L χ => v.1) (h.injective he))
    · intro y
      let y' : {e : E // (p e).1 ≠ 0} :=
        ⟨y.1,fun he => hb ((congrArg Prod.fst y.2).symm.trans he)⟩
      let s := h.symm y'
      have hs : π s.1 = b := calc
        _ = p (h s).1 := (hh s).symm
        _ = p y'.1 := congrArg (fun e : {e : E // (p e).1 ≠ 0} => p e.1) (h.apply_symm_apply y')
        _ = b := y.2
      refine ⟨⟨s.1,hs⟩,Subtype.ext ?_⟩
      exact (hFr s).trans (congrArg Subtype.val (h.apply_symm_apply y'))
  have hc := compactMultiplierSpinProjection_isCoveringMap L χ
  have hFbij := coverMap_bijective_of_one_fiber hc hp F F.continuous hFp b hbij
  have hloc := coverMap_isLocalHomeomorph hc hp F F.continuous hFp
  let H := (Equiv.ofBijective F hFbij).toHomeomorphOfContinuousOpen F.continuous hloc.isOpenMap
  refine ⟨H,⟨hFp,hFr⟩,?_⟩
  intro K hK
  let c : C(CompactMultiplierSpinBundle L χ,E) := ⟨K,K.continuous⟩
  have he : c = F := hFu c hK
  exact Homeomorph.ext (fun s => congrArg (fun g : C(CompactMultiplierSpinBundle L χ,E) => g s) he)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_full_spin_homeomorph_extends
