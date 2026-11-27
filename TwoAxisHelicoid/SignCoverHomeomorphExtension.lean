import TwoAxisHelicoid.SignCoverMapExtension
import TwoAxisHelicoid.CoverFiberTransport

namespace TwoAxisHelicoid
open Set

/-- An actual homeomorphism over the punctured torus between the flat
sign cover and the restriction of any complete cover extends uniquely
to a homeomorphism over the whole torus, including the missing fiber.
The result concerns covers; identifying a geometric spin bundle with
these covers remains a separate obligation. -/
theorem puncturedSignCoverHomeomorph_extends (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    {E : Type*} [TopologicalSpace E] {p : E → PeriodTorus L} (hp : IsCoveringMap p)
    (h : PuncturedSignCover L χ ≃ₜ {e : E // p e ≠ 0})
    (hh : ∀ q, p (h q).1 = latticeSignCoverProjection L χ q.1) :
    ∃! H : LatticeSignCover L χ ≃ₜ E,
      (∀ q, p (H q) = latticeSignCoverProjection L χ q) ∧
      ∀ q : PuncturedSignCover L χ, H q.1 = (h q).1 := by
  let : PathConnectedSpace (PeriodTorus L) :=
    (Quotient.mk_surjective : Function.Surjective (periodTorusProjection L)).pathConnectedSpace
      QuotientAddGroup.continuous_mk
  let f : C(PuncturedSignCover L χ,E) :=
    ⟨fun q => (h q).1,continuous_subtype_val.comp h.continuous⟩
  obtain ⟨F,⟨hFp,hFr⟩,hFu⟩ := puncturedSignCoverMap_extends L χ hp f hh
  let b := (puncturedTorusCenter L).1
  have hb : b ≠ 0 := (puncturedTorusCenter L).2
  have hFb : Function.Bijective (coverFiberMap F hFp b) := by
    constructor
    · intro x y hxy
      let x' : PuncturedSignCover L χ := ⟨x.1,fun he => hb (x.2.symm.trans he)⟩
      let y' : PuncturedSignCover L χ := ⟨y.1,fun he => hb (y.2.symm.trans he)⟩
      have he : h x' = h y' := by
        apply Subtype.ext
        exact (hFr x').symm.trans ((congrArg Subtype.val hxy).trans (hFr y'))
      exact Subtype.ext (congrArg (fun u : PuncturedSignCover L χ => u.1) (h.injective he))
    · intro y
      let y' : {e : E // p e ≠ 0} := ⟨y.1,fun he => hb (y.2.symm.trans he)⟩
      let x' := h.symm y'
      have hx' : latticeSignCoverProjection L χ x'.1 = b := calc
        _ = p (h x').1 := (hh x').symm
        _ = p y'.1 := congrArg (fun e => p e.1) (h.apply_symm_apply y')
        _ = b := y.2
      refine ⟨⟨x'.1,hx'⟩,Subtype.ext ?_⟩
      change F x'.1 = y'.1
      exact (hFr x').trans (congrArg Subtype.val (h.apply_symm_apply y'))
  have hbij : Function.Bijective F := coverMap_bijective_of_one_fiber
    (latticeSignCoverProjection_isCoveringMap L χ) hp F F.continuous hFp b hFb
  have hloc := coverMap_isLocalHomeomorph
    (latticeSignCoverProjection_isCoveringMap L χ) hp F F.continuous hFp
  let H : LatticeSignCover L χ ≃ₜ E :=
    (Equiv.ofBijective F hbij).toHomeomorphOfContinuousOpen F.continuous hloc.isOpenMap
  refine ⟨H,⟨hFp,hFr⟩,?_⟩
  intro K hK
  let Kc : C(LatticeSignCover L χ,E) := ⟨K,K.continuous⟩
  have he : Kc = F := hFu Kc hK
  apply Homeomorph.ext
  exact fun q => congrArg (fun g : C(LatticeSignCover L χ,E) => g q) he

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.puncturedSignCoverHomeomorph_extends
