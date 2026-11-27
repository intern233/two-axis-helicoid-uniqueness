import TwoAxisHelicoid.PuncturedLatticePlane
import TwoAxisHelicoid.OrthonormalFrameCover
import Mathlib.Topology.Instances.ZMod

namespace TwoAxisHelicoid
open Set Topology

noncomputable def quotientFiberDescend {E B Y : Type*} (p : E → B)
    (hp : Function.Surjective p) (f : E → Y) : B → Y :=
  f ∘ Function.surjInv hp

theorem quotientFiberDescend_apply {E B Y : Type*} (p : E → B)
    (hp : Function.Surjective p) (f : E → Y)
    (hf : ∀ x y, p x = p y → f x = f y) (x : E) :
    quotientFiberDescend p hp f (p x) = f x :=
  hf _ x (Function.surjInv_eq hp (p x))

theorem quotientFiberDescend_continuous {E B Y : Type*}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Y]
    {p : E → B} (hp : IsQuotientMap p) (f : E → Y)
    (hf : ∀ x y, p x = p y → f x = f y) (hc : Continuous f) :
    Continuous (quotientFiberDescend p hp.surjective f) := by
  apply hp.continuous_iff.mpr
  have he : quotientFiberDescend p hp.surjective f ∘ p = f :=
    funext (quotientFiberDescend_apply p hp.surjective f hf)
  rw [he]
  exact hc

def UnitSpinorEquivariant (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (s : PuncturedLatticePlane L → UnitSpinor) : Prop :=
  ∀ (ω : L.lattice) (z w : PuncturedLatticePlane L), w.1 = z.1+ω.1 → s w = χ ω +ᵥ s z

theorem unitSpinorTangentFrame_vadd (g : ZMod 2) (s : UnitSpinor) :
    unitSpinorTangentFrame (g +ᵥ s) = unitSpinorTangentFrame s := by
  rcases zmod_two_cases g with rfl | rfl
  · rw [zero_vadd]
  · rw [unitSpinor_vadd_one]
    exact unitSpinorTangentFrame_fibers.mpr (Or.inr rfl)

theorem equivariant_frame_constant_fibers (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (s : PuncturedLatticePlane L → UnitSpinor) (hs : UnitSpinorEquivariant L χ s)
    (z w : PuncturedLatticePlane L) (hzw : puncturedPlaneProjection L z = puncturedPlaneProjection L w) :
    unitSpinorTangentFrame (s z) = unitSpinorTangentFrame (s w) := by
  let ω : L.lattice := ⟨z.1-w.1,(puncturedPlaneProjection_eq_iff L z w).mp hzw⟩
  have he : z.1 = w.1+ω.1 := by dsimp [ω]; ring
  rw [hs ω w z he,unitSpinorTangentFrame_vadd]

noncomputable def equivariantTorusFrame (L : PeriodPair)
    (s : PuncturedLatticePlane L → UnitSpinor) : PuncturedPeriodTorus L → OrthonormalTangentPair :=
  quotientFiberDescend (puncturedPlaneProjection L) (puncturedPlaneProjection_surjective L)
    (unitSpinorTangentFrame ∘ s)

theorem equivariantTorusFrame_projection (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (s : PuncturedLatticePlane L → UnitSpinor) (hs : UnitSpinorEquivariant L χ s)
    (z : PuncturedLatticePlane L) :
    equivariantTorusFrame L s (puncturedPlaneProjection L z) = unitSpinorTangentFrame (s z) :=
  quotientFiberDescend_apply _ _ _ (equivariant_frame_constant_fibers L χ s hs) z

theorem equivariantTorusFrame_continuous (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (s : PuncturedLatticePlane L → UnitSpinor) (hs : UnitSpinorEquivariant L χ s)
    (hc : Continuous s) : Continuous (equivariantTorusFrame L s) := by
  apply quotientFiberDescend_continuous (puncturedPlaneProjection_isQuotientMap L)
    (unitSpinorTangentFrame ∘ s) (equivariant_frame_constant_fibers L χ s hs)
  exact (unitNullTangentPairHomeomorph.continuous.comp unitSpinorQuadratic_continuous).comp hc

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.equivariantTorusFrame_continuous

