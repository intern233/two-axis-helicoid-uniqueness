import TwoAxisHelicoid.RotatedFramePullback
import Mathlib.Topology.Homeomorph.Quotient

namespace TwoAxisHelicoid
open Set Topology

/-- Extension of a two-sheeted cover by the central subgroup of Spin(2).
The diagonal sign changes the sheet and negates the unit phase. -/
def spinPhaseSetoid {E : Type*} (τ : E → E) (hτ : Function.Involutive τ) :
    Setoid (E × Circle) where
  r v w := v = w ∨ v = (τ w.1,-w.2)
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      rintro x y (rfl | rfl)
      · exact Or.inl rfl
      · right
        simp [hτ y.1]
    trans := by
      rintro x y z (rfl | rfl) h
      · exact h
      · rcases h with rfl | rfl
        · exact Or.inr rfl
        · left
          simp [hτ z.1] }

abbrev AssociatedFrameSpin {E : Type*} (τ : E → E) (hτ : Function.Involutive τ) :=
  Quotient (spinPhaseSetoid τ hτ)

noncomputable def associatedSpinPhase {E : Type*} (τ : E → E) (hτ : Function.Involutive τ)
    (v : Circle) : AssociatedFrameSpin τ hτ → AssociatedFrameSpin τ hτ :=
  Quotient.map (fun x => (x.1,v*x.2)) (by
    rintro x y (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Prod.ext rfl (mul_neg _ _)))

variable {B E : Type*} [TopologicalSpace B] [TopologicalSpace E]
variable (f : B → OrthonormalTangentPair) (hf : Continuous f)
variable (τ : E → E) (hτ : Function.Involutive τ)
variable (e : E ≃ₜ QuaternionFramePullback f)
variable (he : ∀ x, e (τ x) = quaternionFramePullbackDeck f (e x))

noncomputable def associatedFrameSpinHomeomorph :
    AssociatedFrameSpin τ hτ ≃ₜ QuaternionFramePullback (rotatedFrameFamily f) := by
  let d := e.prodCongr (Homeomorph.refl Circle)
  let k : C(E × Circle,QuaternionFramePullback (rotatedFrameFamily f)) :=
    ⟨rotatedFrameLiftMk f ∘ d,(rotatedFrameLiftMk_continuous f).comp d.continuous⟩
  have hk : IsQuotientMap k :=
    ((rotatedFrameLiftMk_isLocalHomeomorph f hf).isOpenMap.isQuotientMap
      (rotatedFrameLiftMk_continuous f) (rotatedFrameLiftMk_surjective f)).comp d.isQuotientMap
  refine (Homeomorph.Quotient.congrRight (r' := Setoid.ker k) ?_).trans hk.homeomorph
  intro x y
  change (x = y ∨ x = (τ y.1,-y.2)) ↔ rotatedFrameLiftMk f (d x) = rotatedFrameLiftMk f (d y)
  rw [rotatedFrameLiftMk_fibers, d.injective.eq_iff]
  have hd : (quaternionFramePullbackDeck f (d y).1,-(d y).2) = d (τ y.1,-y.2) := by
    exact Prod.ext (he y.1).symm rfl
  rw [hd,d.injective.eq_iff]

theorem associatedFrameSpinHomeomorph_mk (x : E × Circle) :
    associatedFrameSpinHomeomorph f hf τ hτ e he (Quotient.mk _ x) =
      rotatedFrameLiftMk f (e x.1,x.2) := rfl

/-- The homeomorphism preserves the map to the rotated-frame bundle:
rotating a spin frame by a unit phase rotates its projected frame by its square. -/
theorem associatedFrameSpinHomeomorph_square (x : E × Circle) (v : Circle) :
    (associatedFrameSpinHomeomorph f hf τ hτ e he
      (associatedSpinPhase τ hτ v (Quotient.mk _ x))).1.1 =
      ((e x.1).1.1,v^2*x.2^2) := by
  change ((e x.1).1.1,(v*x.2)^2) = _
  rw [mul_pow]

theorem associatedFrameSpinHomeomorph_phase (v : Circle) (x : AssociatedFrameSpin τ hτ) :
    (associatedFrameSpinHomeomorph f hf τ hτ e he (associatedSpinPhase τ hτ v x)).1.2 =
      spinCircleAction v (associatedFrameSpinHomeomorph f hf τ hτ e he x).1.2 := by
  obtain ⟨w,rfl⟩ := Quotient.exists_rep x
  exact spinCircleAction_mul v w.2 (e w.1).1.2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.associatedFrameSpinHomeomorph
#print axioms TwoAxisHelicoid.associatedFrameSpinHomeomorph_phase
