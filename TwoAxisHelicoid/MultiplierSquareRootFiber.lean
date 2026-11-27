import TwoAxisHelicoid.LatticeSignDoubleCover
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace TwoAxisHelicoid
open scoped TensorProduct

variable (L : PeriodPair) (χ : L.lattice →+ ZMod 2) (b : PeriodTorus L)

abbrev SignFiber := {e : LatticeSignCover L χ // latticeSignCoverProjection L χ e = b}

noncomputable def signFiberDeck (e : SignFiber L χ b) : SignFiber L χ b :=
  ⟨latticeSignCoverDeck L χ e.1,(latticeSignCoverProjection_deck L χ _).trans e.2⟩

theorem signFiberDeck_involutive : Function.Involutive (signFiberDeck L χ b) :=
  fun e => Subtype.ext (latticeSignCoverDeck_involutive L χ e.1)

theorem signFiberDeck_ne (e : SignFiber L χ b) : signFiberDeck L χ b e ≠ e :=
  fun h => latticeSignCoverDeck_ne L χ _ (congrArg Subtype.val h)

theorem signFiber_cases (e d : SignFiber L χ b) : d = e ∨ d = signFiberDeck L χ b e := by
  rcases (latticeSignCoverProjection_fibers L χ d.1 e.1).mp (d.2.trans e.2.symm) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- The associated complex line as the odd functions on the actual two
sheets over a point. This description keeps its canonical tensor square. -/
noncomputable def multiplierLineFiber : Submodule ℂ (SignFiber L χ b → ℂ) where
  carrier := {f | ∀ e, f (signFiberDeck L χ b e) = -f e}
  zero_mem' _ := neg_zero.symm
  add_mem' hf hg e := by simp only [Pi.add_apply,hf e,hg e,neg_add]
  smul_mem' k f hf e := by
    change k • f (signFiberDeck L χ b e) = -(k • f e)
    rw [hf e,smul_neg]

noncomputable def multiplierFiberEval (e : SignFiber L χ b) : multiplierLineFiber L χ b ≃ₗ[ℂ] ℂ := by
  classical
  exact {
    toFun := fun f => f.1 e
    invFun := fun z => ⟨fun d => if d = e then z else -z,by
      intro d
      rcases signFiber_cases L χ b e d with rfl | rfl
      · simp [signFiberDeck_ne]
      · simp [signFiberDeck_ne,signFiberDeck_involutive L χ b e]⟩
    left_inv := by
      intro f
      apply Subtype.ext
      funext d
      rcases signFiber_cases L χ b e d with rfl | rfl
      · simp
      · simp [signFiberDeck_ne,f.2 e]
    right_inv := fun z => ite_eq_left rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

theorem multiplierFiberEval_apply (e : SignFiber L χ b) (f : multiplierLineFiber L χ b) :
    multiplierFiberEval L χ b e f = f.1 e := rfl

theorem multiplierLineFiber_finrank : Module.finrank ℂ (multiplierLineFiber L χ b) = 1 := by
  obtain ⟨e,he⟩ := (latticeSignCoverProjection_isQuotientMap L χ).surjective b
  rw [(multiplierFiberEval L χ b ⟨e,he⟩).finrank_eq,Module.finrank_self]

/-- Tensoring the sign line with itself gives the coefficient line of
the globally defined differential dz on a marked flat torus. -/
noncomputable def multiplierTensorSquare (e : SignFiber L χ b) :
    (multiplierLineFiber L χ b ⊗[ℂ] multiplierLineFiber L χ b) ≃ₗ[ℂ] ℂ :=
  (TensorProduct.congr (multiplierFiberEval L χ b e) (multiplierFiberEval L χ b e)).trans
    (TensorProduct.lid ℂ ℂ)

theorem multiplierTensorSquare_tmul (e : SignFiber L χ b) (f g : multiplierLineFiber L χ b) :
    multiplierTensorSquare L χ b e (f ⊗ₜ g) = f.1 e*g.1 e := rfl

theorem multiplierTensorSquare_independent (e d : SignFiber L χ b) :
    multiplierTensorSquare L χ b e = multiplierTensorSquare L χ b d := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext'
  intro f g
  change f.1 e*g.1 e = f.1 d*g.1 d
  rcases signFiber_cases L χ b e d with rfl | rfl
  · rfl
  · rw [f.2 e,g.2 e,neg_mul_neg]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.multiplierLineFiber_finrank
#print axioms TwoAxisHelicoid.multiplierTensorSquare_independent
