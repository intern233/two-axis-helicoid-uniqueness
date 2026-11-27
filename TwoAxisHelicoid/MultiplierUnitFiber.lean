import TwoAxisHelicoid.CompactMultiplierSpinBundle
import TwoAxisHelicoid.MultiplierSquareRootFiber

namespace TwoAxisHelicoid
open Set
open scoped TensorProduct
variable (L : PeriodPair) (χ : L.lattice →+ ZMod 2)

noncomputable def compactSpinCoefficient (s : CompactMultiplierSpinBundle L χ)
    (e : LatticeSignCover L χ) : ℂ := by
  classical
  refine Quotient.liftOn s (fun w =>
    if w.1 = e then (w.2 : ℂ) else if latticeSignCoverDeck L χ w.1 = e then -(w.2 : ℂ) else 0) ?_
  rintro x y (rfl | rfl)
  · rfl
  · by_cases h : y.1 = e
    · subst e
      simp [latticeSignCoverDeck_ne,latticeSignCoverDeck_involutive L χ y.1]
    · by_cases h' : latticeSignCoverDeck L χ y.1 = e <;>
        simp [h,h',latticeSignCoverDeck_involutive L χ y.1]

theorem compactSpinCoefficient_own (e : LatticeSignCover L χ) (u : Circle) :
    compactSpinCoefficient L χ (Quotient.mk _ (e,u)) e = (u : ℂ) := by
  classical
  simp [compactSpinCoefficient]

theorem compactSpinCoefficient_opp (e : LatticeSignCover L χ) (u : Circle) :
    compactSpinCoefficient L χ (Quotient.mk _ (e,u)) (latticeSignCoverDeck L χ e) = -(u : ℂ) := by
  classical
  simp [compactSpinCoefficient,Ne.symm (latticeSignCoverDeck_ne L χ e)]

abbrev CompactSpinFiber (b : PeriodTorus L) :=
  {s : CompactMultiplierSpinBundle L χ // (compactMultiplierSpinProjection L χ s).1 = b}

noncomputable def compactSpinFiberMk {b : PeriodTorus L} (e : SignFiber L χ b) (u : Circle) :
    CompactSpinFiber L χ b :=
  ⟨Quotient.mk _ (e.1,u),e.2⟩

theorem compactSpinFiber_representative {b : PeriodTorus L} (s : CompactSpinFiber L χ b) :
    ∃ (e : SignFiber L χ b) (u : Circle), compactSpinFiberMk L χ e u = s := by
  rcases s with ⟨s,hs⟩
  obtain ⟨⟨q,u⟩,rfl⟩ := Quotient.exists_rep s
  exact ⟨⟨q,hs⟩,u,rfl⟩

theorem compactSpinFiber_coeff_deck {b : PeriodTorus L} (s : CompactSpinFiber L χ b)
    (d : SignFiber L χ b) :
    compactSpinCoefficient L χ s.1 (signFiberDeck L χ b d).1 = -compactSpinCoefficient L χ s.1 d.1 := by
  obtain ⟨e,u,rfl⟩ := compactSpinFiber_representative L χ s
  rcases signFiber_cases L χ b e d with hd | hd <;> subst d
  · exact (compactSpinCoefficient_opp L χ e.1 u).trans (congrArg Neg.neg (compactSpinCoefficient_own L χ e.1 u)).symm
  · rw [signFiberDeck_involutive L χ b e]
    change compactSpinCoefficient L χ (Quotient.mk _ (e.1,u)) e.1 =
      -compactSpinCoefficient L χ (Quotient.mk _ (e.1,u)) (latticeSignCoverDeck L χ e.1)
    rw [compactSpinCoefficient_own,compactSpinCoefficient_opp,neg_neg]

theorem compactSpinFiber_coeff_norm {b : PeriodTorus L} (s : CompactSpinFiber L χ b)
    (d : SignFiber L χ b) : ‖compactSpinCoefficient L χ s.1 d.1‖ = 1 := by
  obtain ⟨e,u,rfl⟩ := compactSpinFiber_representative L χ s
  rcases signFiber_cases L χ b e d with hd | hd <;> subst d
  · exact (congrArg norm (compactSpinCoefficient_own L χ e.1 u)).trans u.norm_coe
  · change ‖compactSpinCoefficient L χ (Quotient.mk _ (e.1,u)) (latticeSignCoverDeck L χ e.1)‖ = 1
    rw [compactSpinCoefficient_opp,norm_neg,Circle.norm_coe]

abbrev MultiplierUnitLine (b : PeriodTorus L) :=
  {v : multiplierLineFiber L χ b // ∀ e, ‖v.1 e‖ = 1}

noncomputable def compactSpinFiberVector {b : PeriodTorus L} (s : CompactSpinFiber L χ b) :
    MultiplierUnitLine L χ b :=
  ⟨⟨fun d => compactSpinCoefficient L χ s.1 d.1,compactSpinFiber_coeff_deck L χ s⟩,
    compactSpinFiber_coeff_norm L χ s⟩

theorem compactSpinFiber_coeff_rebuild {b : PeriodTorus L} (d : SignFiber L χ b) (s : CompactSpinFiber L χ b) :
    let u : Circle := ⟨compactSpinCoefficient L χ s.1 d.1,mem_sphere_zero_iff_norm.mpr
      (compactSpinFiber_coeff_norm L χ s d)⟩
    compactSpinFiberMk L χ d u = s := by
  obtain ⟨e,v,rfl⟩ := compactSpinFiber_representative L χ s
  rcases signFiber_cases L χ b e d with hd | hd <;> subst d
  · apply Subtype.ext
    apply Quotient.sound
    left
    exact Prod.ext rfl (Circle.ext (compactSpinCoefficient_own L χ e.1 v))
  · apply Subtype.ext
    apply Quotient.sound
    right
    exact Prod.ext rfl (Circle.ext (compactSpinCoefficient_opp L χ e.1 v))

/-- Fiberwise identification of the compact spin frames with the actual
unit vectors in the sign line. -/
noncomputable def compactSpinUnitLineEquiv (b : PeriodTorus L) :
    CompactSpinFiber L χ b ≃ MultiplierUnitLine L χ b := by
  let h := (latticeSignCoverProjection_isQuotientMap L χ).surjective b
  let p := Classical.choose h
  let d : SignFiber L χ b := ⟨p,Classical.choose_spec h⟩
  refine {
    toFun := compactSpinFiberVector L χ
    invFun := fun f => compactSpinFiberMk L χ d ⟨f.1.1 d,mem_sphere_zero_iff_norm.mpr (f.2 d)⟩
    left_inv := compactSpinFiber_coeff_rebuild L χ d
    right_inv := ?_ }
  intro f
  apply Subtype.ext
  apply (multiplierFiberEval L χ b d).injective
  exact compactSpinCoefficient_own L χ p _

/-- The canonical tensor square of a unit vector is exactly the square
projection of the compact Spin(2) covering, in the trivialization dz. -/
theorem compactSpin_tensor_square {b : PeriodTorus L} (s : CompactSpinFiber L χ b) (d : SignFiber L χ b) :
    let f := (compactSpinFiberVector L χ s).1
    multiplierTensorSquare L χ b d (f ⊗ₜ f) = ((compactMultiplierSpinProjection L χ s.1).2 : ℂ) := by
  obtain ⟨e,u,rfl⟩ := compactSpinFiber_representative L χ s
  rw [← multiplierTensorSquare_independent L χ b e d]
  change compactSpinCoefficient L χ (Quotient.mk _ (e.1,u)) e.1 *
    compactSpinCoefficient L χ (Quotient.mk _ (e.1,u)) e.1 = ((u^2 : Circle) : ℂ)
  rw [compactSpinCoefficient_own,Circle.coe_pow,pow_two]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compactSpinUnitLineEquiv
#print axioms TwoAxisHelicoid.compactSpin_tensor_square
