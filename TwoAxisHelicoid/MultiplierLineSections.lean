import TwoAxisHelicoid.MultiplierSquareRootFiber
import TwoAxisHelicoid.LatticeSignMonodromy
import TwoAxisHelicoid.SpinorLatticeCharacter

namespace TwoAxisHelicoid
open Complex

variable (L : PeriodPair) (χ : L.lattice →+ ZMod 2)

abbrev MultiplierLineSection := ∀ b, multiplierLineFiber L χ b

noncomputable def multiplierSectionEval (S : MultiplierLineSection L χ) (e : LatticeSignCover L χ) : ℂ :=
  (S (latticeSignCoverProjection L χ e)).1 ⟨e,rfl⟩

theorem multiplierSectionEval_at (S : MultiplierLineSection L χ) (b : PeriodTorus L)
    (e : SignFiber L χ b) : multiplierSectionEval L χ S e.1 = (S b).1 e := by
  rcases e with ⟨e,rfl⟩
  rfl

theorem multiplierSectionEval_deck (S : MultiplierLineSection L χ) (e : LatticeSignCover L χ) :
    multiplierSectionEval L χ S (latticeSignCoverDeck L χ e) = -multiplierSectionEval L χ S e := by
  let d : SignFiber L χ (latticeSignCoverProjection L χ e) := ⟨e,rfl⟩
  exact (multiplierSectionEval_at L χ S _ (signFiberDeck L χ _ d)).trans ((S _).2 d)

noncomputable def multiplierSectionPlane (S : MultiplierLineSection L χ) (z : ℂ) : ℂ :=
  multiplierSectionEval L χ S (latticeSignCoverMk L χ (z,0))

theorem multiplierSectionEval_mk (S : MultiplierLineSection L χ) (z : ℂ) (σ : ZMod 2) :
    multiplierSectionEval L χ S (latticeSignCoverMk L χ (z,σ)) =
      paritySign σ*multiplierSectionPlane L χ S z := by
  rcases zmod_two_cases σ with rfl | rfl
  · rw [paritySign_zero,one_mul]; rfl
  · have h := multiplierSectionEval_deck L χ S (latticeSignCoverMk L χ (z,0))
    rw [latticeSignCoverDeck_mk,zero_add] at h
    rw [paritySign_one,neg_one_mul]
    exact h

theorem multiplierSectionPlane_translate (S : MultiplierLineSection L χ) (z : ℂ) (ω : L.lattice) :
    multiplierSectionPlane L χ S (z+ω.1) = paritySign (χ ω)*multiplierSectionPlane L χ S z := by
  change multiplierSectionEval L χ S (latticeSignCoverMk L χ (z+ω.1,0)) = _
  rw [latticeSignCoverMk_translate,multiplierSectionEval_mk]
  rcases zmod_two_cases (χ ω) with h | h <;> rw [h] <;> rfl

theorem multiplierSectionPlane_injective : Function.Injective (multiplierSectionPlane L χ) := by
  intro S T he
  funext b
  apply Subtype.ext
  funext d
  rw [← multiplierSectionEval_at L χ S b d,← multiplierSectionEval_at L χ T b d]
  obtain ⟨v,hv⟩ := Quotient.exists_rep d.1
  change latticeSignCoverMk L χ v = d.1 at hv
  rw [← hv,multiplierSectionEval_mk,multiplierSectionEval_mk,he]

/-- A scalar with the required lattice transformation law descends to
an actual section, with values in the one-dimensional multiplier fibers. -/
noncomputable def multiplierScalarDescent (f : ℂ → ℂ)
    (hf : ∀ z (ω : L.lattice), f (z+ω.1) = paritySign (χ ω)*f z) :
    LatticeSignCover L χ → ℂ :=
  Quotient.lift (fun x : ℂ × ZMod 2 => paritySign x.2*f x.1) (by
    intro x y h
    obtain ⟨ω,hw,hσ⟩ := (latticeSignCoverMk_eq L χ x y).mp (Quotient.sound h)
    have hx : x.1 = y.1+ω.1 := by rw [← hw]; ring
    have hy : x.2 = y.2+χ ω := by rw [← hσ]; ring
    rw [hx,hy,paritySign_add,hf y.1 ω]
    linear_combination paritySign y.2*f y.1*(paritySign_sq (χ ω)))

theorem multiplierScalarDescent_deck (f : ℂ → ℂ)
    (hf : ∀ z (ω : L.lattice), f (z+ω.1) = paritySign (χ ω)*f z)
    (e : LatticeSignCover L χ) :
    multiplierScalarDescent L χ f hf (latticeSignCoverDeck L χ e) = -multiplierScalarDescent L χ f hf e := by
  obtain ⟨v,rfl⟩ := Quotient.exists_rep e
  change multiplierScalarDescent L χ f hf (latticeSignCoverDeck L χ (latticeSignCoverMk L χ v)) = _
  rw [latticeSignCoverDeck_mk]
  change paritySign (v.2+1)*f v.1 = -(paritySign v.2*f v.1)
  rw [paritySign_add,paritySign_one]; ring

noncomputable def multiplierSectionFromScalar (f : ℂ → ℂ)
    (hf : ∀ z (ω : L.lattice), f (z+ω.1) = paritySign (χ ω)*f z) : MultiplierLineSection L χ :=
  fun _ => ⟨fun d => multiplierScalarDescent L χ f hf d.1,
    fun d => multiplierScalarDescent_deck L χ f hf d.1⟩

theorem multiplierSectionFromScalar_plane (f : ℂ → ℂ)
    (hf : ∀ z (ω : L.lattice), f (z+ω.1) = paritySign (χ ω)*f z) :
    multiplierSectionPlane L χ (multiplierSectionFromScalar L χ f hf) = f := by
  funext z
  change paritySign 0*f z = f z
  rw [paritySign_zero,one_mul]

/-- Holomorphicity is measured in the plane trivialization of the flat
line. The other sheet changes every coefficient by the constant -1. -/
noncomputable def holomorphicMultiplierSections : Submodule ℂ (MultiplierLineSection L χ) where
  carrier := {s | Differentiable ℂ (multiplierSectionPlane L χ s)}
  zero_mem' := differentiable_const 0
  add_mem' := fun hs ht => hs.add ht
  smul_mem' := fun k _ hs => hs.const_smul k

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.multiplierSectionPlane_injective
#print axioms TwoAxisHelicoid.multiplierSectionFromScalar_plane
