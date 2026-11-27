import TwoAxisHelicoid.SpinPhaseTopology
import TwoAxisHelicoid.WeierstrassFrameSpinBundle

namespace TwoAxisHelicoid
open Set Topology

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (τ : E ≃ₜ E) (hτ : Function.Involutive τ)
    (p : E → B) (hpτ : ∀ e, p (τ e) = p e)

/-- In a fixed oriented trivialization, the spin projection squares the
phase. The sign change of the covering sheet leaves this projection invariant. -/
noncomputable def associatedSpinProjection : AssociatedFrameSpin τ hτ → B × Circle :=
  Quotient.lift (fun e => (p e.1,e.2^2)) (by
    rintro x y (rfl | rfl)
    · rfl
    · exact Prod.ext (hpτ y.1) ((circle_square_fibers _ _).mpr (Or.inr rfl)))

theorem associatedSpinProjection_isOpenQuotientMap (hp : IsOpenQuotientMap p) :
    IsOpenQuotientMap (associatedSpinProjection τ hτ p hpτ) := by
  apply (spinPhaseMk_isOpenQuotientMap τ hτ).of_comp_iff.mp
  exact hp.prodMap ⟨circle_square_surjective,circle_square_isCoveringMap.continuous,
    circle_square_isCoveringMap.isOpenMap⟩

theorem associatedSpinDeck_mk (e : E) (u : Circle) :
    associatedSpinDeck τ hτ (Quotient.mk _ (e,u)) = Quotient.mk _ (e,-u) := by
  change Quotient.mk _ (e,(-1)*u) = _
  rw [neg_one_mul]

theorem associatedSpinDeck_involutive : Function.Involutive (associatedSpinDeck τ hτ) := by
  intro x
  obtain ⟨⟨e,u⟩,rfl⟩ := Quotient.exists_rep x
  rw [associatedSpinDeck_mk,associatedSpinDeck_mk,neg_neg]

theorem associatedSpinDeck_ne (hne : ∀ e, τ e ≠ e) (x : AssociatedFrameSpin τ hτ) :
    associatedSpinDeck τ hτ x ≠ x := by
  obtain ⟨⟨e,u⟩,rfl⟩ := Quotient.exists_rep x
  rw [associatedSpinDeck_mk]
  intro h
  rcases Quotient.exact h with h | h
  · exact Circle.neg_ne_self u (congrArg Prod.snd h)
  · exact hne e (congrArg Prod.fst h).symm

omit [TopologicalSpace B] in
theorem associatedSpinProjection_fibers
    (hfib : ∀ x y, p x = p y ↔ x = y ∨ x = τ y) (v w : AssociatedFrameSpin τ hτ) :
    associatedSpinProjection τ hτ p hpτ v = associatedSpinProjection τ hτ p hpτ w ↔
      v = w ∨ v = associatedSpinDeck τ hτ w := by
  obtain ⟨⟨x,u⟩,rfl⟩ := Quotient.exists_rep v
  obtain ⟨⟨y,v⟩,rfl⟩ := Quotient.exists_rep w
  rw [associatedSpinDeck_mk]
  change ((p x,u^2) = (p y,v^2)) ↔ _
  constructor
  · intro h
    rcases (hfib x y).mp (congrArg Prod.fst h) with rfl | rfl <;>
      rcases (circle_square_fibers u v).mp (congrArg Prod.snd h) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr (Quotient.sound (Or.inr (Prod.ext rfl (neg_neg _).symm)))
    · exact Or.inl (Quotient.sound (Or.inr rfl))
  · rintro (h | h)
    · exact congrArg (associatedSpinProjection τ hτ p hpτ) h
    · have h' := congrArg (associatedSpinProjection τ hτ p hpτ) h
      exact h'.trans (Prod.ext rfl ((circle_square_fibers _ _).mpr (Or.inr rfl)))

theorem associatedSpinProjection_isCoveringMap [T2Space E]
    (hne : ∀ e, τ e ≠ e) (hp : IsOpenQuotientMap p)
    (hfib : ∀ x y, p x = p y ↔ x = y ∨ x = τ y) :
    IsCoveringMap (associatedSpinProjection τ hτ p hpτ) := by
  let := associatedFrameSpin_t2 τ hτ
  exact free_involution_quotient_isCoveringMap (associatedSpinDeck τ hτ)
    (associatedSpinDeck_involutive τ hτ) (associatedSpinDeck_ne τ hτ hne)
    (associatedSpinProjection_isOpenQuotientMap τ hτ p hpτ hp).isQuotientMap
    (associatedSpinProjection_fibers τ hτ p hpτ hfib)

omit [TopologicalSpace B] in
theorem associatedSpinProjection_phase (u : Circle) (x : AssociatedFrameSpin τ hτ) :
    associatedSpinProjection τ hτ p hpτ (associatedSpinPhase τ hτ u x) =
      ((associatedSpinProjection τ hτ p hpτ x).1,u^2*(associatedSpinProjection τ hτ p hpτ x).2) := by
  obtain ⟨⟨e,v⟩,rfl⟩ := Quotient.exists_rep x
  exact Prod.ext rfl (mul_pow _ _ _)

theorem associatedSpinPhase_injective_at (hne : ∀ e, τ e ≠ e) (x : AssociatedFrameSpin τ hτ) :
    Function.Injective (fun u => associatedSpinPhase τ hτ u x) := by
  obtain ⟨⟨e,v⟩,rfl⟩ := Quotient.exists_rep x
  intro u w h
  rcases Quotient.exact h with h | h
  · exact mul_right_cancel (show u*v = w*v from congrArg Prod.snd h)
  · exact False.elim (hne e (congrArg Prod.fst h).symm)

omit [TopologicalSpace B] in
/-- Each base-point fiber is a principal Spin(2) circle: any two spin
frames over the same point differ by exactly one phase. -/
theorem associatedSpinPhase_torsor (hne : ∀ e, τ e ≠ e)
    (hfib : ∀ x y, p x = p y ↔ x = y ∨ x = τ y)
    (x y : AssociatedFrameSpin τ hτ) :
    (associatedSpinProjection τ hτ p hpτ x).1 = (associatedSpinProjection τ hτ p hpτ y).1 ↔
      ∃! u : Circle, associatedSpinPhase τ hτ u x = y := by
  constructor
  · intro h
    obtain ⟨⟨e,v⟩,rfl⟩ := Quotient.exists_rep x
    obtain ⟨⟨d,w⟩,rfl⟩ := Quotient.exists_rep y
    have hex (u : Circle) (hu : associatedSpinPhase τ hτ u (Quotient.mk _ (e,v)) =
        Quotient.mk _ (d,w)) : ∃! s : Circle, associatedSpinPhase τ hτ s (Quotient.mk _ (e,v)) =
        Quotient.mk _ (d,w) :=
      ⟨u,hu,fun _ hs => associatedSpinPhase_injective_at τ hτ hne _ (hs.trans hu.symm)⟩
    rcases (hfib e d).mp h with rfl | rfl
    · apply hex (w/v)
      exact Quotient.sound (Or.inl (Prod.ext rfl (div_mul_cancel w v)))
    · apply hex ((-w)/v)
      exact Quotient.sound (Or.inr (Prod.ext rfl (div_mul_cancel (-w) v)))
  · rintro ⟨u,hu,_⟩
    rw [← hu,associatedSpinProjection_phase]

abbrev CompactMultiplierSpinBundle (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :=
  AssociatedFrameSpin (latticeSignCoverDeck L χ) (latticeSignCoverDeck_involutive L χ)

noncomputable def compactMultiplierSpinProjection (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    CompactMultiplierSpinBundle L χ → PeriodTorus L × Circle :=
  associatedSpinProjection _ (latticeSignCoverDeck_involutive L χ) _
    (latticeSignCoverProjection_deck L χ)

/-- The multiplier spin cover exists over all oriented flat tangent frames
of the compact torus, including the previously removed fiber. -/
theorem compactMultiplierSpinProjection_isCoveringMap (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    IsCoveringMap (compactMultiplierSpinProjection L χ) :=
  associatedSpinProjection_isCoveringMap _ (latticeSignCoverDeck_involutive L χ) _
    (latticeSignCoverProjection_deck L χ) (latticeSignCoverDeck_ne L χ)
    (.of_isOpenMap_isQuotientMap (latticeSignCoverProjection_isCoveringMap L χ).isOpenMap
      (latticeSignCoverProjection_isQuotientMap L χ)) (latticeSignCoverProjection_fibers L χ)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compactMultiplierSpinProjection_isCoveringMap
