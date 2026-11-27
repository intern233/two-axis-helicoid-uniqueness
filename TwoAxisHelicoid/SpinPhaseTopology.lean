import TwoAxisHelicoid.AssociatedFrameSpin

namespace TwoAxisHelicoid
open Set Topology

variable {E : Type*} [TopologicalSpace E] (τ : E ≃ₜ E) (hτ : Function.Involutive τ)

/-- The diagonal sign action gives an open quotient map on the two-sheet
cover times the phase circle. -/
theorem spinPhaseMk_isOpenQuotientMap :
    IsOpenQuotientMap (Quotient.mk (spinPhaseSetoid τ hτ)) := by
  let d := τ.prodCongr circleAntipode
  let π := Quotient.mk (spinPhaseSetoid τ hτ)
  refine ⟨Quotient.mk_surjective,continuous_quotient_mk',?_⟩
  intro U hU
  apply isQuotientMap_quotient_mk'.isCoinducing.isOpen_preimage.mp
  have he : π ⁻¹' (π '' U) = U ∪ d ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y,hy,hxy⟩
      rcases Quotient.exact hxy with h | h
      · exact Or.inl (h ▸ hy)
      · right
        change (τ x.1,-x.2) ∈ U
        rwa [← h]
    · rintro (hx | hx)
      · exact ⟨x,hx,rfl⟩
      · exact ⟨d x,hx,Quotient.sound (Or.inr rfl)⟩
  change IsOpen (π ⁻¹' (π '' U))
  rw [he]
  exact hU.union (hU.preimage d.continuous)

theorem associatedFrameSpin_t2 [T2Space E] : T2Space (AssociatedFrameSpin τ hτ) := by
  let π := Quotient.mk (spinPhaseSetoid τ hτ)
  let d := τ.prodCongr circleAntipode
  have hπ := spinPhaseMk_isOpenQuotientMap τ hτ
  apply (t2Space_iff_of_isOpenQuotientMap hπ).mpr
  have he : {q : (E × Circle) × (E × Circle) | π q.1 = π q.2} =
      diagonal (E × Circle) ∪ {v | v.1 = d v.2} := by
    ext x
    change π x.1 = π x.2 ↔ x.1 = x.2 ∨ x.1 = d x.2
    exact Quotient.eq
  rw [he]
  exact isClosed_diagonal.union (isClosed_eq continuous_fst (d.continuous.comp continuous_snd))

theorem associatedSpinPhase_joint_continuous :
    Continuous (fun w : Circle × AssociatedFrameSpin τ hτ => associatedSpinPhase τ hτ w.1 w.2) := by
  let π := Quotient.mk (spinPhaseSetoid τ hτ)
  have h := (IsOpenQuotientMap.id (X := Circle)).prodMap (spinPhaseMk_isOpenQuotientMap τ hτ)
  apply h.isQuotientMap.continuous_iff.mpr
  change Continuous (fun w : Circle × (E × Circle) => π (w.2.1,w.1*w.2.2))
  exact continuous_quotient_mk'.comp (continuous_snd.fst.prodMk (continuous_fst.mul continuous_snd.snd))

theorem associatedSpinPhase_mul (u v : Circle) (x : AssociatedFrameSpin τ hτ) :
    associatedSpinPhase τ hτ (u*v) x = associatedSpinPhase τ hτ u (associatedSpinPhase τ hτ v x) := by
  obtain ⟨w,rfl⟩ := Quotient.exists_rep x
  exact congrArg (fun z : Circle => Quotient.mk (spinPhaseSetoid τ hτ) (w.1,z)) (mul_assoc u v w.2)

noncomputable def associatedSpinDeck : AssociatedFrameSpin τ hτ ≃ₜ AssociatedFrameSpin τ hτ where
  toFun := associatedSpinPhase τ hτ (-1)
  invFun := associatedSpinPhase τ hτ (-1)
  left_inv x := by
    obtain ⟨w,rfl⟩ := Quotient.exists_rep x
    change Quotient.mk _ (w.1,(-1)*((-1)*w.2)) = Quotient.mk _ w
    simp
  right_inv x := by
    obtain ⟨w,rfl⟩ := Quotient.exists_rep x
    change Quotient.mk _ (w.1,(-1)*((-1)*w.2)) = Quotient.mk _ w
    simp
  continuous_toFun := (associatedSpinPhase_joint_continuous τ hτ).comp
    (continuous_const.prodMk continuous_id)
  continuous_invFun := (associatedSpinPhase_joint_continuous τ hτ).comp
    (continuous_const.prodMk continuous_id)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.associatedFrameSpin_t2
#print axioms TwoAxisHelicoid.associatedSpinPhase_joint_continuous
