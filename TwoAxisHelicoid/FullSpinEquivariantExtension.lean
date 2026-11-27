import TwoAxisHelicoid.FullSpinCoverExtension
import TwoAxisHelicoid.ImmersionSpinExtension

namespace TwoAxisHelicoid
open Set Topology

/-- A cover isomorphism preserving the Spin(2) rotations off the
puncture extends uniquely as an equivariant isomorphism of the full
frame coverings. Connectedness forces commutation on the removed fiber. -/
theorem punctured_full_spin_equivariant_extends (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    {E : Type*} [TopologicalSpace E] {p : E → PeriodTorus L × Circle} (hp : IsCoveringMap p)
    (A : Circle → E → E) (hAc : ∀ u, Continuous (A u))
    (hAp : ∀ u e, p (A u e) = ((p e).1,u^2*(p e).2))
    (h : RestrictedCompactMultiplierSpin L χ ≃ₜ {e : E // (p e).1 ≠ 0})
    (hh : ∀ s, p (h s).1 = compactMultiplierSpinProjection L χ s.1)
    (hphase : ∀ u s, (h (restrictedCompactSpinPhase L χ u s)).1 = A u (h s).1) :
    ∃! H : CompactMultiplierSpinBundle L χ ≃ₜ E,
      (∀ s, p (H s) = compactMultiplierSpinProjection L χ s) ∧
      (∀ s : RestrictedCompactMultiplierSpin L χ, H s.1 = (h s).1) ∧
      ∀ u s, H (associatedSpinPhase _ (latticeSignCoverDeck_involutive L χ) u s) = A u (H s) := by
  obtain ⟨H,⟨hHp,hHr⟩,hHu⟩ := punctured_full_spin_homeomorph_extends L χ hp h hh
  refine ⟨H,⟨hHp,hHr,?_⟩,fun K hK => hHu K ⟨hK.1,hK.2.1⟩⟩
  intro u
  let σ := associatedSpinPhase _ (latticeSignCoverDeck_involutive L χ) u
  let P := compactMultiplierSpinProjection L χ
  have hσ : Continuous σ := (associatedSpinPhase_joint_continuous _ (latticeSignCoverDeck_involutive L χ)).comp
    (f := fun s : CompactMultiplierSpinBundle L χ => (u,s)) (continuous_const.prodMk continuous_id)
  have hσp (s) : P (σ s) = ((P s).1,u^2*(P s).2) :=
    associatedSpinProjection_phase _ (latticeSignCoverDeck_involutive L χ) _
      (latticeSignCoverProjection_deck L χ) u s
  obtain ⟨hPsurj,hPc,_⟩ := compactSpinPlaneMk_isOpenQuotientMap L χ
  let : PathConnectedSpace (CompactMultiplierSpinBundle L χ) := hPsurj.pathConnectedSpace hPc
  let s₀ := puncturedCompactSpinPlaneMk L χ (puncturedBasisLine L 0 0,0)
  have h0 : H (σ s₀.1) = A u (H s₀.1) :=
    (hHr (restrictedCompactSpinPhase L χ u s₀)).trans ((hphase u s₀).trans (congrArg (A u) (hHr s₀)).symm)
  have he : (fun s => H (σ s)) = fun s => A u (H s) := by
    apply hp.eq_of_comp_eq (H.continuous.comp hσ) ((hAc u).comp H.continuous) _ s₀.1 h0
    funext s
    change p (H (σ s)) = p (A u (H s))
    rw [hHp,hAp,hHp]
    exact hσp s
  exact congrFun he

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_full_spin_equivariant_extends
