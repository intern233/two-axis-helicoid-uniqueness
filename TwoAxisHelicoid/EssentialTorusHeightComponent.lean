import TwoAxisHelicoid.TorusClosedCoverLifts
import TwoAxisHelicoid.LevelComponentPhaseLift
import TwoAxisHelicoid.HeightBandsPhaseLifts

namespace TwoAxisHelicoid
open Set

/-- For any continuous real height on a two-torus, at least one connected
component of a level has no simultaneous continuous real lifts of the two
circle coordinates. No regularity of the height or its level set is assumed. -/
theorem marked_height_has_essential_component {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    (H : M ≃ₜ Circle × Circle) {h : M → ℝ} (ch : Continuous h) :
    ∃ (t : ℝ) (x : h ⁻¹' {t}),
      ¬(∃ u v : C(connectedComponent x,ℝ), ∀ q : connectedComponent x,
        normalizedPhase (u q)=(H q.1.1).1 ∧ normalizedPhase (v q)=(H q.1.1).2) := by
  classical
  by_contra fail
  push Not at fail
  have localLifts (t : ℝ) : ∃ O : Set ℝ, IsOpen O ∧ t∈O ∧
      PhaseLiftsOn (Prod.fst ∘ H) (h ⁻¹' O) ∧ PhaseLiftsOn (Prod.snd ∘ H) (h ⁻¹' O) := by
    obtain ⟨A,ca,ta,la⟩ := height_neighborhood_phase_lift ch (continuous_fst.comp H.continuous) t (fun x => by
      obtain ⟨u,v,ok⟩ := fail t x
      exact ⟨u,fun q => (ok q).1⟩)
    obtain ⟨B,cb,tb,lb⟩ := height_neighborhood_phase_lift ch (continuous_snd.comp H.continuous) t (fun x => by
      obtain ⟨u,v,ok⟩ := fail t x
      exact ⟨v,fun q => (ok q).2⟩)
    exact ⟨A∩B,ca.inter cb,⟨ta,tb⟩,la.mono (fun _ p => p.1),lb.mono (fun _ p => p.2)⟩
  obtain ⟨A,B,ca,cb,cover,⟨u,lu⟩,v,lv⟩ := two_closed_sets_from_height_lifts ch _ _ localLifts
  let U := H.symm ⁻¹' A
  let V := H.symm ⁻¹' B
  let ua : C(U,ℝ) := ⟨fun q => u (H.symm q.1),u.continuous.comp (H.symm.continuous.comp continuous_subtype_val)⟩
  let vb : C(V,ℝ) := ⟨fun q => v (H.symm q.1),v.continuous.comp (H.symm.continuous.comp continuous_subtype_val)⟩
  apply torus_closed_cover_lift_obstruction (ca.preimage H.symm.continuous) (cb.preimage H.symm.continuous)
    (fun q => cover (H.symm q)) ua vb
  · intro q
    change normalizedPhase (u (H.symm q.1))=q.1.1
    simpa only [Function.comp_apply,H.apply_symm_apply] using lu (H.symm q.1) q.2
  · intro q
    change normalizedPhase (v (H.symm q.1))=q.1.2
    simpa only [Function.comp_apply,H.apply_symm_apply] using lv (H.symm q.1) q.2

/-- The two standard phases on the product torus give the same obstruction. -/
theorem torus_height_has_essential_component {h : Circle × Circle → ℝ} (ch : Continuous h) :
    ∃ (t : ℝ) (x : h ⁻¹' {t}),
      ¬(∃ u v : C(connectedComponent x,ℝ), ∀ q : connectedComponent x,
        normalizedPhase (u q)=q.1.1.1 ∧ normalizedPhase (v q)=q.1.1.2) :=
  marked_height_has_essential_component (Homeomorph.refl _) ch

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_height_has_essential_component
#print axioms TwoAxisHelicoid.torus_height_has_essential_component
