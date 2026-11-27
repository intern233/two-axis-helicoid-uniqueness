import TwoAxisHelicoid.ExteriorPlaneBase
import Mathlib.Topology.Homeomorph.Lemmas

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology

def fartherExteriorSet {M : Type*} (f : M → ℝ × ℝ) (S : Set M) (B : ℝ) : Set M :=
  S ∩ {q | B < ‖f q‖}

theorem exterior_chart_coordinates_continuousOn {M : Type*} [TopologicalSpace M]
    {S : Set M} {R : ℝ} {f : M → ℝ × ℝ} (E : S ≃ₜ exteriorPlaneBase R)
    (hE : ∀ q : S, (E q).1 = f q.1) : ContinuousOn f S := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun q : S => f q.1)
  have he : (fun q : S => f q.1) = fun q : S => (E q).1 := funext (fun q => (hE q).symm)
  rw [he]
  exact continuous_subtype_val.comp E.continuous

theorem fartherExteriorSet_isOpen {M : Type*} [TopologicalSpace M]
    {S : Set M} {R B : ℝ} {f : M → ℝ × ℝ} (hS : IsOpen S)
    (E : S ≃ₜ exteriorPlaneBase R) (hE : ∀ q : S, (E q).1 = f q.1) :
    IsOpen (fartherExteriorSet f S B) := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  have hc := (exterior_chart_coordinates_continuousOn E hE).continuousAt (hS.mem_nhds hq.1)
  filter_upwards [hS.mem_nhds hq.1,hc.norm.eventually (lt_mem_nhds hq.2)] with p hp hnorm
  exact ⟨hp,hnorm⟩

/-- Restrict the actual end homeomorphism to a farther exterior, keeping
the inverse and the projection formula, rather than postulating a new
end chart. -/
noncomputable def fartherExteriorHomeomorph {M : Type*} [TopologicalSpace M]
    {S : Set M} {R B : ℝ} {f : M → ℝ × ℝ}
    (E : S ≃ₜ exteriorPlaneBase R) (hE : ∀ q : S, (E q).1 = f q.1) (hRB : R < B) :
    fartherExteriorSet f S B ≃ₜ exteriorPlaneBase B where
  toFun q := ⟨(E ⟨q.1,q.2.1⟩).1,by
    change B < ‖(E ⟨q.1,q.2.1⟩).1‖
    rw [hE]
    exact q.2.2⟩
  invFun p := ⟨(E.symm ⟨p.1,hRB.trans p.2⟩).1,
    (E.symm ⟨p.1,hRB.trans p.2⟩).2,by
      change B < ‖f (E.symm ⟨p.1,hRB.trans p.2⟩).1‖
      rw [← hE,E.apply_symm_apply]
      exact p.2⟩
  left_inv q := by
    apply Subtype.ext
    change (E.symm (E ⟨q.1,q.2.1⟩)).1 = q.1
    rw [E.symm_apply_apply]
  right_inv p := by
    apply Subtype.ext
    change (E (E.symm ⟨p.1,hRB.trans p.2⟩)).1 = p.1
    rw [E.apply_symm_apply]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (E.continuous.comp
      (continuous_subtype_val.subtype_mk (fun q => q.2.1)))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (E.symm.continuous.comp
      (continuous_subtype_val.subtype_mk (fun p : exteriorPlaneBase B => hRB.trans p.2)))

theorem fartherExteriorHomeomorph_coordinates {M : Type*} [TopologicalSpace M]
    {S : Set M} {R B : ℝ} {f : M → ℝ × ℝ}
    (E : S ≃ₜ exteriorPlaneBase R) (hE : ∀ q : S, (E q).1 = f q.1) (hRB : R < B)
    (q : fartherExteriorSet f S B) : (fartherExteriorHomeomorph E hE hRB q).1 = f q.1 :=
  hE ⟨q.1,q.2.1⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.fartherExteriorHomeomorph
