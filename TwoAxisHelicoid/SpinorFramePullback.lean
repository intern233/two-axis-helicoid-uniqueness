import TwoAxisHelicoid.EquivariantTorusFrame
import TwoAxisHelicoid.PuncturedSignCover
import TwoAxisHelicoid.PullbackLocalHomeomorph

namespace TwoAxisHelicoid
open Set Topology

theorem zmod_two_neg (g : ZMod 2) : -g = g := by
  rcases zmod_two_cases g with rfl | rfl <;> decide

theorem zmod_two_add_self (g : ZMod 2) : g+g = 0 := by
  rcases zmod_two_cases g with rfl | rfl <;> decide

theorem unitSpinor_vadd_injective (s : UnitSpinor) :
    Function.Injective (fun g : ZMod 2 => g +ᵥ s) := by
  let : IsCancelVAdd (ZMod 2) UnitSpinor :=
    unitSpinorQuadratic_isQuotientCoveringMap.isCancelVAdd
  exact fun _ _ h => IsCancelVAdd.right_cancel _ _ s h

abbrev TorusFramePullback (L : PeriodPair) (s : PuncturedLatticePlane L → UnitSpinor) :=
  CoverPullback (equivariantTorusFrame L s) unitSpinorTangentFrame

noncomputable def spinorFramePullbackMk (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (s : PuncturedLatticePlane L → UnitSpinor) (hs : UnitSpinorEquivariant L χ s) :
    PuncturedLatticePlane L × ZMod 2 → TorusFramePullback L s :=
  fun v => ⟨(puncturedPlaneProjection L v.1,v.2 +ᵥ s v.1),
    (equivariantTorusFrame_projection L χ s hs v.1).trans
      (unitSpinorTangentFrame_vadd v.2 (s v.1)).symm⟩

theorem spinorFramePullbackMk_continuous (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (s : PuncturedLatticePlane L → UnitSpinor) (hs : UnitSpinorEquivariant L χ s)
    (hc : Continuous s) : Continuous (spinorFramePullbackMk L χ s hs) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact (puncturedPlaneProjection_continuous L).comp continuous_fst
  · rw [continuous_prod_of_discrete_right]
    intro g
    exact hc.const_vadd g

theorem spinorFramePullbackMk_surjective (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (s : PuncturedLatticePlane L → UnitSpinor) (hs : UnitSpinorEquivariant L χ s) :
    Function.Surjective (spinorFramePullbackMk L χ s hs) := by
  intro q
  obtain ⟨z,hz⟩ := puncturedPlaneProjection_surjective L q.1.1
  have he : unitSpinorTangentFrame q.1.2 = unitSpinorTangentFrame (s z) := calc
    unitSpinorTangentFrame q.1.2 = equivariantTorusFrame L s q.1.1 := q.2.symm
    _ = equivariantTorusFrame L s (puncturedPlaneProjection L z) := congrArg _ hz.symm
    _ = unitSpinorTangentFrame (s z) := equivariantTorusFrame_projection L χ s hs z
  rcases unitSpinorTangentFrame_fibers.mp he with he | he
  · refine ⟨(z,0),Subtype.ext (Prod.ext hz ?_)⟩
    change (0 : ZMod 2) +ᵥ s z = q.1.2
    simpa only [zero_vadd] using he.symm
  · refine ⟨(z,1),Subtype.ext (Prod.ext hz ?_)⟩
    change (1 : ZMod 2) +ᵥ s z = q.1.2
    simpa only [unitSpinor_vadd_one] using he.symm

theorem spinorFramePullbackMk_fibers (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (s : PuncturedLatticePlane L → UnitSpinor) (hs : UnitSpinorEquivariant L χ s)
    (v w : PuncturedLatticePlane L × ZMod 2) :
    spinorFramePullbackMk L χ s hs v = spinorFramePullbackMk L χ s hs w ↔
      puncturedSignCoverMk L χ v = puncturedSignCoverMk L χ w := by
  rw [puncturedSignCoverMk_eq]
  constructor
  · intro he
    have hb : puncturedPlaneProjection L v.1 = puncturedPlaneProjection L w.1 :=
      congrArg (fun q : TorusFramePullback L s => q.1.1) he
    let ω : L.lattice := ⟨v.1.1-w.1.1,(puncturedPlaneProjection_eq_iff L v.1 w.1).mp hb⟩
    have hz : v.1.1 = w.1.1+ω.1 := by dsimp [ω]; ring
    have hv : v.2 +ᵥ s v.1 = w.2 +ᵥ s w.1 :=
      congrArg (fun q : TorusFramePullback L s => q.1.2) he
    rw [hs ω w.1 v.1 hz,← add_vadd] at hv
    have heq := unitSpinor_vadd_injective (s w.1) hv
    refine ⟨ω,rfl,?_⟩
    have hh : v.2-w.2 = -(χ ω) := by rw [← heq]; abel
    exact hh.trans (zmod_two_neg _)
  · rintro ⟨ω,hω,hg⟩
    have hb : puncturedPlaneProjection L v.1 = puncturedPlaneProjection L w.1 :=
      (puncturedPlaneProjection_eq_iff L v.1 w.1).mpr (hω ▸ ω.2)
    have hz : v.1.1 = w.1.1+ω.1 := by rw [← hω]; ring
    apply Subtype.ext
    apply Prod.ext hb
    change v.2 +ᵥ s v.1 = w.2 +ᵥ s w.1
    rw [hs ω w.1 v.1 hz,← add_vadd]
    have heq : v.2+χ ω = w.2 := by
      rw [← hg]
      have hh : v.2+(v.2-w.2) = (v.2+v.2)-w.2 := by abel
      rw [hh,zmod_two_add_self,zero_sub,zmod_two_neg]
    rw [heq]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.spinorFramePullbackMk_fibers

