import TwoAxisHelicoid.UnitSpinorFrames
import Mathlib.Topology.Covering.Quotient
import Mathlib.Data.ZMod.Basic

namespace TwoAxisHelicoid
open Set Metric Topology
open scoped Topology
set_option maxHeartbeats 1000000

theorem zmod_two_cases (g : ZMod 2) : g = 0 ∨ g = 1 := by
  have hg : g.val = 0 ∨ g.val = 1 := by
    have := ZMod.val_lt g
    omega
  rcases hg with hg | hg
  · exact Or.inl (ZMod.val_injective 2 (by simpa using hg))
  · exact Or.inr (ZMod.val_injective 2 (by simpa [ZMod.val_one_eq_one_mod] using hg))

noncomputable instance unitSpinor_signAction : AddAction (ZMod 2) UnitSpinor where
  vadd g s := if g = 0 then s else unitSpinorAntipode s
  zero_vadd s := by
    change (if (0 : ZMod 2) = 0 then s else unitSpinorAntipode s) = s
    simp
  add_vadd g h s := by
    change (if g+h = 0 then s else unitSpinorAntipode s) =
      (if g = 0 then (if h = 0 then s else unitSpinorAntipode s)
        else unitSpinorAntipode (if h = 0 then s else unitSpinorAntipode s))
    rcases zmod_two_cases g with rfl | rfl <;> rcases zmod_two_cases h with rfl | rfl <;>
      simp [show (1 : ZMod 2)+1 = 0 from by decide,unitSpinorAntipode_involutive]

theorem unitSpinor_vadd_one (s : UnitSpinor) : (1 : ZMod 2) +ᵥ s = unitSpinorAntipode s := by
  change (if (1 : ZMod 2) = 0 then s else unitSpinorAntipode s) = _
  norm_num

instance unitSpinor_continuous_signAction : ContinuousConstVAdd (ZMod 2) UnitSpinor where
  continuous_const_vadd g := by
    rcases zmod_two_cases g with rfl | rfl
    · simpa only [zero_vadd] using! (continuous_id : Continuous (id : UnitSpinor → UnitSpinor))
    · simpa only [unitSpinor_vadd_one] using! unitSpinorAntipode.continuous

theorem unitSpinor_sign_orbit {s t : UnitSpinor} :
    s ∈ AddAction.orbit (ZMod 2) t ↔ s = t ∨ s = unitSpinorAntipode t := by
  constructor
  · rintro ⟨g,hg⟩
    rcases zmod_two_cases g with rfl | rfl
    · exact Or.inl (by simpa only [zero_vadd] using hg.symm)
    · exact Or.inr (by simpa only [unitSpinor_vadd_one] using hg.symm)
  · rintro (hs | hs)
    · exact ⟨0,by simpa only [zero_vadd] using hs.symm⟩
    · exact ⟨1,by simpa only [unitSpinor_vadd_one] using hs.symm⟩

/-- The algebraic spinor map is an actual quotient covering, not just a
surjection with two-point fibers. Local disjoint sheets follow from the
free antipodal action on the compact unit spinor sphere. -/
theorem unitSpinorQuadratic_isQuotientCoveringMap :
    IsAddQuotientCoveringMap unitSpinorQuadratic (ZMod 2) where
  toIsQuotientMap := unitSpinorQuadratic_continuous.isClosedMap.isQuotientMap
    unitSpinorQuadratic_continuous unitSpinorQuadratic_surjective
  continuous_const_vadd := continuous_const_vadd
  apply_eq_iff_mem_orbit := unitSpinorQuadratic_fibers.trans unitSpinor_sign_orbit.symm
  disjoint s := by
    let d := dist (unitSpinorAntipode s) s
    have hd : 0 < d := dist_pos.mpr (unitSpinorAntipode_ne s)
    refine ⟨ball s (d/3),ball_mem_nhds s (by positivity),?_⟩
    intro g hg
    rcases zmod_two_cases g with rfl | rfl
    · rfl
    · exfalso
      obtain ⟨w,⟨z,hz,hzw⟩,hw⟩ := hg
      change (1 : ZMod 2) +ᵥ z = w at hzw
      rw [unitSpinor_vadd_one] at hzw
      have htri := dist_triangle (unitSpinorAntipode s) (unitSpinorAntipode z) s
      rw [unitSpinorAntipode_isometry.dist_eq s z,hzw,dist_comm s z] at htri
      change dist z s < d/3 at hz
      change dist w s < d/3 at hw
      change d ≤ dist z s+dist w s at htri
      linarith

theorem unitSpinorQuadratic_isCoveringMap : IsCoveringMap unitSpinorQuadratic :=
  unitSpinorQuadratic_isQuotientCoveringMap.isCoveringMap

theorem unitSpinorQuadratic_two_sheets (p : UnitNullFrame) :
    ∃ s : UnitSpinor, unitSpinorQuadratic s = p ∧
      unitSpinorQuadratic (unitSpinorAntipode s) = p ∧ unitSpinorAntipode s ≠ s ∧
      ∀ t : UnitSpinor, unitSpinorQuadratic t = p → t = s ∨ t = unitSpinorAntipode s := by
  obtain ⟨s,hs⟩ := unitSpinorQuadratic_surjective p
  refine ⟨s,hs,?_,unitSpinorAntipode_ne s,?_⟩
  · exact (unitSpinorQuadratic_fibers.mpr (Or.inr rfl)).trans hs
  · intro t ht
    exact unitSpinorQuadratic_fibers.mp (ht.trans hs.symm)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.unitSpinorQuadratic_isCoveringMap
#print axioms TwoAxisHelicoid.unitSpinorQuadratic_two_sheets
