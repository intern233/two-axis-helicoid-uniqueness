import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Set Topology

abbrev SpinSquare := unitInterval × unitInterval

noncomputable def spinSquareRadius (z : SpinSquare) : ℝ :=
  max |(z.1 : ℝ)-1/2| |(z.2 : ℝ)-1/2|

def SpinSquarePerimeter (z : SpinSquare) : Prop := z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1

theorem spinSquareRadius_nonneg (z : SpinSquare) : 0 ≤ spinSquareRadius z :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem spinSquareRadius_le_half (z : SpinSquare) : spinSquareRadius z ≤ 1/2 := by
  apply max_le <;> apply abs_le.mpr
  · constructor <;> linarith [z.1.2.1,z.1.2.2]
  · constructor <;> linarith [z.2.2.1,z.2.2.2]

theorem spinSquareRadius_zero_iff (z : SpinSquare) :
    spinSquareRadius z = 0 ↔ (z.1 : ℝ) = 1/2 ∧ (z.2 : ℝ) = 1/2 := by
  constructor
  · intro h
    have H := max_le_iff.mp (le_of_eq h)
    exact ⟨sub_eq_zero.mp (abs_nonpos_iff.mp H.1),sub_eq_zero.mp (abs_nonpos_iff.mp H.2)⟩
  · rintro ⟨h,k⟩
    simp [spinSquareRadius,h,k]

theorem spinSquareRadius_eq_half_iff (z : SpinSquare) : spinSquareRadius z = 1/2 ↔ SpinSquarePerimeter z := by
  have side (w : unitInterval) : |(w : ℝ)-1/2| = 1/2 ↔ w = 0 ∨ w = 1 := by
    rw [abs_eq (by norm_num : 0 ≤ (1/2 : ℝ))]
    constructor
    · rintro (h | h)
      · right; exact Subtype.ext (by change (w : ℝ) = 1; linarith)
      · left; exact Subtype.ext (by change (w : ℝ) = 0; linarith)
    · rintro (rfl | rfl) <;> norm_num
  have h0 := (le_max_left |(z.1 : ℝ)-1/2| |(z.2 : ℝ)-1/2|).trans (spinSquareRadius_le_half z)
  have h1 := (le_max_right |(z.1 : ℝ)-1/2| |(z.2 : ℝ)-1/2|).trans (spinSquareRadius_le_half z)
  change max _ _ = (1/2 : ℝ) ↔ _
  rw [max_eq_iff]
  change ((_ ∧ _) ∨ (_ ∧ _)) ↔ (z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1)
  constructor
  · rintro (⟨h,_⟩|⟨h,_⟩)
    · rcases (side z.1).mp h with h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ((side z.2).mp h))
  · rintro (h|h|h)
    · have hh := (side z.1).mpr (Or.inl h)
      exact Or.inl ⟨hh,hh.symm ▸ h1⟩
    · have hh := (side z.1).mpr (Or.inr h)
      exact Or.inl ⟨hh,hh.symm ▸ h1⟩
    · have hh := (side z.2).mpr h
      exact Or.inr ⟨hh,hh.symm ▸ h0⟩

theorem spinSquareRadius_continuous : Continuous spinSquareRadius := by
  unfold spinSquareRadius
  fun_prop

abbrev SpinPuncturedSquare := {z : SpinSquare // 0 < spinSquareRadius z}

noncomputable def squareRadialGain (t : unitInterval) (z : SpinPuncturedSquare) : ℝ :=
  ((1-(t:ℝ))*spinSquareRadius z.1+(t:ℝ)/2)/spinSquareRadius z.1

theorem squareRadialGain_mul (t : unitInterval) (z : SpinPuncturedSquare) :
    squareRadialGain t z * spinSquareRadius z.1 = (1-(t:ℝ))*spinSquareRadius z.1+(t:ℝ)/2 :=
  div_mul_cancel₀ _ z.2.ne'

theorem squareRadialGain_pos (t : unitInterval) (z : SpinPuncturedSquare) : 0 < squareRadialGain t z := by
  apply div_pos _ z.2
  have h := spinSquareRadius_le_half z.1
  nlinarith [t.2.1,z.2,mul_nonneg t.2.1 (sub_nonneg.mpr h)]

theorem squareRadialGain_mul_le (t : unitInterval) (z : SpinPuncturedSquare) :
    squareRadialGain t z * spinSquareRadius z.1 ≤ 1/2 := by
  rw [squareRadialGain_mul]
  nlinarith [mul_nonneg (sub_nonneg.mpr t.2.2) (sub_nonneg.mpr (spinSquareRadius_le_half z.1))]

theorem squareRadialGain_continuous : Continuous (fun w : unitInterval × SpinPuncturedSquare => squareRadialGain w.1 w.2) := by
  have hR : Continuous (fun w : unitInterval × SpinPuncturedSquare => spinSquareRadius w.2.1) :=
    spinSquareRadius_continuous.comp (continuous_subtype_val.comp continuous_snd)
  have ht := continuous_subtype_val.comp (continuous_fst (X := unitInterval) (Y := SpinPuncturedSquare))
  exact (((continuous_const.sub ht).mul hR).add (ht.div_const 2)).div hR (fun w => w.2.2.ne')

noncomputable def squareRadialCoordinate (t : unitInterval) (z : SpinPuncturedSquare) (x : unitInterval)
    (hx : |(x:ℝ)-1/2| ≤ spinSquareRadius z.1) : unitInterval :=
  ⟨1/2+squareRadialGain t z*((x:ℝ)-1/2),by
    have he := (mul_le_mul_of_nonneg_left hx (squareRadialGain_pos t z).le).trans (squareRadialGain_mul_le t z)
    rw [← abs_of_nonneg (squareRadialGain_pos t z).le,← abs_mul] at he
    obtain ⟨h0,h1⟩ := abs_le.mp he
    constructor <;> linarith⟩

noncomputable def squareRadialPoint (t : unitInterval) (z : SpinPuncturedSquare) : SpinSquare :=
  (squareRadialCoordinate t z z.1.1 (le_max_left _ _), squareRadialCoordinate t z z.1.2 (le_max_right _ _))

theorem squareRadialPoint_radius (t : unitInterval) (z : SpinPuncturedSquare) :
    spinSquareRadius (squareRadialPoint t z) = squareRadialGain t z*spinSquareRadius z.1 := by
  simp only [spinSquareRadius,squareRadialPoint,squareRadialCoordinate,add_sub_cancel_left,abs_mul,
    abs_of_pos (squareRadialGain_pos t z),mul_max_of_nonneg _ _ (squareRadialGain_pos t z).le]

noncomputable def squareRadialFlow (t : unitInterval) (z : SpinPuncturedSquare) : SpinPuncturedSquare :=
  ⟨squareRadialPoint t z,by rw [squareRadialPoint_radius]; exact mul_pos (squareRadialGain_pos t z) z.2⟩

theorem squareRadialFlow_continuous : Continuous (fun w : unitInterval × SpinPuncturedSquare => squareRadialFlow w.1 w.2) := by
  have hR := squareRadialGain_continuous
  apply Continuous.subtype_mk
  apply Continuous.prodMk <;> apply Continuous.subtype_mk
  · exact continuous_const.add (hR.mul ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd).fst).sub continuous_const))
  · exact continuous_const.add (hR.mul ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd).snd).sub continuous_const))

theorem squareRadialFlow_zero (z : SpinPuncturedSquare) : squareRadialFlow 0 z = z := by
  have hk : squareRadialGain 0 z = 1 := by simp [squareRadialGain,z.2.ne']
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext <;> change 1/2+squareRadialGain 0 z*(_-1/2) = _ <;> rw [hk,one_mul] <;> ring

theorem squareRadialFlow_perimeter (z : SpinPuncturedSquare) : SpinSquarePerimeter (squareRadialFlow 1 z).1 := by
  apply (spinSquareRadius_eq_half_iff _).mp
  rw [squareRadialFlow,squareRadialPoint_radius,squareRadialGain_mul]
  norm_num

theorem squareRadialFlow_fixed (t : unitInterval) (z : SpinPuncturedSquare) (hz : SpinSquarePerimeter z.1) :
    squareRadialFlow t z = z := by
  have hr := (spinSquareRadius_eq_half_iff z.1).mpr hz
  have hk : squareRadialGain t z = 1 := by unfold squareRadialGain; rw [hr]; ring
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext <;> change 1/2+squareRadialGain t z*(_-1/2) = _ <;> rw [hk,one_mul] <;> ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.squareRadialFlow_continuous
#print axioms TwoAxisHelicoid.squareRadialFlow_perimeter
