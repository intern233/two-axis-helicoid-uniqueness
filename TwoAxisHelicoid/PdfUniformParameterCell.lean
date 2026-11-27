import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

namespace TwoAxisHelicoid.PdfVertical
open Set

/-- Every point of a closed real interval belongs to a cell of its
uniform subdivision, including its right endpoint. -/
theorem closed_uniform_cell {l u x : ℝ} {N : ℕ} (hN : 0<N) (order : l<u) (xin : x∈Icc l u) :
    ∃ i : Fin N, l+(u-l)*(i:ℝ)/N≤x ∧ x≤l+(u-l)*((i:ℝ)+1)/N := by
  have hp : 0<(N:ℝ) := by exact_mod_cast hN
  have step : 0<u-l := sub_pos.mpr order
  let y := (N:ℝ)*(x-l)/(u-l)
  have yn : 0≤y := div_nonneg (mul_nonneg hp.le (sub_nonneg.mpr xin.1)) step.le
  have yu : y≤N := (div_le_iff₀ step).mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right xin.2 l) hp.le)
  obtain ⟨i,li,ui⟩ : ∃ i : Fin N, (i:ℝ)≤y ∧ y≤(i:ℝ)+1 := by
    by_cases eq : y=N
    · have pred : (↑(N-1):ℝ)=(N:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
      exact ⟨⟨N-1,by omega⟩,by change (↑(N-1):ℝ)≤y ∧ y≤(↑(N-1):ℝ)+1;rw [pred,eq];constructor <;> linarith⟩
    · let k := ⌊y⌋₊
      have kg : k<N := (Nat.floor_lt yn).mpr (lt_of_le_of_ne yu eq)
      exact ⟨⟨k,kg⟩,Nat.floor_le yn,(Nat.lt_floor_add_one y).le⟩
  have left := (le_div_iff₀ step).mp li
  have right := (div_le_iff₀ step).mp ui
  refine ⟨i,?_,?_⟩
  · apply (le_sub_iff_add_le').mp
    apply (div_le_iff₀ hp).mpr
    nlinarith only [left]
  · rw [← sub_le_iff_le_add']
    apply (le_div_iff₀ hp).mpr
    nlinarith only [right]

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.closed_uniform_cell
