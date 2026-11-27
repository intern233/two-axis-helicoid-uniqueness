module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

public section

namespace TwoAxisHelicoid.VerticalAttachment
open Filter Topology Finset

@[expose] noncomputable def atanTerm (x : ℝ) (n : ℕ) : ℝ := x ^ (2*n+1) / ((2*n+1 : ℕ) : ℝ)

@[expose] noncomputable def atanSum40 (x : ℝ) : ℝ := ∑ n ∈ range 40, (-1 : ℝ)^n * atanTerm x n

/-- The actual alternating lower and upper sums in the attached 40-term calculation. -/
theorem atanSum40_bounds {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    atanSum40 x ≤ Real.arctan x ∧ Real.arctan x ≤ atanSum40 x + x^81/81 := by
  have decreasing : Antitone (atanTerm x) := by
    apply antitone_nat_of_succ_le
    intro k
    unfold atanTerm
    apply div_le_div₀ (pow_nonneg hx _)
      (pow_le_pow_of_le_one hx hx1.le (show 2*k+1 ≤ 2*(k+1)+1 by omega))
    · exact_mod_cast (show 0 < 2*k+1 by omega)
    · exact_mod_cast (show 2*k+1 ≤ 2*(k+1)+1 by omega)
  have sums : Tendsto (fun k => ∑ n ∈ range k, (-1 : ℝ)^n * atanTerm x n)
      atTop (𝓝 (Real.arctan x)) := by
    simpa only [atanTerm, mul_div_assoc] using
      (Real.hasSum_arctan (by rwa [Real.norm_eq_abs, abs_of_nonneg hx] : ‖x‖ < 1)).tendsto_sum_nat
  have lower := decreasing.alternating_series_le_tendsto sums 20
  have upper := decreasing.tendsto_le_alternating_series sums 20
  change (∑ n ∈ range (40+1), (-1 : ℝ)^n * atanTerm x n) ≥ Real.arctan x at upper
  have last : (-1 : ℝ)^40 * atanTerm x 40 = x^81/81 := by norm_num [atanTerm]
  rw [sum_range_succ, last] at upper
  exact ⟨lower, upper⟩

/-- Machin's formula with the two one-sided alternating errors kept with their signs. -/
theorem machin_unrounded_bounds :
    16*atanSum40 (1/5) - 4*(atanSum40 (1/239)+(1/239)^81/81) ≤ Real.pi ∧
    Real.pi ≤ 16*(atanSum40 (1/5)+(1/5)^81/81) - 4*atanSum40 (1/239) := by
  have ha := atanSum40_bounds (x := 1/5) (by norm_num) (by norm_num)
  have hb := atanSum40_bounds (x := 1/239) (by norm_num) (by norm_num)
  have machin : 4*Real.arctan (1/5) - Real.arctan (1/239) = Real.pi/4 := by
    simpa only [one_div] using Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

end TwoAxisHelicoid.VerticalAttachment

#print axioms TwoAxisHelicoid.VerticalAttachment.atanSum40_bounds
#print axioms TwoAxisHelicoid.VerticalAttachment.machin_unrounded_bounds
