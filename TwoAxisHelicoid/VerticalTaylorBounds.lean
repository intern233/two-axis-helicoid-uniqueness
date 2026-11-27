module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

public section

namespace TwoAxisHelicoid.VerticalAttachment
open Finset Filter Topology

@[expose] noncomputable def expPartial (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, (-x)^k / (k.factorial : ℝ)

/-- For the arguments of the uploaded program the series decreases from
index 60 onward, even when its first terms increase. -/
theorem expPartial_bounds {x : ℝ} (hx : 0 ≤ x) (hmax : x ≤ 61) :
    expPartial x 62 ≤ Real.exp (-x) ∧ Real.exp (-x) ≤ expPartial x 61 := by
  let f : ℕ → ℝ := fun n => (-x)^n / (n.factorial : ℝ)
  let magnitude : ℕ → ℝ := fun k => x^(k+60) / ((k+60).factorial : ℝ)
  have decreasing : Antitone magnitude := by
    apply antitone_nat_of_succ_le
    intro k
    let m := k+60
    have he : k+1+60 = m+1 := rfl
    have hm : x ≤ (m : ℝ)+1 := by
      dsimp [m]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) k]
    change x^(k+1+60) / ((k+1+60).factorial : ℝ) ≤ x^m / (m.factorial : ℝ)
    rw [he, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one,
      mul_comm ((m : ℝ)+1), mul_div_mul_comm]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 hm)
  have hs : HasSum f (Real.exp (-x)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (-x)
  have sign (k : ℕ) : f (k+60) = (-1:ℝ)^k * magnitude k := by
    have hpow : (-x)^(k+60) = (-1:ℝ)^k * x^(k+60) := calc
      (-x)^(k+60) = ((-1:ℝ)*x)^(k+60) := by rw [neg_one_mul]
      _ = _ := by rw [mul_pow, pow_add (-1:ℝ)]; norm_num
    simp only [f, magnitude, hpow, mul_div_assoc]
  have tail := ((hasSum_nat_add_iff' 60).2 hs).tendsto_sum_nat
  simp only [sign] at tail
  have low := decreasing.alternating_series_le_tendsto tail 1
  have high := decreasing.tendsto_le_alternating_series tail 0
  change (∑ i ∈ range 2, (-1:ℝ)^i * magnitude i) ≤
    Real.exp (-x) - ∑ i ∈ range 60, f i at low
  change Real.exp (-x) - ∑ i ∈ range 60, f i ≤
    ∑ i ∈ range 1, (-1:ℝ)^i * magnitude i at high
  have split (n : ℕ) : expPartial x (60+n) =
      (∑ i ∈ range 60, f i) + ∑ i ∈ range n, (-1:ℝ)^i * magnitude i := by
    change (∑ i ∈ range (60+n), f i) = _
    rw [sum_range_add]
    simp only [Nat.add_comm 60, sign]
  rw [show 62 = 60+2 by rfl, split, show 61 = 60+1 by rfl, split]
  constructor <;> linarith

end TwoAxisHelicoid.VerticalAttachment

#print axioms TwoAxisHelicoid.VerticalAttachment.expPartial_bounds
