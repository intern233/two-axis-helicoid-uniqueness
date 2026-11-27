import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# The real-analysis implication in TwoAxisHelicoid, §10

The function `H` below is arbitrary.  This file proves the last real-analysis
implication from explicit hypotheses; it does NOT establish those hypotheses for
the theta-integral in the PDF.  In particular, this is not Theorem 1.1 or a
complete formalization of Theorem 10.1 for the actual period function.
-/

namespace TwoAxisHelicoid
open Set

/-- These are outstanding analytical obligations, not certified numerical facts. -/
structure PeriodHypotheses (H : ℝ → ℝ) (T : ℝ) : Prop where
  endpoint : (7 : ℝ) / 5 < T
  continuous : ContinuousOn H (Icc ((17 : ℝ) / 20) (9 / 10))
  left : ∀ t ∈ Ioc (0 : ℝ) (1 / 8), 0 < H t
  positive : ∀ t ∈ Icc ((1 : ℝ) / 8) (17 / 20), 3 / 10000 < H t
  negative : ∀ t ∈ Icc ((9 : ℝ) / 10) (7 / 5), H t < -(1 / 25)
  right : ∀ t ∈ Ico ((7 : ℝ) / 5) T, H t < -(7 / 5)
  derivative : ∀ t ∈ Icc ((17 : ℝ) / 20) (9 / 10), deriv H t < -1

/-- Every zero in the allowed domain is strictly inside the central interval. -/
theorem zero_in_central_interval {H : ℝ → ℝ} {T t : ℝ}
    (h : PeriodHypotheses H T) (ht : t ∈ Ioo (0 : ℝ) T) (hz : H t = 0) :
    t ∈ Ioo ((17 : ℝ) / 20) (9 / 10) := by
  constructor
  · by_contra hn
    have hle : t ≤ (17 : ℝ) / 20 := le_of_not_gt hn
    by_cases hs : t ≤ (1 : ℝ) / 8
    · have hp := h.left t ⟨ht.1, hs⟩
      linarith
    · have hp := h.positive t ⟨le_of_lt (lt_of_not_ge hs), hle⟩
      linarith
  · by_contra hn
    have hle : (9 : ℝ) / 10 ≤ t := le_of_not_gt hn
    by_cases hs : t ≤ (7 : ℝ) / 5
    · have hp := h.negative t ⟨hle, hs⟩
      linarith
    · have hp := h.right t ⟨le_of_lt (lt_of_not_ge hs), ht.2⟩
      linarith

theorem central_strictAnti {H : ℝ → ℝ} {T : ℝ}
    (h : PeriodHypotheses H T) : StrictAntiOn H (Icc ((17 : ℝ) / 20) (9 / 10)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) h.continuous
  intro t ht
  have hd := h.derivative t (interior_subset ht)
  linarith

/-- The conditional assembly of the five-region argument in Theorem 10.1. -/
theorem existsUnique_period_zero_of_hypotheses {H : ℝ → ℝ} {T : ℝ}
    (h : PeriodHypotheses H T) : ∃! t, t ∈ Ioo (0 : ℝ) T ∧ H t = 0 := by
  have hp : 0 < H ((17 : ℝ) / 20) := by
    have hb := h.positive (17 / 20) (by constructor <;> norm_num)
    linarith
  have hn : H ((9 : ℝ) / 10) < 0 := by
    have hb := h.negative (9 / 10) (by constructor <;> norm_num)
    linarith
  obtain ⟨t, ht, hz⟩ := intermediate_value_Icc'
    (by norm_num : (17 : ℝ) / 20 ≤ 9 / 10) h.continuous ⟨hn.le, hp.le⟩
  have htDomain : t ∈ Ioo (0 : ℝ) T := by
    have he := h.endpoint
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨t, ⟨htDomain, hz⟩, ?_⟩
  intro y hy
  have hyc := zero_in_central_interval h hy.1 hy.2
  exact (central_strictAnti h).injOn ⟨hyc.1.le, hyc.2.le⟩ ht (hy.2.trans hz.symm)

/-- Nonvanishing of the derivative at every zero follows from the same inputs. -/
theorem period_zero_is_simple_of_hypotheses {H : ℝ → ℝ} {T t : ℝ}
    (h : PeriodHypotheses H T) (ht : t ∈ Ioo (0 : ℝ) T) (hz : H t = 0) :
    deriv H t < -1 ∧ deriv H t ≠ 0 := by
  have hc := zero_in_central_interval h ht hz
  have hd := h.derivative t ⟨hc.1.le, hc.2.le⟩
  exact ⟨hd, by linarith⟩

/-- Opposite signs at finer endpoints localize the unique zero. -/
theorem localize_period_zero_of_hypotheses {H : ℝ → ℝ} {T l u : ℝ}
    (h : PeriodHypotheses H T)
    (hl : l ∈ Icc ((17 : ℝ) / 20) (9 / 10))
    (hu : u ∈ Icc ((17 : ℝ) / 20) (9 / 10))
    (hlpos : 0 < H l) (huneg : H u < 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (hz : H t = 0) : t ∈ Ioo l u := by
  have hc := zero_in_central_interval h ht hz
  have htc : t ∈ Icc ((17 : ℝ) / 20) (9 / 10) := ⟨hc.1.le, hc.2.le⟩
  have hm := (central_strictAnti h).antitoneOn
  constructor
  · by_contra hn
    have hp := hm htc hl (le_of_not_gt hn)
    linarith
  · by_contra hn
    have hp := hm hu htc (le_of_not_gt hn)
    linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.existsUnique_period_zero_of_hypotheses
#print axioms TwoAxisHelicoid.period_zero_is_simple_of_hypotheses
#print axioms TwoAxisHelicoid.localize_period_zero_of_hypotheses
