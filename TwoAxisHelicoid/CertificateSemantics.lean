import TwoAxisHelicoid.CertificateData
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Semantics of the finite interval tables

This file proves that a gap-free rational partition covers *every real point*,
including irrational points and shared endpoints. It also proves the logical
step from genuine function enclosures to strict signs.

The `encloses` hypotheses below are explicit, unproved analytic obligations.
In particular these theorems do not verify Arb, theta evaluation, or integration,
and do not identify an arbitrary function `f` with the TwoAxisHelicoid period function.
-/

namespace TwoAxisHelicoid.CertificateSemantics

open TwoAxisHelicoid.CertificateData

/-- Membership in the closed real interval with the given rational endpoints. -/
def RealMem (r : Interval) (x : ℝ) : Prop :=
  (r.lower : ℝ) ≤ x ∧ x ≤ (r.upper : ℝ)

/-- A nondegenerate rational partition covers all real points of its interval.
The strict endpoint hypothesis excludes the empty-list degenerate partition. -/
theorem partition_covers {lo hi : ℚ} {rows : List Interval}
    (hp : Partition lo hi rows) (hne : lo < hi) {x : ℝ}
    (hx : (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)) :
    ∃ r ∈ rows, RealMem r x := by
  induction rows generalizing lo with
  | nil =>
      change lo = hi at hp
      exact (hne.ne hp).elim
  | cons r rs ih =>
      obtain ⟨hlo, _, htail⟩ := hp
      subst lo
      by_cases hxr : x ≤ (r.upper : ℝ)
      · exact ⟨r, List.mem_cons_self, hx.1, hxr⟩
      · have hlt : (r.upper : ℝ) < x := lt_of_not_ge hxr
        have htailpos : r.upper < hi := by
          exact_mod_cast lt_of_lt_of_le hlt hx.2
        obtain ⟨s, hs, hmem⟩ := ih htail htailpos ⟨hlt.le, hx.2⟩
        exact ⟨s, List.mem_cons_of_mem r hs, hmem⟩

/-- A partition of the time columns selects a row for every real parameter. -/
theorem checked_sign_row_covers {positive : Bool} {margin lo hi : ℚ}
    {rows : List (CheckedSignRow positive margin)}
    (hp : Partition lo hi (rows.map fun r => r.t)) (hne : lo < hi)
    {x : ℝ} (hx : (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)) :
    ∃ r ∈ rows, RealMem r.t x := by
  obtain ⟨s, hs, hmem⟩ := partition_covers hp hne hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
  exact ⟨r, hr, hmem⟩

/-- A positive checked row implies a strict lower bound, provided its reported
interval actually encloses the real function value. -/
theorem positive_of_row_enclosure {margin : ℚ} (r : CheckedSignRow true margin)
    {y : ℝ} (hy : RealMem r.hReal y) : (margin : ℝ) < y := by
  rcases r.verified with ⟨_, _, _, _, _, _, _, _, _, _, _, h⟩
  have hq : margin < r.hReal.lower := by simpa using h
  have hr : (margin : ℝ) < (r.hReal.lower : ℝ) := by exact_mod_cast hq
  exact lt_of_lt_of_le hr hy.1

/-- Negative version of `positive_of_row_enclosure`. -/
theorem negative_of_row_enclosure {margin : ℚ} (r : CheckedSignRow false margin)
    {y : ℝ} (hy : RealMem r.hReal y) : y < -(margin : ℝ) := by
  rcases r.verified with ⟨_, _, _, _, _, _, _, _, _, _, _, h⟩
  have hq : r.hReal.upper < -margin := by simpa using h
  have hr : (r.hReal.upper : ℝ) < -(margin : ℝ) := by exact_mod_cast hq
  exact lt_of_le_of_lt hy.2 hr

/-- Finite positive data yield a uniform bound only after soundness of every
reported enclosure has been established for the real function `f`. -/
theorem positive_on_partition {margin lo hi : ℚ}
    (rows : List (CheckedSignRow true margin))
    (hp : Partition lo hi (rows.map fun r => r.t)) (hne : lo < hi)
    (f : ℝ → ℝ)
    (encloses : ∀ r ∈ rows, ∀ x : ℝ, RealMem r.t x → RealMem r.hReal (f x))
    {x : ℝ} (hx : (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)) : (margin : ℝ) < f x := by
  obtain ⟨r, hr, hmem⟩ := checked_sign_row_covers hp hne hx
  exact positive_of_row_enclosure r (encloses r hr x hmem)

/-- The corresponding negative finite-table soundness implication. -/
theorem negative_on_partition {margin lo hi : ℚ}
    (rows : List (CheckedSignRow false margin))
    (hp : Partition lo hi (rows.map fun r => r.t)) (hne : lo < hi)
    (f : ℝ → ℝ)
    (encloses : ∀ r ∈ rows, ∀ x : ℝ, RealMem r.t x → RealMem r.hReal (f x))
    {x : ℝ} (hx : (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)) : f x < -(margin : ℝ) := by
  obtain ⟨r, hr, hmem⟩ := checked_sign_row_covers hp hne hx
  exact negative_of_row_enclosure r (encloses r hr x hmem)

/-- The PDF's 558 positive rows give the advertised real-interval bound,
conditional on their as-yet-unproved analytic enclosure property. -/
theorem pdf_positive_of_enclosures (f : ℝ → ℝ)
    (encloses : ∀ r ∈ positiveData, ∀ x : ℝ,
      RealMem r.t x → RealMem r.hReal (f x))
    {x : ℝ} (hx : (1 / 8 : ℝ) ≤ x ∧ x ≤ (17 / 20 : ℝ)) :
    (3 / 10000 : ℝ) < f x := by
  have h := positive_on_partition positiveData positive_partition (by norm_num) f encloses
    (x := x) (by simpa using hx)
  simpa using h

/-- The PDF's 59 negative rows, with the same explicit analytic obligation. -/
theorem pdf_negative_of_enclosures (f : ℝ → ℝ)
    (encloses : ∀ r ∈ negativeData, ∀ x : ℝ,
      RealMem r.t x → RealMem r.hReal (f x))
    {x : ℝ} (hx : (9 / 10 : ℝ) ≤ x ∧ x ≤ (7 / 5 : ℝ)) :
    f x < -(1 / 25 : ℝ) := by
  have h := negative_on_partition negativeData negative_partition (by norm_num) f encloses
    (x := x) (by simpa using hx)
  simpa using h

end TwoAxisHelicoid.CertificateSemantics

#print axioms TwoAxisHelicoid.CertificateSemantics.partition_covers
#print axioms TwoAxisHelicoid.CertificateSemantics.positive_on_partition
#print axioms TwoAxisHelicoid.CertificateSemantics.negative_on_partition
#print axioms TwoAxisHelicoid.CertificateSemantics.pdf_positive_of_enclosures
#print axioms TwoAxisHelicoid.CertificateSemantics.pdf_negative_of_enclosures
