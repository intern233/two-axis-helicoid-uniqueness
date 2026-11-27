import TwoAxisHelicoid.CertificateSemantics
import TwoAxisHelicoid.PositiveSignAll
import TwoAxisHelicoid.NegativeSignAll
import TwoAxisHelicoid.MiddleDerivativeAll
import TwoAxisHelicoid.RightSignAll

namespace TwoAxisHelicoid.CertificateSemantics
open TwoAxisHelicoid.CertificateData

private theorem bounds_of_partition {lo hi : ℚ} {rows : List Interval} (h : Partition lo hi rows) :
    lo≤hi ∧ ∀ r∈rows, lo≤r.lower ∧ r.upper≤hi := by
  induction rows generalizing lo with
  | nil => exact ⟨le_of_eq h,by simp⟩
  | cons r rs ih =>
    obtain ⟨rfl,lt,tail⟩ := h
    obtain ⟨bound,rest⟩ := ih tail
    refine ⟨lt.le.trans bound,?_⟩
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨le_rfl,bound⟩
    · exact ⟨lt.le.trans (rest s hs).1,(rest s hs).2⟩

private theorem within_checked_column {T : Type} {lo hi : ℚ} {rows : List T} {f : T → Interval}
    (hp : Partition lo hi (rows.map f)) {r : T} (hr : r∈rows) {x : ℝ} (hx : RealMem (f r) x) :
    (lo:ℝ) ≤ x ∧ x ≤ (hi:ℝ) := by
  obtain ⟨a,b⟩ := (bounds_of_partition hp).2 _ (List.mem_map.mpr ⟨r,hr,rfl⟩)
  exact ⟨(Rat.cast_le (K := ℝ)).mpr a |>.trans hx.1,hx.2.trans ((Rat.cast_le (K := ℝ)).mpr b)⟩

/-- The true period and derivative satisfy the manuscript's asserted
inequalities on every one of the original parameter rows. -/
theorem actual_period_on_original_rows :
    (∀ r∈positiveData, ∀ x : ℝ, RealMem r.t x → (3/10000 : ℝ)<actualPeriodAlong x) ∧
    (∀ r∈negativeData, ∀ x : ℝ, RealMem r.t x → actualPeriodAlong x< -(1/25 : ℝ)) ∧
    (∀ r∈derivativeData, ∀ x : ℝ, RealMem r.t x → deriv actualPeriodAlong x< -1) ∧
    (∀ r∈endpointData, ∀ a : ℝ, RealMem r.a a → ∀ t : ℝ, (7/5:ℝ)≤t → t≤141/100 →
      thetaHorizontalPeriod t a< -7/5) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro r hr x hx
    have e := within_checked_column positive_partition hr hx
    push_cast at e
    exact actualPeriodAlong_positive_compact e.1 e.2
  · intro r hr x hx
    have e := within_checked_column negative_partition hr hx
    push_cast at e
    simpa only [neg_div] using actualPeriodAlong_negative_compact e.1 e.2
  · intro r hr x hx
    have e := within_checked_column derivative_partition hr hx
    push_cast at e
    exact actualPeriodAlong_deriv_lt_neg_one_middle e.1 e.2
  · intro r hr a ha t lt ut
    have e := within_checked_column endpoint_partition hr ha
    push_cast at e
    exact right_rectangle_horizontal_period_lt lt ut e.1 (by simpa only [div_one] using e.2)

end TwoAxisHelicoid.CertificateSemantics
#print axioms TwoAxisHelicoid.CertificateSemantics.actual_period_on_original_rows
