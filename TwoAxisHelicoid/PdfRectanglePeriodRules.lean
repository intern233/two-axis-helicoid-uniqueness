import TwoAxisHelicoid.PdfOriginalExactSignMargins

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics

/-- The entire real column on each original rectangle and the exact extremal
entry shared by the rectangles on the same side. -/
def ReportedRectanglePeriods (F : ℝ → ℝ → ℝ) : Prop :=
  (∀ r ∈ positiveData, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
    RealMem r.hReal (F t a) ∧ (originalPositiveMargin : ℝ) ≤ F t a) ∧
  (∀ r ∈ negativeData, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
    RealMem r.hReal (F t a) ∧ F t a ≤ -(originalNegativeMargin : ℝ))

/-- Positivity of the height follows from the initial endpoint of the full
partition, even at the boundary shared by two closed rows. -/
theorem partition_start_le_selected_lower {lo hi : ℚ} {rows : List Interval}
    (partition : Partition lo hi rows) {r : Interval} (member : r ∈ rows) :
    lo ≤ r.lower := by
  induction rows generalizing lo with
  | nil => simp at member
  | cons q rest ih =>
    obtain ⟨start, step, tail⟩ := partition
    rcases List.mem_cons.mp member with same | later
    · simpa only [same] using start.le
    · exact start.le.trans (step.le.trans (ih tail later))

private theorem rectangle_in_domain {b : Bool} {m lo hi : ℚ}
    {rows : List (CheckedSignRow b m)} (partition : Partition lo hi (rows.map fun r => r.t))
    (lo_pos : 0 < lo) {r} (member : r ∈ rows) {t a : ℝ}
    (ht : RealMem r.t t) (ha : RealMem r.a a) : 0 < t ∧ a ∈ Ioo (0 : ℝ) 2 := by
  have start := partition_start_le_selected_lower partition (List.mem_map_of_mem member)
  obtain ⟨_, _, al, _, au, _⟩ := r.verified
  have a_lt_one : a < 1 := ha.2.trans_lt (by exact_mod_cast au)
  exact ⟨(Rat.cast_pos.mpr (lo_pos.trans_le start)).trans_le ht.1,
    (Rat.cast_pos.mpr al).trans_le ha.1, a_lt_one.trans (by norm_num)⟩

theorem reported_rectangle_periods_of_columns (F G : ℝ → ℝ → ℝ)
    (agree : ∀ {t a : ℝ}, 0 < t → a ∈ Ioo (0 : ℝ) 2 → G t a = F t a)
    (pos : ∀ r ∈ positiveData, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
      RealMem r.hReal (F t a) ∧ 3/10000 < F t a)
    (neg : ∀ r ∈ negativeData, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
      RealMem r.hReal (F t a)) : ReportedRectanglePeriods G := by
  constructor
  · intro r hr t a ht ha
    obtain ⟨tp, ad⟩ := rectangle_in_domain positive_partition (by norm_num) hr ht ha
    rw [agree tp ad]
    have box := (pos r hr t a ht ha).1
    exact ⟨box, ((Rat.cast_le (K := ℝ)).mpr (original_sign_summary_extrema.1 r hr)).trans box.1⟩
  · intro r hr t a ht ha
    obtain ⟨tp, ad⟩ := rectangle_in_domain negative_partition (by norm_num) hr ht ha
    rw [agree tp ad]
    have box := neg r hr t a ht ha
    exact ⟨box, box.2.trans (by exact_mod_cast (original_sign_summary_extrema.2.2.1 r hr))⟩

end TwoAxisHelicoid.PdfVertical

#print axioms TwoAxisHelicoid.PdfVertical.reported_rectangle_periods_of_columns
