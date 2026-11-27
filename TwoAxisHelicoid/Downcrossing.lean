import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-!
# The downcrossing criterion of Appendix A.3

This is a real-analysis theorem, not an assertion that the particular TwoAxisHelicoid
period function meets its hypotheses. In fact continuity of the derivative
is unnecessary: continuity of the function and a negative derivative at
each zero suffice.
-/

open Set Filter SignType
open scoped Topology

namespace TwoAxisHelicoid

private theorem right_negative_point {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (ha : f a = 0) (hda : deriv f a < 0) :
    ∃ r ∈ Ioo a b, f r < 0 := by
  have he := eventually_nhdsWithin_sign_eq_of_deriv_neg hda ha
  obtain ⟨l, u, ⟨hla, hau⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp he
  obtain ⟨r, har, hr⟩ := exists_between (lt_min hau hab)
  refine ⟨r, ⟨har, (lt_min_iff.mp hr).2⟩, ?_⟩
  apply sign_eq_neg_one_iff.mp
  rw [hlu ⟨hla.trans har, (lt_min_iff.mp hr).1⟩]
  exact sign_neg (sub_neg.mpr har)

private theorem left_positive_point {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hb : f b = 0) (hdb : deriv f b < 0) :
    ∃ s ∈ Ioo a b, 0 < f s := by
  have he := eventually_nhdsWithin_sign_eq_of_deriv_neg hdb hb
  obtain ⟨l, u, ⟨hlb, hbu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp he
  obtain ⟨s, hs, hsb⟩ := exists_between (max_lt hlb hab)
  refine ⟨s, ⟨(max_lt_iff.mp hs).2, hsb⟩, ?_⟩
  apply sign_eq_one_iff.mp
  rw [hlu ⟨(max_lt_iff.mp hs).1, hsb.trans hbu⟩]
  exact sign_pos (sub_pos.mpr hsb)

/-- Two ordered endpoints cannot both be roots when every root in their
closed interval has strictly negative derivative. -/
theorem no_two_downcrossing_roots {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Icc a b, f x = 0 → deriv f x < 0)
    (ha : f a = 0) (hb : f b = 0) : False := by
  obtain ⟨r, hr, hfr⟩ := right_negative_point hab ha (hd a ⟨le_rfl, hab.le⟩ ha)
  have hsub : Icc r b ⊆ Icc a b := Icc_subset_Icc hr.1.le le_rfl
  have hcr : ContinuousOn f (Icc r b) := hc.mono hsub
  let Z := Icc r b ∩ f ⁻¹' {0}
  have hZclosed : IsClosed Z := hcr.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZcompact : IsCompact Z := isCompact_Icc.of_isClosed_subset hZclosed inter_subset_left
  have hZnonempty : Z.Nonempty := ⟨b, ⟨⟨hr.2.le, le_rfl⟩, hb⟩⟩
  obtain ⟨c, hcmin⟩ := hZcompact.exists_isLeast hZnonempty
  have hcZ : c ∈ Z := hcmin.1
  have hfc : f c = 0 := hcZ.2
  have hrc : r < c := lt_of_le_of_ne hcZ.1.1 (by
    intro h
    have : f r = 0 := h ▸ hfc
    linarith)
  obtain ⟨s, hs, hfs⟩ := left_positive_point hrc hfc (hd c (hsub hcZ.1) hfc)
  have hrs : r ≤ s := hs.1.le
  have hcs : ContinuousOn f (Icc r s) := hcr.mono (Icc_subset_Icc le_rfl (hs.2.le.trans hcZ.1.2))
  obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc hrs hcs ⟨hfr.le, hfs.le⟩
  have hzZ : z ∈ Z := ⟨⟨hz.1, hz.2.trans (hs.2.le.trans hcZ.1.2)⟩, hfz⟩
  have hcz : c ≤ z := hcmin.2 hzZ
  linarith [hz.2, hs.2]

/-- Appendix A.3, in a form that applies to any real interval.
Only continuity of `f`, not of `deriv f`, is required. -/
theorem downcrossing_roots_unique {f : ℝ → ℝ} {D : Set ℝ}
    (hD : OrdConnected D) (hc : ContinuousOn f D)
    (hd : ∀ x ∈ D, f x = 0 → deriv f x < 0)
    {x y : ℝ} (hx : x ∈ D) (hy : y ∈ D)
    (hfx : f x = 0) (hfy : f y = 0) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · have hsub := hD.out hx hy
    exact False.elim (no_two_downcrossing_roots hxy (hc.mono hsub)
      (fun z hz => hd z (hsub hz)) hfx hfy)
  · exact hxy
  · have hsub := hD.out hy hx
    exact False.elim (no_two_downcrossing_roots hyx (hc.mono hsub)
      (fun z hz => hd z (hsub hz)) hfy hfx)

/-- The exact open-interval form used in Appendix A.3. -/
theorem downcrossing_unique_Ioo {f : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Ioo a b))
    (hd : ∀ x ∈ Ioo a b, f x = 0 → deriv f x < 0) :
    Set.Subsingleton {x ∈ Ioo a b | f x = 0} := by
  intro x hx y hy
  exact downcrossing_roots_unique ordConnected_Ioo hc hd hx.1 hy.1 hx.2 hy.2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.no_two_downcrossing_roots
#print axioms TwoAxisHelicoid.downcrossing_roots_unique
#print axioms TwoAxisHelicoid.downcrossing_unique_Ioo
