import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

namespace TwoAxisHelicoid
open Set

theorem continuous_nonzero_constant_sign {s : Set ℝ} (hs : IsPreconnected s)
    (hne : s.Nonempty) {d : ℝ → ℝ} (hd : ContinuousOn d s) (hn : ∀ x ∈ s, d x ≠ 0) :
    (∀ x ∈ s, 0 < d x) ∨ (∀ x ∈ s, d x < 0) := by
  obtain ⟨x,hx⟩ := hne
  rcases lt_or_gt_of_ne (hn x hx) with hneg | hpos
  · right
    intro y hy
    by_contra h
    obtain ⟨z,hz,he⟩ := hs.intermediate_value hx hy hd
      (show (0 : ℝ) ∈ Icc (d x) (d y) from ⟨hneg.le,le_of_not_gt h⟩)
    exact hn z hz he
  · left
    intro y hy
    by_contra h
    obtain ⟨z,hz,he⟩ := hs.intermediate_value hy hx hd
      (show (0 : ℝ) ∈ Icc (d y) (d x) from ⟨le_of_not_gt h,hpos.le⟩)
    exact hn z hz he

theorem strictMonoOn_or_strictAntiOn_of_continuous_nonzero_derivative {a b : ℝ}
    (hab : a < b) {f d : ℝ → ℝ} (hf : ∀ x ∈ Ioo a b, HasDerivAt f (d x) x)
    (hd : ContinuousOn d (Ioo a b)) (hn : ∀ x ∈ Ioo a b, d x ≠ 0) :
    StrictMonoOn f (Ioo a b) ∨ StrictAntiOn f (Ioo a b) := by
  have hc : ContinuousOn f (Ioo a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  rcases continuous_nonzero_constant_sign (convex_Ioo a b).isPreconnected
      (nonempty_Ioo.mpr hab) hd hn with hp | hm
  · left
    apply strictMonoOn_of_deriv_pos (convex_Ioo a b) hc
    intro x hx
    rw [isOpen_Ioo.interior_eq] at hx
    rw [(hf x hx).deriv]
    exact hp x hx
  · right
    apply strictAntiOn_of_deriv_neg (convex_Ioo a b) hc
    intro x hx
    rw [isOpen_Ioo.interior_eq] at hx
    rw [(hf x hx).deriv]
    exact hm x hx

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.strictMonoOn_or_strictAntiOn_of_continuous_nonzero_derivative
