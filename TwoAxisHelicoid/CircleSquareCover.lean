import TwoAxisHelicoid.SpinFrameRotation
import Mathlib.Analysis.Complex.Circle

namespace TwoAxisHelicoid
open Complex Set Topology

noncomputable def circleAntipode : Circle ≃ₜ Circle where
  toFun u := -u
  invFun u := -u
  left_inv := neg_neg
  right_inv := neg_neg
  continuous_toFun := continuous_neg
  continuous_invFun := continuous_neg

theorem circle_square_fibers (u v : Circle) : u^2 = v^2 ↔ u = v ∨ u = -v := by
  constructor
  · intro he
    have hs : (u : ℂ)^2 = (v : ℂ)^2 := congrArg (fun w : Circle => (w : ℂ)) he
    have hz : ((u : ℂ)-(v : ℂ))*((u : ℂ)+(v : ℂ)) = 0 := by
      linear_combination hs
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl (Circle.ext (sub_eq_zero.mp h))
    · exact Or.inr (Circle.ext (add_eq_zero_iff_eq_neg.mp h))
  · rintro (rfl | rfl)
    · rfl
    · apply Circle.ext
      simp

theorem circle_square_surjective : Function.Surjective (fun u : Circle => u^2) := by
  intro v
  obtain ⟨u,hu⟩ := complex_has_square_root (v : ℂ)
  have hn : ‖u‖ = 1 := by
    have hs : ‖u‖^2 = 1 := by
      rw [← norm_pow,hu,Circle.norm_coe]
    nlinarith [norm_nonneg u]
  let w : Circle := ⟨u,mem_sphere_zero_iff_norm.mpr hn⟩
  exact ⟨w,Circle.ext hu⟩

/-- The Spin(2) square map is the actual twofold covering of the unit
circle, with its usual topology and antipodal deck transformation. -/
theorem circle_square_isCoveringMap : IsCoveringMap (fun u : Circle => u^2) := by
  have hc : Continuous (fun u : Circle => u^2) := continuous_id.pow 2
  exact free_involution_quotient_isCoveringMap circleAntipode neg_neg Circle.neg_ne_self
    (hc.isClosedMap.isQuotientMap hc circle_square_surjective) circle_square_fibers

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.circle_square_isCoveringMap
