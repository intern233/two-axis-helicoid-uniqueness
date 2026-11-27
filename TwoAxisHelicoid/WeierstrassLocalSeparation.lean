import TwoAxisHelicoid.NullEuclideanMetric
import Mathlib.Analysis.Calculus.MeanValue

namespace TwoAxisHelicoid
open Set Complex Topology

/-- A checkable local injectivity bound for a Weierstrass coordinate
box. The only numerical data are uniform errors for the three complex
coefficients and the conformal metric at the reference coefficient. -/
theorem weierstrass_box_injective {X : ℂ → Fin 3 → ℝ} {p : ℂ → Fin 3 → ℂ} {U : Set ℂ}
    (convex : Convex ℝ U) (der : ∀ z∈U, HasFDerivAt X (nullRealDerivative (p z)) z)
    {p₀ : Fin 3 → ℂ} (null : ComplexNull p₀) {ε : ℝ} (positive : 0≤ε)
    (error : ∀ z∈U, ∀ j, ‖p z j-p₀ j‖≤ε) (margin : 3*ε^2<nullMetric p₀) : InjOn X U := by
  let proj := fun j : Fin 3 => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j
  let D := fun j a => (proj j).comp (nullRealDerivative a)
  have bound (j : Fin 3) (z : ℂ) (hz : z∈U) : ‖D j (p z)-D j p₀‖≤ε := by
    apply ContinuousLinearMap.opNorm_le_bound _ positive
    intro v
    change ‖(v*p z j).re-(v*p₀ j).re‖≤ε*‖v‖
    rw [← Complex.sub_re,← mul_sub,Real.norm_eq_abs]
    exact (abs_re_le_norm _).trans (by rw [norm_mul,mul_comm ε]; exact mul_le_mul_of_nonneg_left (error z hz j) (norm_nonneg _))
  intro x hx y hy eq
  by_contra ne
  change x≠y at ne
  let v := y-x
  have vp : 0<‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr ne.symm))
  have each (j : Fin 3) : ((nullRealDerivative p₀ v) j)^2≤(ε*‖v‖)^2 := by
    have hd (z : ℂ) (hz : z∈U) : HasFDerivWithinAt (fun w => X w j) (D j (p z)) U z :=
      ((proj j).hasFDerivAt.comp z (der z hz)).hasFDerivWithinAt
    have est := convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' hd (bound j) hx hy
    change ‖X y j-X x j-(nullRealDerivative p₀ v) j‖≤ε*‖v‖ at est
    rw [eq,sub_self,zero_sub,norm_neg,Real.norm_eq_abs] at est
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (mul_nonneg positive (norm_nonneg _))).mpr est
  have total := nullRealDerivative_euclidean_norm_sq null v
  rw [EuclideanSpace.real_norm_sq_eq] at total
  change (∑ j, (nullRealDerivative p₀ v j)^2)=nullMetric p₀*‖v‖^2 at total
  have upper := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3))) (fun j _ => each j)
  rw [total] at upper
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_pow] at upper
  exact (mul_lt_mul_of_pos_right margin vp).not_ge (by linarith)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.weierstrass_box_injective
