import TwoAxisHelicoid.HelicoidTubeMetric

namespace TwoAxisHelicoid
open Real
set_option maxHeartbeats 1000000

theorem symmetric_two_coordinate_upper_bound {k : ℝ} (hk : |k| ≤ 1/2) (a b : ℝ) :
    (a+k*b)^2+(b+k*a)^2 ≤ (9/4)*(a^2+b^2) := by
  have hab := abs_le.mp hk
  have hp : 0 ≤ (9/4 : ℝ)-(1+k)^2 := by nlinarith
  have hm : 0 ≤ (9/4 : ℝ)-(1-k)^2 := by nlinarith
  have h1 := mul_nonneg hp (sq_nonneg (a+b))
  have h2 := mul_nonneg hm (sq_nonneg (a-b))
  nlinarith

theorem helicoid_graph_tangent_part_bound {r s : ℝ} (hs : |s| ≤ 1/2) (a b : ℝ) :
    (a+s*b/helicoidQ r)^2+(helicoidQ r)^2*(b+s*a/(helicoidQ r)^3)^2 ≤
      (9/4)*(a^2+(helicoidQ r)^2*b^2) := by
  have hq := helicoidQ_pos r
  have hq2 : (1 : ℝ) ≤ (helicoidQ r)^2 := one_le_pow₀ (helicoidQ_ge_one r)
  have hk : |s/(helicoidQ r)^2| ≤ 1/2 := by
    rw [abs_div,abs_of_pos (pow_pos hq 2)]
    apply (div_le_iff₀ (pow_pos hq 2)).mpr
    linarith
  have h := symmetric_two_coordinate_upper_bound hk a (helicoidQ r*b)
  have h1 : a+(s/(helicoidQ r)^2)*(helicoidQ r*b) = a+s*b/helicoidQ r := by field_simp
  have h2 : helicoidQ r*b+(s/(helicoidQ r)^2)*a =
      helicoidQ r*(b+s*a/(helicoidQ r)^3) := by field_simp
  rw [h1,h2,mul_pow,mul_pow] at h
  exact h

/-- A small angle between tangent planes bounds the derivative of graph
height in the helicoid metric. The constant is uniform over the half tube. -/
theorem helicoid_graph_height_linear_bound {r s κ : ℝ} (hs : |s| ≤ 1/2)
    (hκ : |κ| ≤ 1/2) (a b c : ℝ)
    (hangle : c^2 ≤ κ^2*((a+s*b/helicoidQ r)^2+
      (helicoidQ r)^2*(b+s*a/(helicoidQ r)^3)^2+c^2)) :
    c^2 ≤ 4*κ^2*(a^2+(helicoidQ r)^2*b^2) := by
  have ht := helicoid_graph_tangent_part_bound (r := r) hs a b
  have hκ2 : κ^2 ≤ (1/4 : ℝ) := by
    have h := abs_le.mp hκ
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left ht (sq_nonneg κ)
  have h2 := mul_le_mul_of_nonneg_right hκ2 (sq_nonneg c)
  have h3 : 0 ≤ κ^2*(a^2+(helicoidQ r)^2*b^2) := by positivity
  nlinarith

theorem real_pair_linear_form (L : (ℝ × ℝ) →L[ℝ] ℝ) (a b : ℝ) :
    L (a,b) = a*L (1,0)+b*L (0,1) := by
  have he : (a,b) = a • ((1 : ℝ),0)+b • ((0 : ℝ),1) := by ext <;> simp
  rw [he,map_add,map_smul,map_smul]
  rfl

/-- The resulting operator bound is exactly the gradient bound for the
metric dr² + (1+r²)dθ² on the helicoid. -/
theorem helicoid_height_gradient_sq_bound (L : (ℝ × ℝ) →L[ℝ] ℝ) (r κ : ℝ)
    (hL : ∀ a b : ℝ, (L (a,b))^2 ≤ 4*κ^2*(a^2+(helicoidQ r)^2*b^2)) :
    (L (1,0))^2+(L (0,1))^2/(helicoidQ r)^2 ≤ 4*κ^2 := by
  let G := (L (1,0))^2+(L (0,1))^2/(helicoidQ r)^2
  have hG0 : 0 ≤ G := by dsimp [G]; positivity
  have he : L (L (1,0),L (0,1)/(helicoidQ r)^2) = G := by
    rw [real_pair_linear_form]
    dsimp [G]
    ring
  have hmetric : (L (1,0))^2+(helicoidQ r)^2*(L (0,1)/(helicoidQ r)^2)^2 = G := by
    dsimp [G]
    field_simp
  have h := hL (L (1,0)) (L (0,1)/(helicoidQ r)^2)
  rw [he,hmetric] at h
  change G ≤ 4*κ^2
  by_contra hn
  have hgt : 4*κ^2 < G := lt_of_not_ge hn
  have hG : 0 < G := lt_of_le_of_lt (by positivity) hgt
  have hpos := mul_pos hG (sub_pos.mpr hgt)
  nlinarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoid_height_gradient_sq_bound
