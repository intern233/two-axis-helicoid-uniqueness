import TwoAxisHelicoid.VerticalAttachmentNome
import TwoAxisHelicoid.VerticalLambertRun
import TwoAxisHelicoid.EndpointLambertSlopeIdentity

namespace TwoAxisHelicoid.VerticalAttachment

/-- Propagate the real Lambert sums through the original finite arithmetic,
including every outward rounding of products, sums and quotients. -/
theorem uploaded_slope_from_lambert {t : ℝ}
    (hl : ((1/right : ℚ) : ℝ) ≤ t) (hu : t ≤ ((1/left : ℚ) : ℝ)) :
    let q := Real.exp (-(Real.pi*t))
    let s₁ := ∑' n : ℕ, uploadedLambertTerm q 1 n
    let s₃ := ∑' n : ℕ, uploadedLambertTerm q 3 n
    ContainsReal slopeBox
      (endpointSlopeExpression t (Real.pi^2/12*(1-24*s₁)) (Real.pi^4/12*(1+240*s₃))) := by
  intro q s₁ s₃
  let tbox : Box := (1/right,1/left)
  have ht : ContainsReal tbox t := ⟨hl, hu⟩
  have one : ContainsReal oneBox 1 := by simp [ContainsReal, oneBox]
  have hπ := uploaded_machin_pi_contains
  have hπ2 := boxMul_contains hπ hπ
  have hπ4 := boxMul_contains hπ2 hπ2
  have hq := original_three_nome_enclosures.2.2 t hl hu
  obtain ⟨hs₁, hs₃⟩ := original_lambert_real_sums hq
  change ContainsReal endS1 s₁ at hs₁
  change ContainsReal endS3 s₃ at hs₃
  have hη := boxScale_contains (boxMul_contains hπ2
    (boxAdd_contains one (boxScale_contains hs₁ (-24)))) (1/12)
  have hg := boxScale_contains (boxMul_contains hπ4
    (boxAdd_contains one (boxScale_contains hs₃ 240))) (1/12)
  have hf := boxDiv_contains hπ ht (by decide +kernel)
  have he := boxAdd_contains hf (boxNeg_contains hη)
  have hc := boxAdd_contains (boxScale_contains (boxMul_contains he he) 6)
    (boxScale_contains hg (-1/2))
  have hn := boxAdd_contains (boxMul_contains hf hf) (boxScale_contains (boxMul_contains he hf) 2)
  have h := boxDiv_contains (boxAdd_contains hn (boxScale_contains hc (-2/3))) hπ
    (by rw [original_pi_box]; decide +kernel)
  unfold slopeBox
  dsimp only
  rw [original_endpoint_nome, original_lambert_one, original_lambert_three]
  convert h using 1
  unfold endpointSlopeExpression
  push_cast
  ring

/-- The actual endpoint derivative enclosed directly by the uploaded arithmetic. -/
theorem uploaded_slope_by_original_algorithm :
    ContainsReal slopeBox
      (derivWithin rightExtendedPeriod (Set.Iio ellipticVerticalUpper) ellipticVerticalUpper) := by
  have l : 1/right = rightCoefficientTLower := by decide +kernel
  have u : 1/left = rightCoefficientTUpper := by decide +kernel
  have ht := ellipticVerticalUpper_in_coefficient_interval
  rw [← l, ← u] at ht
  have h := uploaded_slope_from_lambert ht.1 ht.2
  rw [← endpoint_lambert_derivative]
  simpa [uploadedLambertTerm, neg_mul] using h

end TwoAxisHelicoid.VerticalAttachment

#print axioms TwoAxisHelicoid.VerticalAttachment.uploaded_slope_from_lambert
#print axioms TwoAxisHelicoid.VerticalAttachment.uploaded_slope_by_original_algorithm
