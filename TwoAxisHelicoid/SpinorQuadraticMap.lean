import TwoAxisHelicoid.NullVectorRegularity

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 1000000

/-- The actual quadratic Weierstrass map, in the convention used by
the PDF and the previously verified coordinate differential. -/
noncomputable def spinorQuadratic (s : ℂ × ℂ) : Fin 3 → ℂ :=
  ![s.2^2-s.1^2,I*(s.2^2+s.1^2),2*s.1*s.2]

noncomputable def spinorWeight (s : ℂ × ℂ) : ℝ := normSq s.1+normSq s.2

theorem spinorQuadratic_null (s : ℂ × ℂ) : ComplexNull (spinorQuadratic s) := by
  dsimp [ComplexNull,spinorQuadratic]
  ring_nf
  simp only [I_sq]
  ring

theorem spinorQuadratic_metric (s : ℂ × ℂ) :
    nullMetric (spinorQuadratic s) = (spinorWeight s)^2 := by
  dsimp [nullMetric,spinorQuadratic,spinorWeight]
  norm_num [pow_two,Complex.mul_re,Complex.mul_im,Complex.normSq_apply]
  ring

theorem spinorWeight_nonneg (s : ℂ × ℂ) : 0 ≤ spinorWeight s :=
  add_nonneg (normSq_nonneg _) (normSq_nonneg _)

theorem spinorWeight_pos {s : ℂ × ℂ} (hs : s ≠ 0) : 0 < spinorWeight s := by
  rcases ne_or_eq s.1 0 with h1 | h1
  · exact add_pos_of_pos_of_nonneg (normSq_pos.mpr h1) (normSq_nonneg _)
  · have h2 : s.2 ≠ 0 := fun h2 => hs (Prod.ext h1 h2)
    exact add_pos_of_nonneg_of_pos (normSq_nonneg _) (normSq_pos.mpr h2)

theorem spinorQuadratic_neg (s : ℂ × ℂ) : spinorQuadratic (-s) = spinorQuadratic s := by
  ext j
  fin_cases j <;> simp [spinorQuadratic]

theorem spinorQuadratic_invariants {s t : ℂ × ℂ} (h : spinorQuadratic s = spinorQuadratic t) :
    s.1^2 = t.1^2 ∧ s.2^2 = t.2^2 ∧ s.1*s.2 = t.1*t.2 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  change s.2^2-s.1^2 = t.2^2-t.1^2 at h0
  change I*(s.2^2+s.1^2) = I*(t.2^2+t.1^2) at h1
  change 2*s.1*s.2 = 2*t.1*t.2 at h2
  have hsum := mul_left_cancel₀ I_ne_zero h1
  refine ⟨?_,?_,?_⟩
  · linear_combination (hsum-h0)/2
  · linear_combination (hsum+h0)/2
  · linear_combination h2/2

/-- The fibers of the quadratic frame map consist exactly of opposite
spinors. This includes the degenerate zero fiber and uses no numerical
or topological assumption. -/
theorem spinorQuadratic_eq_iff {s t : ℂ × ℂ} :
    spinorQuadratic s = spinorQuadratic t ↔ s = t ∨ s = -t := by
  constructor
  · intro he
    obtain ⟨h1,h2,hprod⟩ := spinorQuadratic_invariants he
    by_cases hs : s.1 = 0
    · have ht : t.1 = 0 := by
        have hh : t.1^2 = 0 := by rw [← h1,hs]; norm_num
        exact (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hh
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with hv | hv
      · exact Or.inl (Prod.ext (hs.trans ht.symm) hv)
      · exact Or.inr (Prod.ext (by simp [hs,ht]) hv)
    · rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with hu | hu
      · have hv : s.2 = t.2 := mul_left_cancel₀ hs (by simpa only [← hu] using hprod)
        exact Or.inl (Prod.ext hu hv)
      · have hv : s.2 = -t.2 := by
          apply mul_left_cancel₀ hs
          rw [hprod,hu]
          ring
        exact Or.inr (Prod.ext hu hv)
  · rintro (rfl | rfl)
    · rfl
    · exact spinorQuadratic_neg t

theorem spinorQuadratic_smul (a : ℂ) (s : ℂ × ℂ) :
    spinorQuadratic (a • s) = a^2 • spinorQuadratic s := by
  ext j
  fin_cases j <;> dsimp [spinorQuadratic] <;> ring

theorem spinorWeight_smul (a : ℂ) (s : ℂ × ℂ) :
    spinorWeight (a • s) = normSq a*spinorWeight s := by
  change normSq (a*s.1)+normSq (a*s.2) = _
  rw [map_mul,map_mul]
  unfold spinorWeight
  ring

theorem spinorQuadratic_continuous : Continuous spinorQuadratic := by
  apply continuous_pi
  intro j
  fin_cases j <;> dsimp [spinorQuadratic] <;> fun_prop

theorem spinorWeight_continuous : Continuous spinorWeight := by
  unfold spinorWeight
  fun_prop

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.spinorQuadratic_eq_iff
#print axioms TwoAxisHelicoid.spinorQuadratic_metric
