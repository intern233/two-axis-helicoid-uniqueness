import TwoAxisHelicoid.AnalyticCauchyRiemannContinuation
import TwoAxisHelicoid.MinimalChartComplexData

namespace TwoAxisHelicoid
open Complex Matrix Set Filter
open scoped Topology

theorem real_complex_map_columns {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : ℂ →L[ℝ] E) (w : ℂ) : D w = w.re • D 1+w.im • D I := by
  have h : w.re • (1 : ℂ)+w.im • I = w := by apply Complex.ext <;> simp [Complex.real_smul]
  exact (congrArg D h.symm).trans (by rw [map_add,map_smul,map_smul])

theorem spatial_conformal_pairing (D : ℂ →L[ℝ] (Fin 3 → ℝ))
    (he : D 1 ⬝ᵥ D 1 = D I ⬝ᵥ D I) (ho : D 1 ⬝ᵥ D I = 0) (u v : ℂ) :
    D u ⬝ᵥ D v = (D 1 ⬝ᵥ D 1)*(u.re*v.re+u.im*v.im) := by
  have h₁ := real_complex_map_columns D u
  have h₂ := real_complex_map_columns D v
  conv_lhs => rw [h₁,h₂]
  simp only [add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    ho,(dotProduct_comm (D I) (D 1)).trans ho,← he,mul_zero]
  ring

theorem perpendicular_equal_columns {u v : ℂ} (hu : u ≠ 0)
    (hn : u.re*u.re+u.im*u.im = v.re*v.re+v.im*v.im)
    (ho : u.re*v.re+u.im*v.im = 0) : v = I*u ∨ v = -(I*u) := by
  let r := v/u
  have hr : r.re = 0 := by
    change (v/u).re = 0
    rw [Complex.div_re]
    have hh : v.re*u.re+v.im*u.im = 0 := by linear_combination ho
    rw [← add_div,hh,zero_div]
  have hsq : normSq v = normSq u := hn.symm
  have hu' : normSq u ≠ 0 := by rw [Complex.normSq_eq_norm_sq]; exact pow_ne_zero _ (norm_ne_zero_iff.mpr hu)
  have hs : normSq r = 1 := by simp [r,map_div₀,hsq,hu']
  have hm : r.im = 1 ∨ r.im = -1 := by
    rw [Complex.normSq_apply,hr,zero_mul,zero_add] at hs
    exact (mul_self_eq_one_iff.mp hs)
  have eqv : r*u=v := div_mul_cancel₀ _ hu
  rcases hm with h | h
  · left
    have h' : r = I := Complex.ext (by simpa using hr) (by simpa using h)
    rw [← eqv,h']
  · right
    have h' : r = -I := Complex.ext (by simpa using hr) (by simpa using h)
    rw [← eqv,h',neg_mul]

/-- The sign of the two possible conformal orientations is constant over
a connected parameter set. Nondegeneracy keeps the two possibilities apart. -/
theorem constant_conformal_column_sign {U : Set ℂ} (hU : IsPreconnected U)
    {p q : ℂ → ℂ} (hp : ContinuousOn p U) (hq : ContinuousOn q U)
    (hn : ∀ z ∈ U, q z ≠ 0) (h : ∀ z ∈ U, p z = q z ∨ p z = -(q z)) :
    (∀ z ∈ U, p z = q z) ∨ (∀ z ∈ U, p z = -(q z)) := by
  let f := fun z => p z/q z
  have hf : ContinuousOn f U := hp.div hq hn
  have ht : f '' U ⊆ ({1,-1} : Set ℂ) := by
    rintro _ ⟨z,hz,rfl⟩
    rcases h z hz with he | he
    · simp [f,he,hn z hz]
    · simp [f,he,hn z hz]
  have hfin : (f '' U).Finite := ((finite_singleton (-1:ℂ)).insert 1).subset ht
  have hsub := (hU.image f hf).isDiscrete_iff_subsingleton.mp hfin.isDiscrete
  rcases U.eq_empty_or_nonempty with hem | ⟨b,hb⟩
  · simp [hem]
  have hc (z : ℂ) (hz : z ∈ U) : f z = f b := hsub ⟨z,hz,rfl⟩ ⟨b,hb,rfl⟩
  rcases h b hb with he | he
  · left
    intro z hz
    have ha := hc z hz
    simpa [f,he,hn b hb,div_eq_iff (hn z hz)] using ha
  · right
    intro z hz
    have ha := hc z hz
    simpa [f,he,hn b hb,div_eq_iff (hn z hz)] using ha

theorem real_complex_map_intertwines (D : ℂ →L[ℝ] ℂ) {k : ℂ}
    (hk : k = I ∨ k = -I) (hc : D I = k*D 1) (w : ℂ) : D (I*w) = k*D w := by
  rw [real_complex_map_columns D (I*w),real_complex_map_columns D w,hc]
  rcases hk with rfl | rfl <;> apply Complex.ext <;>
    simp [Complex.mul_re,Complex.mul_im,Complex.real_smul] <;> ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.perpendicular_equal_columns
#print axioms TwoAxisHelicoid.constant_conformal_column_sign
