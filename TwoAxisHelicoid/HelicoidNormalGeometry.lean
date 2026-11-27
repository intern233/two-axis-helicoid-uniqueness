import TwoAxisHelicoid.HelicoidTubeInjective
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Tactic.FinCases

namespace TwoAxisHelicoid
open Real

noncomputable def standardHelicoid (r θ : ℝ) : Fin 3 → ℝ := ![r*cos θ,r*sin θ,θ]
noncomputable def standardHelicoidR (θ : ℝ) : Fin 3 → ℝ := ![cos θ,sin θ,0]
noncomputable def standardHelicoidTheta (r θ : ℝ) : Fin 3 → ℝ := ![-r*sin θ,r*cos θ,1]
noncomputable def standardHelicoidNormal (r θ : ℝ) : Fin 3 → ℝ :=
  ![sin θ/helicoidQ r,-cos θ/helicoidQ r,r/helicoidQ r]

theorem standardHelicoid_r_hasDerivAt (r θ : ℝ) :
    HasDerivAt (fun x => standardHelicoid x θ) (standardHelicoidR θ) r := by
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases j <;> dsimp [standardHelicoid,standardHelicoidR]
  · simpa only [one_mul,id_eq] using (hasDerivAt_id r).mul_const (cos θ)
  · simpa only [one_mul,id_eq] using (hasDerivAt_id r).mul_const (sin θ)
  · exact hasDerivAt_const r θ

theorem standardHelicoid_theta_hasDerivAt (r θ : ℝ) :
    HasDerivAt (standardHelicoid r) (standardHelicoidTheta r θ) θ := by
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases j <;> dsimp [standardHelicoid,standardHelicoidTheta]
  · simpa only [neg_mul,mul_neg] using (hasDerivAt_cos θ).const_mul r
  · exact (hasDerivAt_sin θ).const_mul r
  · exact hasDerivAt_id θ

theorem standardHelicoid_metric (r θ : ℝ) :
    (∑ j, (standardHelicoidR θ j)^2) = 1 ∧
    (∑ j, standardHelicoidR θ j*standardHelicoidTheta r θ j) = 0 ∧
    (∑ j, (standardHelicoidTheta r θ j)^2) = (helicoidQ r)^2 := by
  simp only [Fin.sum_univ_succ,standardHelicoidR,standardHelicoidTheta,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero]
  refine ⟨?_,?_,?_⟩
  · nlinarith [sin_sq_add_cos_sq θ]
  · ring
  · rw [helicoidQ_sq]
    nlinarith [congrArg (fun x : ℝ => r^2*x) (sin_sq_add_cos_sq θ)]

theorem standardHelicoid_unit_normal (r θ : ℝ) :
    (∑ j, (standardHelicoidNormal r θ j)^2) = 1 ∧
    (∑ j, standardHelicoidR θ j*standardHelicoidNormal r θ j) = 0 ∧
    (∑ j, standardHelicoidTheta r θ j*standardHelicoidNormal r θ j) = 0 := by
  simp only [Fin.sum_univ_succ,standardHelicoidR,standardHelicoidTheta,standardHelicoidNormal,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero]
  refine ⟨?_,?_,?_⟩
  · field_simp [(helicoidQ_pos r).ne']
    nlinarith [helicoidQ_sq r,sin_sq_add_cos_sq θ]
  · ring
  · field_simp [(helicoidQ_pos r).ne']
    nlinarith [congrArg (fun x : ℝ => r*x) (sin_sq_add_cos_sq θ)]

theorem helicoidNormalMap_is_normal_displacement (r θ s : ℝ) :
    ![(helicoidNormalMap r θ s).1,(helicoidNormalMap r θ s).2.1,
      (helicoidNormalMap r θ s).2.2] = standardHelicoid r θ+s • standardHelicoidNormal r θ := by
  ext j
  fin_cases j <;> dsimp [helicoidNormalMap,standardHelicoid,standardHelicoidNormal,helicoidAngle] <;> ring

theorem standardHelicoidNormal_r_hasDerivAt (r θ : ℝ) :
    HasDerivAt (fun x => standardHelicoidNormal x θ)
      ((1/(helicoidQ r)^3) • standardHelicoidTheta r θ) r := by
  apply hasDerivAt_pi.mpr
  intro j
  have hq := helicoidQ_hasDerivAt r
  have hn := (helicoidQ_pos r).ne'
  fin_cases j <;> dsimp [standardHelicoidNormal,standardHelicoidTheta]
  · convert (hasDerivAt_const r (sin θ)).div hq hn using 1
    field_simp
    ring
  · convert (hasDerivAt_const r (-cos θ)).div hq hn using 1
    field_simp
    ring
  · convert (hasDerivAt_id r).div hq hn using 1
    · rfl
    · simp only [id_eq]
      field_simp
      nlinarith [helicoidQ_sq r]

theorem standardHelicoidNormal_theta_hasDerivAt (r θ : ℝ) :
    HasDerivAt (standardHelicoidNormal r) ((1/helicoidQ r) • standardHelicoidR θ) θ := by
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases j <;> dsimp [standardHelicoidNormal,standardHelicoidR]
  · convert (hasDerivAt_sin θ).div_const (helicoidQ r) using 1
    ring
  · convert (hasDerivAt_cos θ).neg.div_const (helicoidQ r) using 1
    ring
  · simpa using hasDerivAt_const θ (r/helicoidQ r)

/-- The square of the shape operator norm is exactly `(1+r²)⁻²`:
this coordinate identity also proves the uniform curvature bound used in §4.3. -/
theorem standardHelicoid_normal_differential_metric (r θ v w : ℝ) :
    (∑ j, (v/(helicoidQ r)^3*standardHelicoidTheta r θ j+
      w/helicoidQ r*standardHelicoidR θ j)^2) =
      (v^2+(helicoidQ r)^2*w^2)/(helicoidQ r)^4 := by
  have hnorm := standardHelicoid_metric r θ
  simp only [Fin.sum_univ_succ,standardHelicoidR,standardHelicoidTheta,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero]
  field_simp [(helicoidQ_pos r).ne']
  nlinarith [congrArg (fun x : ℝ => v^2*x) (sin_sq_add_cos_sq θ),
    congrArg (fun x : ℝ => (helicoidQ r)^4*w^2*x) (sin_sq_add_cos_sq θ),
    congrArg (fun x : ℝ => v^2*x) (helicoidQ_sq r)]

theorem standardHelicoid_shape_bound (r : ℝ) : 0 < 1/(helicoidQ r)^2 ∧ 1/(helicoidQ r)^2 ≤ 1 := by
  constructor
  · exact div_pos (by norm_num) (pow_pos (helicoidQ_pos r) _)
  · exact div_le_one_of_le₀ (one_le_pow₀ (helicoidQ_ge_one r)) (by positivity)

noncomputable def scaledHelicoidNormalMap (c r θ s : ℝ) : ℝ × ℝ × ℝ :=
  c • helicoidNormalMap r θ (s/c)

theorem scaledHelicoidNormalMap_injective {c r₁ r₂ θ₁ θ₂ s₁ s₂ : ℝ}
    (hc : 0 < c) (hs₁ : |s₁| < c) (hs₂ : |s₂| < c)
    (he : scaledHelicoidNormalMap c r₁ θ₁ s₁ = scaledHelicoidNormalMap c r₂ θ₂ s₂) :
    r₁ = r₂ ∧ θ₁ = θ₂ ∧ s₁ = s₂ := by
  have hh := congrArg (fun v : ℝ × ℝ × ℝ => c⁻¹ • v) he
  simp only [scaledHelicoidNormalMap,smul_smul,inv_mul_cancel₀ hc.ne',one_smul] at hh
  have h1 : |s₁/c| < 1 := by rw [abs_div,abs_of_pos hc]; exact (div_lt_one hc).mpr hs₁
  have h2 : |s₂/c| < 1 := by rw [abs_div,abs_of_pos hc]; exact (div_lt_one hc).mpr hs₂
  obtain ⟨hr,hθ,hs⟩ := helicoidNormalMap_injective h1 h2 hh
  exact ⟨hr,hθ,(div_left_inj' hc.ne').mp hs⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.standardHelicoid_unit_normal
#print axioms TwoAxisHelicoid.standardHelicoidNormal_r_hasDerivAt
#print axioms TwoAxisHelicoid.standardHelicoid_normal_differential_metric
