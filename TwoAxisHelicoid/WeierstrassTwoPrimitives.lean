import TwoAxisHelicoid.WeierstrassSimilarity

namespace TwoAxisHelicoid
open Complex Set

theorem complexVerticalRotation_mul (q r : ℂ) (v : Fin 3 → ℂ) :
    complexVerticalRotation q (complexVerticalRotation r v)=complexVerticalRotation (q*r) v := by
  ext j
  fin_cases j <;> simp [complexVerticalRotation,Complex.mul_re,Complex.mul_im] <;> ring

theorem phasedCoordinateData_change_phase_scale (t a c₁ c₂ : ℝ) (ht : 0 < t)
    (hc₁ : c₁ ≠ 0) (q₁ q₂ z : ℂ) (hq₁ : q₁ ≠ 0) :
    phasedCoordinateData t a c₂ ht q₂ z =
      (c₂/c₁) • complexVerticalRotation (q₂/q₁) (phasedCoordinateData t a c₁ ht q₁ z) := by
  unfold phasedCoordinateData
  rw [coordinateData_real_smul t a c₂ ht z,coordinateData_real_smul t a c₁ ht z]
  simp only [complexVerticalRotation_real_smul,
    complexVerticalRotation_mul,smul_smul]
  rw [div_mul_cancel₀ q₂ hq₁,div_mul_cancel₀ c₂ hc₁]

theorem actual_two_coordinate_primitives_phase_scale {s : Set ℂ}
    (hs : IsOpen s) (hconn : IsPreconnected s) {t a c₁ c₂ : ℝ} (ht : 0 < t)
    (hc₁ : c₁ ≠ 0) (q₁ q₂ : ℂ) (hq₁ : q₁ ≠ 0) {X Y : ℂ → Fin 3 → ℝ}
    (hX : ∀ z ∈ s, HasFDerivAt X (nullRealDerivative (phasedCoordinateData t a c₁ ht q₁ z)) z)
    (hY : ∀ z ∈ s, HasFDerivAt Y (nullRealDerivative (phasedCoordinateData t a c₂ ht q₂ z)) z) :
    ∃ b : Fin 3 → ℝ, ∀ z ∈ s, Y z=(c₂/c₁) • verticalRotation (q₂/q₁) (X z)+b := by
  have hR (z : ℂ) (hz : z ∈ s) :=
    ((verticalRotation (q₂/q₁)).hasFDerivAt.comp z (hX z hz)).const_smul (c₂/c₁)
  apply hs.exists_eq_add_of_fderiv_eq hconn
    (fun z hz => (hY z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hR z hz).differentiableAt.differentiableWithinAt)
  intro z hz
  rw [(hY z hz).fderiv,(hR z hz).fderiv,
    phasedCoordinateData_change_phase_scale t a c₁ c₂ ht hc₁ q₁ q₂ z hq₁,
    nullRealDerivative_real_smul,nullRealDerivative_complexVerticalRotation]

/-- Any two primitives of the same actual normalized data, allowing arbitrary
unit Gauss phases and nonzero real height scales, differ by a positive Euclidean
similarity. No canonical primitive is assumed to exist. -/
theorem actual_two_coordinate_primitives_similarity {s : Set ℂ}
    (hs : IsOpen s) (hconn : IsPreconnected s) {t a c₁ c₂ : ℝ} (ht : 0 < t)
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) {q₁ q₂ : ℂ} (hq₁ : ‖q₁‖=1) (hq₂ : ‖q₂‖=1)
    {X Y : ℂ → Fin 3 → ℝ}
    (hX : ∀ z ∈ s, HasFDerivAt X (nullRealDerivative (phasedCoordinateData t a c₁ ht q₁ z)) z)
    (hY : ∀ z ∈ s, HasFDerivAt Y (nullRealDerivative (phasedCoordinateData t a c₂ ht q₂ z)) z) :
    ∃ (scale : ℝ) (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3)), 0 < scale ∧
        ∀ z ∈ s, WithLp.toLp 2 (Y z)=scale • R (WithLp.toLp 2 (X z))+b := by
  have hq₁n : q₁ ≠ 0 := by intro h; simp [h] at hq₁
  have hq : ‖q₂/q₁‖=1 := by rw [norm_div,hq₁,hq₂,div_one]
  have hr : c₂/c₁ ≠ 0 := div_ne_zero hc₂ hc₁
  obtain ⟨b,hb⟩ := actual_two_coordinate_primitives_phase_scale hs hconn ht hc₁ q₁ q₂ hq₁n hX hY
  by_cases hp : 0 < c₂/c₁
  · refine ⟨c₂/c₁,euclideanVerticalRotationEquiv (q₂/q₁) hq,WithLp.toLp 2 b,hp,?_⟩
    intro z hz
    rw [hb z hz,euclideanVerticalRotationEquiv_apply]
    rfl
  · have hn : c₂/c₁ < 0 := lt_of_le_of_ne (le_of_not_gt hp) hr
    refine ⟨-(c₂/c₁),(euclideanVerticalRotationEquiv (q₂/q₁) hq).trans
      (LinearIsometryEquiv.neg ℝ),WithLp.toLp 2 b,neg_pos.mpr hn,?_⟩
    intro z hz
    rw [hb z hz]
    change WithLp.toLp 2 ((c₂/c₁) • verticalRotation (q₂/q₁) (X z)+b) =
      (-(c₂/c₁)) • -(WithLp.toLp 2 (verticalRotation (q₂/q₁) (X z)))+WithLp.toLp 2 b
    simp only [neg_smul,smul_neg,neg_neg]
    rfl

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_two_coordinate_primitives_similarity
