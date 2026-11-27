import TwoAxisHelicoid.WeierstrassRotation
import TwoAxisHelicoid.WeierstrassCoordinateData
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The phase, nonzero real height coefficient and additive integration constant
in the explicit Weierstrass data give precisely Euclidean isometries and positive
scaling. This does not identify an arbitrary embedded surface with that data. -/
namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

noncomputable def complexVerticalRotation (q : ℂ) (v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![(q.re : ℂ)*v 0-(q.im : ℂ)*v 1,
    (q.im : ℂ)*v 0+(q.re : ℂ)*v 1,v 2]

noncomputable def phasedCoordinateData (t a c : ℝ) (ht : 0 < t) (q z : ℂ) : Fin 3 → ℂ :=
  complexVerticalRotation q (coordinateData t a c ht z)

theorem coordinateData_real_smul (t a c : ℝ) (ht : 0 < t) (z : ℂ) :
    coordinateData t a c ht z = c • coordinateData t a 1 ht z := by
  ext j
  fin_cases j <;> simp [coordinateData,Algebra.smul_def] <;> ring

theorem complexVerticalRotation_real_smul (q : ℂ) (c : ℝ) (v : Fin 3 → ℂ) :
    complexVerticalRotation q (c • v) = c • complexVerticalRotation q v := by
  ext j
  fin_cases j <;> simp [complexVerticalRotation,Algebra.smul_def] <;> ring

theorem nullRealDerivative_real_smul (c : ℝ) (v : Fin 3 → ℂ) :
    nullRealDerivative (c • v) = c • nullRealDerivative v := by
  ext w j
  simp [Algebra.smul_def,Complex.mul_re,Complex.mul_im]
  ring

theorem nullRealDerivative_complexVerticalRotation (q : ℂ) (v : Fin 3 → ℂ) :
    nullRealDerivative (complexVerticalRotation q v) =
      (verticalRotation q).comp (nullRealDerivative v) := by
  ext w j
  fin_cases j <;>
    simp [complexVerticalRotation,verticalRotation_apply,Complex.mul_re,Complex.mul_im] <;> ring

theorem phasedCoordinateData_eq_original {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) {q z : ℂ} (hq : ‖q‖ = 1)
    (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    phasedCoordinateData t a c ht q z =
      weierstrassTriple (q*thetaGauss t a 1 z)
        (I*c*((rhombicPeriodPair t ht).weierstrassP z-
          (rhombicPeriodPair t ht).weierstrassP a)) := by
  rw [weierstrassTriple_unit_multiplier hq]
  unfold phasedCoordinateData
  rw [coordinateData_eq_original ht ha hz hm hp]
  rfl

theorem actual_coordinate_primitives_phase_scale {s : Set ℂ}
    (hs : IsOpen s) (hconn : IsPreconnected s) {t a c : ℝ} (ht : 0 < t)
    (q : ℂ) {X Y : ℂ → Fin 3 → ℝ}
    (hX : ∀ z ∈ s, HasFDerivAt X (nullRealDerivative (coordinateData t a 1 ht z)) z)
    (hY : ∀ z ∈ s, HasFDerivAt Y (nullRealDerivative (phasedCoordinateData t a c ht q z)) z) :
    ∃ b : Fin 3 → ℝ, ∀ z ∈ s, Y z = c • verticalRotation q (X z)+b := by
  have hR (z : ℂ) (hz : z ∈ s) :=
    ((verticalRotation q).hasFDerivAt.comp z (hX z hz)).const_smul c
  apply hs.exists_eq_add_of_fderiv_eq hconn
    (fun z hz => (hY z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hR z hz).differentiableAt.differentiableWithinAt)
  intro z hz
  rw [(hY z hz).fderiv,(hR z hz).fderiv]
  unfold phasedCoordinateData
  rw [coordinateData_real_smul,complexVerticalRotation_real_smul,
    nullRealDerivative_real_smul,nullRealDerivative_complexVerticalRotation]

theorem verticalRotation_mul (q r : ℂ) (v : Fin 3 → ℝ) :
    verticalRotation q (verticalRotation r v) = verticalRotation (q*r) v := by
  ext j
  fin_cases j <;> simp [verticalRotation_apply,Complex.mul_re,Complex.mul_im] <;> ring

@[simp] theorem verticalRotation_one (v : Fin 3 → ℝ) : verticalRotation 1 v = v := by
  ext j
  fin_cases j <;> simp [verticalRotation_apply]

noncomputable def euclideanVerticalRotation (q : ℂ) (hq : ‖q‖ = 1) :
    EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toLinearMap := (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap.comp
    ((verticalRotation q).toLinearMap.comp (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap)
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    exact verticalRotation_preserves_squared_length hq v

@[simp] theorem euclideanVerticalRotation_apply (q : ℂ) (hq : ‖q‖ = 1)
    (v : EuclideanSpace ℝ (Fin 3)) :
    euclideanVerticalRotation q hq v = WithLp.toLp 2 (verticalRotation q v) := rfl

noncomputable def euclideanVerticalRotationEquiv (q : ℂ) (hq : ‖q‖ = 1) :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearIsometryEquiv.ofSurjective (euclideanVerticalRotation q hq) (by
    intro v
    refine ⟨WithLp.toLp 2 (verticalRotation (q⁻¹) v),?_⟩
    rw [euclideanVerticalRotation_apply]
    change WithLp.toLp 2 (verticalRotation q (verticalRotation (q⁻¹) v)) = v
    rw [verticalRotation_mul,mul_inv_cancel₀ (by intro h; simp [h] at hq),verticalRotation_one])

@[simp] theorem euclideanVerticalRotationEquiv_apply (q : ℂ) (hq : ‖q‖ = 1)
    (v : EuclideanSpace ℝ (Fin 3)) :
    euclideanVerticalRotationEquiv q hq v = WithLp.toLp 2 (verticalRotation q v) := rfl

/-- The nonzero signed coefficient is absorbed by a positive scale and an
orthogonal map (central reflection is allowed when the coefficient is negative). -/
theorem actual_coordinate_primitives_similarity {s : Set ℂ}
    (hs : IsOpen s) (hconn : IsPreconnected s) {t a c : ℝ} (ht : 0 < t)
    (hc : c ≠ 0) {q : ℂ} (hq : ‖q‖ = 1) {X Y : ℂ → Fin 3 → ℝ}
    (hX : ∀ z ∈ s, HasFDerivAt X (nullRealDerivative (coordinateData t a 1 ht z)) z)
    (hY : ∀ z ∈ s, HasFDerivAt Y (nullRealDerivative (phasedCoordinateData t a c ht q z)) z) :
    ∃ (scale : ℝ) (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3)),
      0 < scale ∧ ∀ z ∈ s,
        WithLp.toLp 2 (Y z) = scale • R (WithLp.toLp 2 (X z))+b := by
  obtain ⟨b,hb⟩ := actual_coordinate_primitives_phase_scale hs hconn ht q hX hY
  by_cases hp : 0 < c
  · refine ⟨c,euclideanVerticalRotationEquiv q hq,WithLp.toLp 2 b,hp,?_⟩
    intro z hz
    rw [hb z hz,euclideanVerticalRotationEquiv_apply]
    rfl
  · have hn : c < 0 := lt_of_le_of_ne (le_of_not_gt hp) hc
    refine ⟨-c,(euclideanVerticalRotationEquiv q hq).trans (LinearIsometryEquiv.neg ℝ),
      WithLp.toLp 2 b,neg_pos.mpr hn,?_⟩
    intro z hz
    rw [hb z hz]
    change WithLp.toLp 2 (c • verticalRotation q (X z)+b) =
      (-c) • -(WithLp.toLp 2 (verticalRotation q (X z)))+WithLp.toLp 2 b
    simp only [neg_smul,smul_neg,neg_neg]
    rfl

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_coordinate_primitives_similarity
