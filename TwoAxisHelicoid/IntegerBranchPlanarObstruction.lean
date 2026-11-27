import TwoAxisHelicoid.PlanarSectionFrame
import TwoAxisHelicoid.EssentialPlanarTurning
import TwoAxisHelicoid.PeriodSpinDisplacement
import TwoAxisHelicoid.SignCoverSections

namespace TwoAxisHelicoid
open Complex Set Matrix
set_option maxHeartbeats 1000000

theorem frameHorizontalTangent_norm (q : UnitQuaternion) (ht : (unitQuaternionFrame q).1.1 2 = 0) :
    ‖frameHorizontalTangent q‖ = 1 := by
  have h := (unitQuaternionFrame q).2.1
  have hs : normSq (frameHorizontalTangent q) = 1 := by
    simpa [frameHorizontalTangent,Complex.normSq_apply,dotProduct,Fin.sum_univ_three,ht] using h
  rw [normSq_eq_norm_sq] at hs
  nlinarith [norm_nonneg (frameHorizontalTangent q)]

theorem frameHorizontalTangent_direction (q : UnitQuaternion) (ht : (unitQuaternionFrame q).1.1 2 = 0)
    {v : ℂ} (hv : v ≠ 0) {k : ℝ} (hk : 0 < k) (h : frameHorizontalTangent q = (k : ℂ)*v) :
    frameHorizontalTangent q = (unitComplexDirection v hv : Circle) := by
  have he := frameHorizontalTangent_norm q ht
  rw [h,norm_mul,norm_real,Real.norm_eq_abs,abs_of_pos hk] at he
  change frameHorizontalTangent q = v/(‖v‖ : ℂ)
  rw [h,eq_div_iff (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv))]
  have hC : (k : ℂ)*(‖v‖ : ℂ) = 1 := by exact_mod_cast he
  calc
    (k : ℂ)*v*(‖v‖ : ℂ) = (k*(‖v‖ : ℂ))*v := by ring
    _ = v := by rw [hC,one_mul]

/-- An essential transverse simple planar section forces the spin character
of its lattice period to be nontrivial. Both tangent directions are the
actual derivatives of the indicated immersion. -/
theorem essential_planar_section_integer_character
    {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (m : ℤ) {C : ℂ} (hC0 : C ≠ 0) (hC : C^2 = (c : ℂ)/(2*thetaSigma t a^2))
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice, puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
      I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z)
    {ξ γ : ℝ → ℂ} (hξ : ContDiff ℝ 1 ξ) (hγ : ContDiff ℝ 1 γ)
    (ω : (rhombicPeriodPair t ht).lattice) (hω : ω.1 ≠ 0) (hper : ∀ r, ξ (r+1) = ξ r+ω.1)
    (hreg : ∀ r, deriv ξ r ≠ 0) (hinj : ∀ r h : ℝ, h ∈ Ioo (0 : ℝ) 1 → ξ (r+h) ≠ ξ r)
    (hξd : ∀ r, ξ r ∉ (rhombicPeriodPair t ht).lattice)
    (hpγ : Function.Periodic γ 1) (hregγ : ∀ r, deriv γ r ≠ 0)
    (hinjγ : ∀ r h : ℝ, h ∈ Ioo (0 : ℝ) 1 → γ (r+h) ≠ γ r)
    (hvel : ∀ r, fderiv ℝ X (ξ r) (deriv ξ r) = ![(deriv γ r).re,(deriv γ r).im,0])
    (htrans : ∀ r, (fderiv ℝ X (ξ r) (I*deriv ξ r)) 2 ≠ 0) :
    latticeSpinParity (rhombicPeriodPair t ht) m ω ≠ 0 := by
  let L := rhombicPeriodPair t ht
  let ξ₁ : C(unitInterval,PuncturedLatticePlane L) := ⟨fun r => ⟨ξ r.1,hξd r.1⟩,
    (hξ.continuous.comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨u,hu,hue⟩ := essential_torus_tangent_closed_half_angle hξ hω hper hreg hinj
  let f : C(unitInterval,UnitQuaternion) := ⟨fun r => unitSpinorQuaternionHomeomorph (weierstrassUnitLift ht ha m hC0 (ξ₁ r)),
    unitSpinorQuaternionHomeomorph.continuous.comp ((weierstrassUnitLift_continuous ht ha m hC0).comp ξ₁.continuous)⟩
  let q : C(unitInterval,UnitQuaternion) := ⟨fun r => spinCircleAction (u r) (f r),
    spinCircleAction_continuous.comp (f := fun r : unitInterval => (u r,f r)) (u.continuous.prodMk f.continuous)⟩
  let K := fun r : unitInterval => (spinorWeight (weierstrassSpinorPair t a m C (ξ r.1)))⁻¹ / ‖deriv ξ r.1‖
  have hK (r) : 0 < K r := div_pos (inv_pos.mpr (spinorWeight_pos (weierstrassSpinorPair_ne_zero ht ha m hC0 (hξd r.1))))
    (norm_pos_iff.mpr (hreg _))
  have hpair (r : unitInterval) : (unitQuaternionFrame (q r)).1 =
      (K r • fderiv ℝ X (ξ r.1) (deriv ξ r.1), K r • fderiv ℝ X (ξ r.1) (I*deriv ξ r.1)) := by
    apply quaternion_phase_aligns_differential _ _ _ _ (u r).normSq_coe
    · exact congrArg (fun v : Circle => (v : ℂ)) (hu r)
    · change (unitQuaternionFrame (unitSpinorQuaternionHomeomorph (weierstrassUnitLift ht ha m hC0 (ξ₁ r)))).1 = _
      rw [unitQuaternionFrame_spinor,← weierstrassTorusFrame_projection]
      exact harmonic_integer_torus_frame_derivative ht ha hc m hC0 hC hX hh hg (ξ₁ r)
  have hz (r : unitInterval) : (unitQuaternionFrame (q r)).1.1 2 = 0 := by rw [hpair,hvel]; simp
  have hb (r : unitInterval) : (unitQuaternionFrame (q r)).1.2 2 ≠ 0 := by
    rw [hpair]
    exact mul_ne_zero (hK r).ne' (htrans r.1)
  have hxy (r : unitInterval) : frameHorizontalTangent (q r) = unitComplexDirection (deriv γ r.1) (hregγ _) := by
    apply frameHorizontalTangent_direction (q r) (hz r) (hregγ _) (hK r)
    apply Complex.ext <;> simp [frameHorizontalTangent,hpair,hvel,Complex.mul_re,Complex.mul_im]
  have hnot := transverse_planar_section_quaternion_lift_not_closed hγ hpγ hregγ hinjγ q hz hb hxy
  intro hzero
  apply hnot
  have he : (ξ₁ 1).1 = (ξ₁ 0).1+ω.1 := by simpa [ξ₁] using hper 0
  have hf := weierstrassUnitLift_equivariant ht ha m hC0 ω (ξ₁ 0) (ξ₁ 1) he
  rw [hzero,zero_vadd] at hf
  exact congrArg₂ spinCircleAction hue (congrArg unitSpinorQuaternionHomeomorph hf)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.essential_planar_section_integer_character
