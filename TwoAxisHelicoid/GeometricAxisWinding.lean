import TwoAxisHelicoid.AxisHelicoidTangentPlanes
import TwoAxisHelicoid.HeightEndAxis

namespace TwoAxisHelicoid
open Set Complex
open scoped ComplexConjugate
attribute [local irreducible] thetaGauss

theorem thetaGauss_axis_normSq {t a y : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    (m : ℤ) (hy : y ∈ Ioo (0 : ℝ) (2*t)) : normSq (thetaGauss t a m (I*y)) = 1 := by
  obtain ⟨_,hm,hp⟩ := integerAxis_regular_points ht ha hy
  have h := thetaGauss_neg_product ht a m hm hp
  have hc := thetaGauss_conj t a m (I*(y : ℂ))
  rw [show conj (I*(y : ℂ)) = -(I*y) by simp] at hc
  rw [hc,neg_mul,neg_inj,mul_comm,Complex.mul_conj] at h
  exact_mod_cast h

theorem harmonic_height_real_primitive {t a c : ℝ} (ht : 0 < t)
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 = coordinateData t a c ht z 2) :
    ∃ b : ℝ, ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      X z 2 = (actualComplexHeight t a c ht z).re+b := by
  let H := actualComplexHeight t a c ht
  let U := (rhombicPeriodPair t ht).lattice
  have hd (z : ℂ) (hz : z ∉ U) : HasFDerivAt (fun w => X w 2)
      (realCoefficientDerivative (coordinateData t a c ht z 2)) z := by
    exact ((ContinuousLinearMap.proj 2 : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z
      (puncturedImmersionCoefficient_hasFDerivAt hX hz)).congr_fderiv (by
        ext w
        change (w*puncturedImmersionCoefficient _ X z 2).re = _
        rw [hh z hz]
        rfl)
  have hd' (z : ℂ) (hz : z ∉ U) : HasFDerivAt (fun w => (H w).re)
      (realCoefficientDerivative (coordinateData t a c ht z 2)) z :=
    Complex.reCLM.hasFDerivAt.comp z ((actualComplexHeight_hasDerivAt ht hz).hasFDerivAt.restrictScalars ℝ)
  exact (rhombicPeriodPair t ht).isClosed_lattice.isOpen_compl.exists_eq_add_of_fderiv_eq
    (rhombic_punctured_plane_isConnected ht).2
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd' z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).fderiv.trans (hd' z hz).fderiv.symm)

theorem harmonic_integer_axis_height_difference {t a c : ℝ} (ht : 0 < t)
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 = coordinateData t a c ht z 2)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) (2*t)) :
    actualComplexHeight t a c ht (I*y)-actualComplexHeight t a c ht (I*t) =
      ((X (I*y) 2-X (I*t) 2 : ℝ) : ℂ) := by
  let H := actualComplexHeight t a c ht
  let U := (rhombicPeriodPair t ht).lattice
  obtain ⟨b,hb⟩ := harmonic_height_real_primitive ht hX hh
  have hmem (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) (2*t)) : I*(s : ℂ) ∉ U := by
    simpa only [Complex.ofReal_zero,zero_add] using
      rhombic_vertical_strip_not_mem ht (by norm_num : (0 : ℝ) ∈ Ioo (-1) 1) hs
  have hreal (s : ℝ) : (H (I*s)).im = 0 := by
    have hh := actualComplexHeight_reflection (a := a) (c := c) ht (I*(s : ℂ))
    rw [show -conj (I*(s : ℂ)) = I*s by simp] at hh
    have hi := congrArg Complex.im hh
    change (H (I*s)).im = -(H (I*s)).im at hi
    linarith
  rw [hb _ (hmem y hy),hb _ (hmem t ⟨ht,by linarith⟩)]
  apply Complex.ext
  · simp
  · change (H (I*y)).im - (H (I*t)).im = 0
    rw [hreal,hreal,sub_self]

/-- Once intersections away from the origin exclude actual tangent-plane
coincidence along the vertical axis, all branches except 0 and 1 are
impossible. The helicoid is calibrated by the Gauss direction and actual
height at the axes' common point, allowing translations of height. -/
theorem harmonic_integer_axis_parameter_of_distinct_tangent_planes {t a c : ℝ}
    (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 = coordinateData t a c ht z 2)
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z)
    (hdist : ∀ y ∈ Ioo (0 : ℝ) (2*t), y ≠ t →
      range (fderiv ℝ X (I*y)) ≠ range (fderiv ℝ
        (axisRuledHelicoid (thetaGauss t a m (I*t)) (2*(a-m)/c) (X (I*t) 2)) (I*(X (I*y) 2)))) :
    m = 0 ∨ m = 1 := by
  apply integerAxisPhase_parameter_zero_or_one ht ha m
  intro y hy
  have hp (hd : integerAxisPhase t a m y = -Real.pi ∨ integerAxisPhase t a m y = Real.pi) : False := by
    have hyn : y ≠ t := by
      rintro rfl
      rw [integerAxisPhase_midpoint] at hd
      rcases hd with h | h <;> linarith [Real.pi_pos]
    apply hdist y hy hyn
    have hz := (not_mem_gaussLogPoleSet _ _ _).mpr (integerAxis_regular_points ht ha hy)
    have hn : coordinateData t a c ht (I*y) 2 ≠ 0 :=
      null_height_nonzero_away_pair ht ha (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hc))
        (p := coordinateData t a c ht) (fun _ _ => rfl) hz
    rw [(harmonic_integer_gauss_data_has_coordinate_differential ht ha hc m hX hh hg _ hz).fderiv,
      weierstrass_unit_gauss_tangent_range (thetaGauss_axis_normSq ht ha m hy) hn,
      axisRuledHelicoid_tangent_range]
    have he := thetaGauss_integerAxisPhase_identity ht ha hG hc m hy
    dsimp only at he
    rw [harmonic_integer_axis_height_difference ht hX hh hy,mul_add,Complex.exp_add] at he
    have hsign : Complex.exp (I*(integerAxisPhase t a m y : ℂ)) = -1 := by
      rcases hd with hd | hd
      · rw [hd,Complex.ofReal_neg,mul_neg,mul_comm,Complex.exp_neg_pi_mul_I]
      · rw [hd,mul_comm,Complex.exp_pi_mul_I]
    rw [hsign,mul_neg_one,mul_neg] at he
    rw [he,verticalGaussPlane_neg]
    push_cast
    rfl
  exact ⟨fun h => hp (Or.inl h),fun h => hp (Or.inr h)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_integer_axis_parameter_of_distinct_tangent_planes
