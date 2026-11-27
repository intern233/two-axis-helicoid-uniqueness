import TwoAxisHelicoid.JacobiAbsoluteNormalization
import TwoAxisHelicoid.ThetaJacobiIdentity
import TwoAxisHelicoid.LeftParameterLimits

namespace TwoAxisHelicoid
open Complex

/-- The odd characteristic in the manuscript's radian variable, expressed using the
two-variable Jacobi theta function through its translated function `jacobiOdd`. -/
noncomputable def rhombicManuscriptThetaOne (s : ℝ) (v : ℂ) : ℂ :=
  (-I) * exp ((Real.pi : ℂ) * I * rhombicTau s / 4) *
    (exp (v * I) * jacobiOdd (v / Real.pi) (rhombicTau s))

/-- The fourth root in the theta prefactor uses the exponential lift of the nome. -/
theorem rhombic_theta_fourth_root (s : ℝ) :
    exp ((Real.pi : ℂ) * I * rhombicTau s / 4)^4 =
      I * (Real.exp (-Real.pi * s / 2) : ℂ) := by
  rw [← Complex.exp_nat_mul]
  have h : (4 : ℂ) * ((Real.pi : ℂ) * I * rhombicTau s / 4) =
      (Real.pi : ℂ) / 2 * I + ((-Real.pi * s / 2 : ℝ) : ℂ) := by
    unfold rhombicTau
    push_cast
    ring_nf
    simp only [I_sq]
    ring
  change exp ((4 : ℂ) * ((Real.pi : ℂ) * I * rhombicTau s / 4)) = _
  rw [h, Complex.exp_add, Complex.exp_pi_div_two_mul_I, Complex.ofReal_exp]

private theorem left_half_angle_square (w : ℂ) :
    exp (((Real.pi / 2 : ℂ) * w) * I)^2 = jacobiExp w := by
  rw [pow_two, ← Complex.exp_add, jacobiExp]
  congr 1
  ring

/-- The selected lift of the inverse half-power is entire on the w-plane. -/
theorem left_inverse_half_nome_lift :
    Differentiable ℂ (fun w : ℂ => exp (-I * (Real.pi : ℂ) * w / 2)) ∧
      ∀ w : ℂ, exp (-I * (Real.pi : ℂ) * w / 2)^2 = (jacobiExp w)⁻¹ := by
  constructor
  · fun_prop
  · intro w
    rw [show -I * (Real.pi : ℂ) * w / 2 = -(((Real.pi / 2 : ℂ) * w) * I) by ring,
      Complex.exp_neg, inv_pow, left_half_angle_square]

private theorem left_half_angle_factors (w : ℂ) :
    let a := (Real.pi / 2 : ℂ) * w
    2 * exp (a * I) * sin a = I * (1 - jacobiExp w) ∧
      2 * exp (a * I) * cos a = jacobiExp w + 1 := by
  dsimp only
  rw [← left_half_angle_square w]
  constructor
  · simp only [Complex.sin, neg_mul, Complex.exp_neg]
    field_simp [Complex.exp_ne_zero]
  · simp only [Complex.cos, neg_mul, Complex.exp_neg]
    field_simp [Complex.exp_ne_zero]

/-- Formula at line 1147, with the global lift of the inverse square root on the
w-plane.  It holds at the zeros as well as away from them. -/
theorem rhombicManuscriptThetaOne_eq_absolute_product {s : ℝ} (hs : 0 < s) (w : ℂ) :
    rhombicManuscriptThetaOne s ((Real.pi / 2 : ℂ) * w) =
      I * exp ((Real.pi : ℂ) * I * rhombicTau s / 4) *
        exp (-I * (Real.pi : ℂ) * w / 2) * (1 - jacobiExp w) *
        rhombicEulerProduct s *
        (jacobiFactorProduct (jacobiNome s) (jacobiExp w) *
         jacobiFactorProduct (jacobiNome s) (jacobiExp w)⁻¹) := by
  let a := (Real.pi / 2 : ℂ) * w
  let C := exp ((Real.pi : ℂ) * I * rhombicTau s / 4)
  have hjet := thetaScaledJet_zero_absolute_product hs w
  simp only [thetaScaledJet, pow_zero, one_mul] at hjet
  have hsin : 2 * sin a =
      I * exp (-I * (Real.pi : ℂ) * w / 2) * (1 - jacobiExp w) := by
    have he : -I * (Real.pi : ℂ) * w / 2 = -(a * I) := by dsimp [a]; ring
    calc
      2 * sin a = (exp (a * I))⁻¹ * (2 * exp (a * I) * sin a) := by
        field_simp [Complex.exp_ne_zero]
      _ = _ := by rw [(left_half_angle_factors w).1, he, Complex.exp_neg]; ring
  change (-I) * C * (exp (a * I) * jacobiOdd (a / Real.pi) (rhombicTau s)) = _
  rw [← thetaBilateral_eq_jacobiOdd hs a]
  calc
    (-I) * C * ((2 * I) * thetaJet s 0 a) = C * (2 * thetaJet s 0 a) := by
      linear_combination (-2 * C * thetaJet s 0 a) * Complex.I_sq
    _ = C * (2 * sin a) * rhombicEulerProduct s *
        (jacobiFactorProduct (jacobiNome s) (jacobiExp w) *
         jacobiFactorProduct (jacobiNome s) (jacobiExp w)⁻¹) := by
      change C * (2 * thetaJet s 0 ((Real.pi / 2 : ℂ) * w)) = _
      rw [hjet]
      dsimp [a]
      ring
    _ = _ := by rw [hsin]; dsimp [C]; ring

/-- The dual height and the original manuscript nome, with both Euler products
written literally.  `Q` is the square of the imaginary theta nome. -/
theorem leftThetaOne_eq_manuscript_product {t : ℝ} (ht : 0 < t) (w : ℂ) :
    let Q : ℂ := (-((leftNome t)^2 : ℝ) : ℂ)
    let x := jacobiExp w
    rhombicManuscriptThetaOne (1/t) ((Real.pi / 2 : ℂ) * w) =
      I * exp ((Real.pi : ℂ) * I * rhombicTau (1/t) / 4) *
        exp (-I * (Real.pi : ℂ) * w / 2) * (1 - x) *
        (∏' n : ℕ, (1 - Q^(n+1))) *
        (∏' n : ℕ, ((1 - Q^(n+1)*x) * (1 - Q^(n+1)/x))) := by
  dsimp only
  have hs := one_div_pos.mpr ht
  let Q := jacobiNome (1/t)
  have hq : ‖Q‖ < 1 := jacobiNome_norm_lt_one hs
  let x := jacobiExp w
  have hd : (∏' n : ℕ, ((1 - Q^(n+1)*x) * (1 - Q^(n+1)/x))) =
      jacobiFactorProduct Q x * jacobiFactorProduct Q x⁻¹ := by
    simpa only [jacobiFactorProduct, div_eq_mul_inv] using
      (jacobiFactorProduct_multipliable hq x).tprod_mul (jacobiFactorProduct_multipliable hq x⁻¹)
  rw [← jacobiNome_inverse_eq_leftNome ht, hd]
  exact rhombicManuscriptThetaOne_eq_absolute_product hs w

theorem left_manuscript_theta_fourth_root {t : ℝ} (ht : 0 < t) :
    exp ((Real.pi : ℂ) * I * rhombicTau (1/t) / 4)^4 = I * (leftNome t : ℂ) := by
  rw [rhombic_theta_fourth_root, leftNome_eq_exp_neg_kappa0]
  have h : -Real.pi * (1/t) / 2 = -leftKappa0 t := by
    unfold leftKappa0
    field_simp [ht.ne']
  rw [h]

/-- The line 1238 substitution is the genuine cotangent in the manuscript coordinate. -/
theorem cot_half_period_eq_leftMobius {w : ℂ} (hx : jacobiExp w ≠ 1) :
    cot ((Real.pi / 2 : ℂ) * w) = leftMobius (jacobiExp w) := by
  let a := (Real.pi / 2 : ℂ) * w
  let E := exp (a * I)
  have hE : (2 : ℂ) * E ≠ 0 := mul_ne_zero two_ne_zero (Complex.exp_ne_zero _)
  calc
    cos a / sin a = (2 * E * cos a) / (2 * E * sin a) :=
      (mul_div_mul_left _ _ hE).symm
    _ = (jacobiExp w + 1) / (I * (1 - jacobiExp w)) := by
      rw [(left_half_angle_factors w).1, (left_half_angle_factors w).2]
    _ = leftMobius (jacobiExp w) := by
      unfold leftMobius
      field_simp [I_ne_zero, sub_ne_zero.mpr hx, sub_ne_zero.mpr hx.symm]
      ring_nf
      simp [I_sq]
      ring

private theorem left_half_angle_rational_square {w : ℂ} (hx : jacobiExp w ≠ 1) :
    let a := (Real.pi / 2 : ℂ) * w
    sin a ≠ 0 ∧ (jacobiExp w)^2 / (1 - jacobiExp w)^2 =
      -jacobiExp w / (4 * sin a ^ 2) := by
  let a := (Real.pi / 2 : ℂ) * w
  let E := exp (a * I)
  have hs : 2 * E * sin a = I * (1 - jacobiExp w) := (left_half_angle_factors w).1
  have hd := sub_ne_zero.mpr hx.symm
  have hn : sin a ≠ 0 := by
    intro h
    rw [h, mul_zero] at hs
    exact (mul_ne_zero I_ne_zero hd) hs.symm
  refine ⟨hn, ?_⟩
  have hsq : 4 * jacobiExp w * sin a^2 = -(1 - jacobiExp w)^2 := by
    calc
      4 * jacobiExp w * sin a^2 = (2 * E * sin a)^2 := by
        rw [← left_half_angle_square w]
        dsimp [E, a]
        ring
      _ = (I * (1 - jacobiExp w))^2 := by rw [hs]
      _ = _ := by rw [mul_pow, I_sq, neg_one_mul]
  apply (div_eq_div_iff (pow_ne_zero 2 hd) (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (pow_ne_zero 2 hn))).mpr
  linear_combination jacobiExp w * hsq

/-- The exact trigonometric expression of the actual comparison integrand (line 1232). -/
theorem leftComparisonFunction_eq_cotangent {t : ℝ} (ht : 0 < t) {w : ℂ}
    (hx : jacobiExp w ≠ 1) :
    leftComparisonFunction t w =
      (-I * (Real.pi : ℂ)^2 / (4 * (t : ℂ))) * jacobiExp w *
        (sin ((Real.pi / 2 : ℂ) * w)^2)⁻¹ *
        exp (I * (leftKappa t : ℂ) * cot ((Real.pi / 2 : ℂ) * w)) := by
  obtain ⟨hs, hsq⟩ := left_half_angle_rational_square hx
  have hex : (leftKappa t : ℂ) * (-1 + 2 / (1 - jacobiExp w)) =
      I * (leftKappa t : ℂ) * cot ((Real.pi / 2 : ℂ) * w) := by
    rw [cot_half_period_eq_leftMobius hx, ← I_mul_leftMobius hx]
    ring
  unfold leftComparisonFunction dualProductMainTerm
  rw [← leftKappa_eq_dualProductKappa ht, hex, div_pow, hsq]
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne', hs]

theorem leftComparisonFunction_cotangent_on_vertical_line {t : ℝ} (ht : 0 < t) (y : ℝ) :
    let w := leftPathW y
    let a := (Real.pi / 2 : ℂ) * w
    leftPathU y = cot a ∧
      leftComparisonFunction t w = (-I * (Real.pi : ℂ)^2 / (4 * (t : ℂ))) *
        jacobiExp w * (sin a ^ 2)⁻¹ * exp (I * (leftKappa t : ℂ) * cot a) :=
  ⟨(cot_half_period_eq_leftMobius (leftPathX_ne_one y)).symm,
    leftComparisonFunction_eq_cotangent ht (leftPathX_ne_one y)⟩

/-- The two hyperbolic endpoint parameters in line 1238, in the original nome. -/
theorem leftChordHK_eq_hyperbolic (t : ℝ) :
    leftChordH (leftNome t) = (Real.cosh (leftKappa0 t))⁻¹ ∧
      leftChordK (leftNome t) = Real.tanh (leftKappa0 t) := by
  have hq := leftNome_pos t
  have hi : Real.exp (leftKappa0 t) = (leftNome t)⁻¹ := by
    rw [leftNome_eq_exp_neg_kappa0, Real.exp_neg, inv_inv]
  have hs : (leftNome t)⁻¹ + leftNome t ≠ 0 := (add_pos (inv_pos.mpr hq) hq).ne'
  have hd : 1 + (leftNome t)^2 ≠ 0 := by positivity
  rw [Real.cosh_eq, Real.tanh_eq, hi, ← leftNome_eq_exp_neg_kappa0,
    leftChordH, leftChordK]
  constructor <;> field_simp [hq.ne', hs, hd]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftThetaOne_eq_manuscript_product
#print axioms TwoAxisHelicoid.left_manuscript_theta_fourth_root
#print axioms TwoAxisHelicoid.left_inverse_half_nome_lift
#print axioms TwoAxisHelicoid.leftComparisonFunction_cotangent_on_vertical_line
#print axioms TwoAxisHelicoid.leftComparisonFunction_eq_cotangent
#print axioms TwoAxisHelicoid.cot_half_period_eq_leftMobius
#print axioms TwoAxisHelicoid.leftChordHK_eq_hyperbolic
