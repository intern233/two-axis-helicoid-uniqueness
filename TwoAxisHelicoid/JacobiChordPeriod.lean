import TwoAxisHelicoid.JacobiChordAnalytic

namespace TwoAxisHelicoid
open Complex Set Metric MeasureTheory
set_option maxHeartbeats 1000000
attribute [local irreducible] thetaA dualThetaA jacobiPairProduct jacobiProductError

noncomputable def jacobiArcDifferential (t a y : ℝ) : ℂ :=
  I*(I*(t : ℂ)*dualThetaA t a (leftPathW y))

theorem horizontalPeriod_eq_jacobiArc {t a : ℝ} (ht : 0 < t)
    (ha0 : 0 < a) (ha1 : a < 1) :
    thetaHorizontalPeriod t a =
      -(∫ y : ℝ in (-(1/(2*t)))..(1/(2*t)), jacobiArcDifferential t a y).re := by
  have ha := real_not_mem_rhombic_lattice_of_pos ht ha0 (by linarith : a < 2)
  have hsub := intervalIntegral.integral_comp_div
    (fun y : ℝ => dualThetaA t a (leftPathW y)) ht.ne'
    (a := (-1/2 : ℝ)) (b := (1/2 : ℝ))
  have he (y : ℝ) : jacobiArcDifferential t a y =
      -(t : ℂ)*dualThetaA t a (leftPathW y) := by
    unfold jacobiArcDifferential
    simp only [← mul_assoc]
    rw [← pow_two, I_sq, neg_one_mul]
  simp only [div_div, neg_div, Complex.real_smul] at hsub
  rw [horizontal_period_dual ht ha]
  change (∫ x : ℝ in (-1/2)..(1/2), dualThetaA t a (leftPathW (x/t))).re = _
  simp only [neg_div]
  rw [hsub]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, neg_mul, Complex.neg_re, neg_neg]

theorem jacobiArcDifferential_continuous {t a : ℝ} (ht : 0 < t)
    (ha0 : 0 < a) (ha1 : a < 1) : Continuous (jacobiArcDifferential t a) := by
  have hreg := real_not_mem_rhombic_lattice_of_pos ht ha0 (by linarith : a < 2)
  have he (y : ℝ) : dualThetaA t a (leftPathW y) =
      thetaA t a (((-(t*y) : ℝ) : ℂ)+I*((t/2 : ℝ) : ℂ)) := by
    have h := dualThetaA_midline ht hreg (t*y)
    have hdiv : t*y/t = y := by field_simp [ht.ne']
    rw [hdiv] at h
    exact h
  have hc := (horizontal_integrand_continuous ht a).comp
    (by fun_prop : Continuous (fun y : ℝ => -(t*y)))
  unfold jacobiArcDifferential
  simp_rw [he]
  exact continuous_const.mul (continuous_const.mul hc)

theorem jacobiMainTerm_mobius {t : ℝ} (ht : 0 < t) (a : ℝ) {w : ℂ}
    (hx : jacobiExp w ≠ 1) :
    I*(t : ℂ)*dualProductMainTerm t a w =
      leftChordDifferential t (dualProductKappa t a) (leftMobius (jacobiExp w))*
        ((-2*I/(jacobiExp w-1)^2)*(I*(Real.pi : ℂ)*jacobiExp w)) := by
  have he : I*(dualProductKappa t a : ℂ)*leftMobius (jacobiExp w) =
      (dualProductKappa t a : ℂ)*(-1+2/(1-jacobiExp w)) := by
    rw [mul_right_comm, I_mul_leftMobius hx]
    ring
  unfold leftChordDifferential
  rw [leftMobius_ratio hx, he]
  unfold dualProductMainTerm
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne',
    sub_ne_zero.mpr hx, sub_ne_zero.mpr hx.symm]
  simp only [I_sq]
  ring

theorem jacobiArcDifferential_chain {t a y : ℝ} (ht : 0 < t)
    (ha0 : 0 < a) (ha1 : a < 1)
    (hy : y ∈ Icc (-(1/(2*t))) (1/(2*t))) :
    jacobiArcDifferential t a y = jacobiChordDifferential t a (leftPathU y)*
      (((-2*I/(jacobiExp (leftPathW y)-1)^2)*
        (I*(Real.pi : ℂ)*jacobiExp (leftPathW y)))*I) := by
  have hreg := leftPath_product_region ht hy
  have hf := dualThetaA_eq_product ht ha0 ha1 (leftPathX_ne_one y) hreg.1 hreg.2
  have he : jacobiArcDifferential t a y =
      (I*(I*(t : ℂ)*dualProductMainTerm t a (leftPathW y)))*
      jacobiProductError (jacobiNome (1/t)) (dualProductR t a) (dualProductKappa t a)
        (jacobiExp (leftPathW y)) := by
    unfold jacobiArcDifferential
    rw [hf, dualProductIntegrand_factor]
    ring
  rw [he, jacobiMainTerm_mobius ht a (leftPathX_ne_one y)]
  unfold jacobiChordDifferential leftPathU jacobiChordX
  rw [leftMobius_ratio (leftPathX_ne_one y)]
  ring

theorem jacobiArc_primitive_difference {t a : ℝ} (ht : 0 < t)
    (ha0 : 0 < a) (ha1 : a < 1) {g : ℂ → ℂ}
    (hg : ∀ u ∈ ball ((1/leftChordH (leftNome t) : ℝ) : ℂ)
      (1/leftChordH (leftNome t)-leftChordH (leftNome t)/2),
      HasDerivAt g (jacobiChordDifferential t a u) u) :
    (∫ y : ℝ in (-(1/(2*t)))..(1/(2*t)), jacobiArcDifferential t a y) =
      g ((leftChordH (leftNome t) : ℂ)-I*(leftChordK (leftNome t) : ℂ))-
      g ((leftChordH (leftNome t) : ℂ)+I*(leftChordK (leftNome t) : ℂ)) := by
  have hab : -(1/(2*t)) ≤ 1/(2*t) := le_trans (neg_nonpos.mpr (by positivity)) (by positivity)
  have hd (y : ℝ) (hy : y ∈ Icc (-(1/(2*t))) (1/(2*t))) :
      HasDerivAt (fun s : ℝ => g (leftPathU s)) (jacobiArcDifferential t a y) y := by
    have h := (hg _ (leftPathU_mem_jacobiChord_ball hy)).comp y (leftPathU_hasDerivAt y)
    rwa [← jacobiArcDifferential_chain ht ha0 ha1 hy] at h
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -(1/(2*t))) (b := 1/(2*t))
    (fun y hy => hd y (by simpa only [uIcc_of_le hab] using hy))
    ((jacobiArcDifferential_continuous ht ha0 ha1).intervalIntegrable _ _)
  rw [(leftPathU_endpoints t).1, (leftPathU_endpoints t).2] at hf
  exact hf

theorem jacobiChord_line_mem_ball {h k v : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hsq : h^2+k^2 = 1) (hv : v ∈ Icc (-k) k) :
    (h : ℂ)+I*(v : ℂ) ∈ ball ((1/h : ℝ) : ℂ) (1/h-h/2) := by
  apply jacobiChord_mem_ball hh hh1
  · simp
  · have hv2 : v^2 ≤ k^2 := by
      nlinarith [mul_nonneg (show 0 ≤ v+k by linarith [hv.1])
        (show 0 ≤ k-v by linarith [hv.2])]
    have hn := Complex.sq_norm ((h : ℂ)+I*(v : ℂ))
    simp only [normSq_apply, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im,
      I_re, I_im, zero_mul, mul_zero, one_mul, sub_self, add_zero, zero_add] at hn
    nlinarith [norm_nonneg ((h : ℂ)+I*(v : ℂ))]

theorem jacobiChordK_pos {q : ℝ} (hq : 0 < q) (hqu : q ≤ 1/3) : 0 < leftChordK q := by
  unfold leftChordK
  apply div_pos _ (by positivity)
  nlinarith

theorem jacobiChord_line_primitive_difference {t : ℝ} (ht : 0 < t)
    (hq : leftNome t ≤ 1/3) (a : ℝ) {g : ℂ → ℂ}
    (hg : ∀ u ∈ ball ((1/leftChordH (leftNome t) : ℝ) : ℂ)
      (1/leftChordH (leftNome t)-leftChordH (leftNome t)/2),
      HasDerivAt g (jacobiChordDifferential t a u) u) :
    (∫ v : ℝ in (-leftChordK (leftNome t))..(leftChordK (leftNome t)),
      I*jacobiChordDifferential t a ((leftChordH (leftNome t) : ℂ)+I*(v : ℂ))) =
      g ((leftChordH (leftNome t) : ℂ)+I*(leftChordK (leftNome t) : ℂ))-
      g ((leftChordH (leftNome t) : ℂ)-I*(leftChordK (leftNome t) : ℂ)) := by
  have hk := jacobiChordK_pos (leftNome_pos t) hq
  have hab : -leftChordK (leftNome t) ≤ leftChordK (leftNome t) := by linarith
  have hmem (v : ℝ) (hv : v ∈ Icc (-leftChordK (leftNome t)) (leftChordK (leftNome t))) :=
    jacobiChord_line_mem_ball (leftChordH_pos (leftNome_pos t)) (leftChordH_le_one _)
      (leftChordH_sq_add_K_sq _) hv
  have hd (v : ℝ) (hv : v ∈ Icc (-leftChordK (leftNome t)) (leftChordK (leftNome t))) :
      HasDerivAt (fun x : ℝ => g ((leftChordH (leftNome t) : ℂ)+I*(x : ℂ)))
        (I*jacobiChordDifferential t a ((leftChordH (leftNome t) : ℂ)+I*(v : ℂ))) v := by
    have harg := (((hasDerivAt_id v).ofReal_comp).const_mul I).const_add (leftChordH (leftNome t) : ℂ)
    have hd := (hg _ (hmem v hv)).comp v harg
    convert hd using 1
    · rfl
    · simp only [Complex.ofReal_one, mul_one]
      ring
  have hc : ContinuousOn (fun v : ℝ =>
      I*jacobiChordDifferential t a ((leftChordH (leftNome t) : ℂ)+I*(v : ℂ)))
      (Icc (-leftChordK (leftNome t)) (leftChordK (leftNome t))) := by
    apply continuousOn_const.mul
    exact (jacobiChordDifferential_differentiableOn ht hq a).continuousOn.comp
      (by fun_prop) hmem
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -leftChordK (leftNome t)) (b := leftChordK (leftNome t))
    (fun v hv => hd v (by simpa only [uIcc_of_le hab] using hv))
    (hc.intervalIntegrable_of_Icc hab)
  simpa only [Complex.ofReal_neg, mul_neg, ← sub_eq_add_neg] using hf

theorem horizontalPeriod_eq_jacobiChord_of_nome {t a : ℝ} (ht : 0 < t) (hq : leftNome t ≤ 1/3)
    (ha0 : 0 < a) (ha1 : a < 1) :
    thetaHorizontalPeriod t a =
      (∫ v : ℝ in (-leftChordK (leftNome t))..(leftChordK (leftNome t)),
        I*jacobiChordDifferential t a ((leftChordH (leftNome t) : ℂ)+I*(v : ℂ))).re := by
  obtain ⟨g,hg⟩ := jacobiChordDifferential_exact_ball ht hq a
  have hA := jacobiArc_primitive_difference ht ha0 ha1 hg
  have hB := jacobiChord_line_primitive_difference ht hq a hg
  rw [horizontalPeriod_eq_jacobiArc ht ha0 ha1, hA, hB, Complex.sub_re, Complex.sub_re]
  ring

theorem horizontalPeriod_eq_jacobiChord {t a : ℝ} (ht : 0 < t) (htu : t ≤ 17/20)
    (ha0 : 0 < a) (ha1 : a < 1) :
    thetaHorizontalPeriod t a =
      (∫ v : ℝ in (-leftChordK (leftNome t))..(leftChordK (leftNome t)),
        I*jacobiChordDifferential t a ((leftChordH (leftNome t) : ℂ)+I*(v : ℂ))).re :=
  horizontalPeriod_eq_jacobiChord_of_nome ht
    ((leftNome_lt_one_fifth ht htu).le.trans (by norm_num)) ha0 ha1

theorem horizontalPeriod_eq_jacobiChord_to_seven_fifths {t a : ℝ}
    (ht : 0 < t) (htu : t ≤ 7/5) (ha0 : 0 < a) (ha1 : a < 1) :
    thetaHorizontalPeriod t a =
      (∫ v : ℝ in (-leftChordK (leftNome t))..(leftChordK (leftNome t)),
        I*jacobiChordDifferential t a ((leftChordH (leftNome t) : ℂ)+I*(v : ℂ))).re :=
  horizontalPeriod_eq_jacobiChord_of_nome ht (leftNome_lt_one_third ht htu).le ha0 ha1

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.horizontalPeriod_eq_jacobiChord
