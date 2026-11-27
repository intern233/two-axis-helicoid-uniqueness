import TwoAxisHelicoid.OriginalCoordinatePeriods

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped ComplexConjugate Interval
attribute [local irreducible] thetaZeta coordinateData thetaG

theorem originalPath_weierstrass_integrable {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable (fun s : ℝ =>
      (rhombicPeriodPair t ht).weierstrassP (originalPeriodPath t s)) volume (-1) 1 := by
  apply ContinuousOn.intervalIntegrable
  intro s hs
  have hz := rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht
    (by simpa only [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using hs))
  exact ((rhombicPeriodPair t ht).analyticOnNhd_weierstrassP _ hz).continuousAt.comp_continuousWithinAt
    (show ContinuousWithinAt (originalPeriodPath t) (uIcc (-1:ℝ) 1) s by
      unfold originalPeriodPath; fun_prop)

theorem originalPath_weierstrass_integral {t : ℝ} (ht : 0 < t) :
    ((1-I*t)/2)*(∫ s : ℝ in (-1)..1,
      (rhombicPeriodPair t ht).weierstrassP (originalPeriodPath t s)) =
      -thetaEtaExpression t*(1-I*t)-(Real.pi:ℂ)*I := by
  have hz (s : ℝ) (hs : s ∈ uIcc (-1:ℝ) 1) :=
    rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht
      (by simpa only [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using hs))
  have hd (s : ℝ) (hs : s ∈ uIcc (-1:ℝ) 1) :
      HasDerivAt (fun s => -thetaZeta t (originalPeriodPath t s))
        (((1-I*t)/2)*(rhombicPeriodPair t ht).weierstrassP (originalPeriodPath t s)) s := by
    have hpath : HasDerivAt (originalPeriodPath t) ((1-I*t)/2) s := by
      convert ((((hasDerivAt_id s).ofReal_comp).mul_const (1-I*t)).div_const 2).const_add (-1:ℂ) using 1
      · rfl
      · simp
    convert ((thetaZeta_hasDerivAt_of_pos ht ht (hz s hs)).comp s hpath).neg using 1
    · rfl
    · ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((originalPath_weierstrass_integrable ht).const_mul ((1-I*t)/2))
  rw [intervalIntegral.integral_const_mul] at he
  have hq := thetaZeta_add_half_of_pos ht ht (hz 1 (by norm_num))
  have harg : originalPeriodPath t 1+(1+I*t) = originalPeriodPath t (-1)+2 := by
    unfold originalPeriodPath
    push_cast
    ring
  rw [harg,thetaZeta_add_two] at hq
  rw [he]
  linear_combination hq

theorem originalCoordinatePeriod_height {t a c : ℝ} (ht : 0 < t) :
    originalCoordinatePeriod t a c ht 2 =
      I*c*(-(thetaEtaExpression t+(rhombicPeriodPair t ht).weierstrassP a)*(1-I*t)-
        (Real.pi:ℂ)*I) := by
  have hP := originalPath_weierstrass_integrable ht
  have hval (z : ℂ) : coordinateData t a c ht z 2 =
      I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a) := by
    unfold coordinateData
    rfl
  unfold originalCoordinatePeriod
  simp_rw [hval]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub hP intervalIntegrable_const]
  have he := originalPath_weierstrass_integral ht
  simp only [intervalIntegral.integral_const,Complex.real_smul] at *
  norm_num at *
  linear_combination I*(c:ℂ)*he

theorem originalCoordinatePeriod_height_re {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0:ℝ) 2) :
    (originalCoordinatePeriod t a c ht 2).re = -c*t*(thetaG t a).re := by
  rw [originalCoordinatePeriod_height ht,thetaG_eq_weierstrassP_of_pos ht ht a
    (real_not_mem_rhombic_lattice_of_pos ht ha.1 ha.2)]
  simp only [Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,
    Complex.add_re,Complex.add_im,Complex.neg_re,Complex.neg_im,Complex.I_re,
    Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im,
    thetaEtaExpression_real,rhombic_weierstrassP_real,zero_mul,mul_zero,one_mul,mul_one,
    zero_add,add_zero,sub_zero,zero_sub,neg_zero]
  field_simp [ht.ne']
  ring

theorem conjugateCoordinatePeriod_height {t a c : ℝ} (ht : 0 < t) :
    conjugateCoordinatePeriod t a c ht 2 = -conj (originalCoordinatePeriod t a c ht 2) := by
  unfold conjugateCoordinatePeriod originalCoordinatePeriod
  simp_rw [coordinateData_conj ht]
  change ((1+I*t)/2)*(∫ s : ℝ in (-1)..1, -conj (coordinateData t a c ht (originalPeriodPath t s) 2)) =
    -conj (((1-I*t)/2)*(∫ s : ℝ in (-1)..1, coordinateData t a c ht (originalPeriodPath t s) 2))
  simp only [intervalIntegral.integral_neg,intervalIntegral.intervalIntegral_conj,map_mul,map_div₀,
    map_sub,map_one,map_ofNat,Complex.conj_I,Complex.conj_ofReal,neg_mul,sub_neg_eq_add,mul_neg]

theorem original_all_generators_close_iff {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0:ℝ) 2) (hc : c ≠ 0) :
    (∀ j : Fin 3, (originalCoordinatePeriod t a c ht j).re = 0 ∧
      (conjugateCoordinatePeriod t a c ht j).re = 0) ↔
        thetaG t a = 0 ∧ thetaHorizontalPeriod t a = 0 := by
  have hheight : (originalCoordinatePeriod t a c ht 2).re = 0 ↔ thetaG t a = 0 := by
    rw [originalCoordinatePeriod_height_re ht ha]
    have hreal : (thetaG t a).re = 0 ↔ thetaG t a = 0 := by
      constructor
      · intro h
        exact Complex.ext h (thetaG_real t a)
      · intro h
        rw [h,Complex.zero_re]
    rw [mul_eq_zero]
    have hnt : -c*t ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hc) ht.ne'
    simp only [hnt,false_or,hreal]
  constructor
  · intro h
    exact ⟨hheight.mp (h 2).1,(original_horizontal_generators_close_iff ht hc).mp
      ⟨(h 0).1,(h 1).1,(h 0).2,(h 1).2⟩⟩
  · rintro ⟨hG,hH⟩ j
    have hh := (original_horizontal_generators_close_iff ht hc).mpr hH
    have hv := hheight.mpr hG
    fin_cases j
    · exact ⟨hh.1,hh.2.2.1⟩
    · exact ⟨hh.2.1,hh.2.2.2⟩
    · change (originalCoordinatePeriod t a c ht 2).re = 0 ∧
        (conjugateCoordinatePeriod t a c ht 2).re = 0
      rw [conjugateCoordinatePeriod_height ht]
      simpa only [Complex.neg_re,Complex.conj_re,hv,neg_zero] using And.intro hv (by rfl : (0:ℝ) = 0)

theorem existsUnique_original_closed_data_locally (c : ℝ) (hc : c ≠ 0) :
    ∃! p : ℝ × ℝ, ∃ ht : 0 < p.1,
      p.1 ∈ Ioo (rootTLower:ℝ) rootTUpper ∧ p.2 ∈ Ioo (0:ℝ) 1 ∧
      ∀ j : Fin 3, (originalCoordinatePeriod p.1 p.2 c ht j).re = 0 ∧
        (conjugateCoordinatePeriod p.1 p.2 c ht j).re = 0 := by
  obtain ⟨p,hp,hu⟩ := existsUnique_root_common_period_unit_strip
  have ht := root_t_positive hp.1.1.le
  have ha : p.2 ∈ Ioo (0:ℝ) 2 := ⟨hp.2.1.1,by linarith [hp.2.1.2]⟩
  refine ⟨p,⟨ht,hp.1,hp.2.1,(original_all_generators_close_iff ht ha hc).mpr hp.2.2⟩,?_⟩
  rintro q ⟨hqt,hq,haq,hclose⟩
  have haq2 : q.2 ∈ Ioo (0:ℝ) 2 := ⟨haq.1,by linarith [haq.2]⟩
  exact hu q ⟨hq,haq,(original_all_generators_close_iff hqt haq2 hc).mp hclose⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.original_all_generators_close_iff
#print axioms TwoAxisHelicoid.existsUnique_original_closed_data_locally
