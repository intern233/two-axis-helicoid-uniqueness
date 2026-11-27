import TwoAxisHelicoid.OriginalSlopingPeriod

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped ComplexConjugate Interval

noncomputable def slopingIntegral (t : ℝ) (f : ℂ → ℂ) : ℂ :=
  ((1-I*t)/2)*(∫ s : ℝ in (-1)..1, f (originalPeriodPath t s))

theorem slopingIntegral_eq_wedge {t : ℝ} (ht : 0 < t) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (complexOpenRect (-2) 0 (-t) t)) :
    slopingIntegral t f =
      wedgeIntegral (originalPeriodPath t (-1)) (originalPeriodPath t 1) (f) := by
  let c := originalPeriodPath t (-1)
  let F := fun z => wedgeIntegral c z (f)
  have hhol := hf
  have hc : c ∈ complexOpenRect (-2) 0 (-t) t :=
    originalPeriodPath_mem_rectangle ht (by norm_num)
  have hF := holomorphic_rectangle_has_primitive hhol hc
  have hpath (s : ℝ) : HasDerivAt (originalPeriodPath t) ((1-I*t)/2) s := by
    convert ((((hasDerivAt_id s).ofReal_comp).mul_const (1-I*t)).div_const 2).const_add (-1:ℂ) using 1
    · rfl
    · simp
  have hmaps : MapsTo (originalPeriodPath t) (uIcc (-1:ℝ) 1) (complexOpenRect (-2) 0 (-t) t) := by
    intro s hs
    exact originalPeriodPath_mem_rectangle ht (by simpa only [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using hs)
  have hcont : ContinuousOn (fun s => f (originalPeriodPath t s)) (uIcc (-1:ℝ) 1) :=
    hhol.continuousOn.comp (by unfold originalPeriodPath; fun_prop) hmaps
  have hd (s : ℝ) (hs : s ∈ uIcc (-1:ℝ) 1) :
      HasDerivAt (fun s => F (originalPeriodPath t s))
        (((1-I*t)/2)*f (originalPeriodPath t s)) s := by
    convert (hF _ (hmaps hs)).comp s (hpath s) using 1
    · rfl
    · ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hcont.intervalIntegrable.const_mul ((1-I*t)/2))
  rw [intervalIntegral.integral_const_mul] at he
  simpa [slopingIntegral,F,c,wedgeIntegral] using he

theorem symmetric_function_vertical_integral_real (t x : ℝ) (f : ℂ → ℂ)
    (hconj : ∀ z, f (conj z) = conj (f z)) :
    (∫ y : ℝ in (t/2)..(-t/2), f ((x:ℂ)+y*I)).im = 0 := by
  let g := fun y : ℝ => f ((x:ℂ)+y*I)
  have hc (y : ℝ) : conj (g y) = g (-y) := by
    dsimp [g]
    rw [← hconj]
    congr 1
    simp
  have he : conj (∫ y : ℝ in (t/2)..(-t/2), g y) =
      ∫ y : ℝ in (t/2)..(-t/2), g y := by
    rw [← intervalIntegral.intervalIntegral_conj]
    simp_rw [hc]
    rw [intervalIntegral.integral_comp_neg]
    congr 1 <;> ring
  have hi := congrArg Complex.im he
  simp only [Complex.conj_im] at hi
  change (∫ y : ℝ in (t/2)..(-t/2), g y).im = 0
  linarith

theorem slopingIntegral_re_horizontal_segment {t : ℝ} (ht : 0 < t) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (complexOpenRect (-2) 0 (-t) t))
    (hconj : ∀ z, f (conj z) = conj (f z)) :
    (slopingIntegral t f).re =
      (∫ x : ℝ in (-3/2)..(-1/2), f ((x:ℂ)+I*((t/2:ℝ):ℂ))).re := by
  rw [slopingIntegral_eq_wedge ht f hf]
  have hm : (originalPeriodPath t (-1)).re = -3/2 ∧
      (originalPeriodPath t (-1)).im = t/2 := by
    norm_num [originalPeriodPath,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  have hp : (originalPeriodPath t 1).re = -1/2 ∧
      (originalPeriodPath t 1).im = -t/2 := by
    norm_num [originalPeriodPath,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  unfold wedgeIntegral
  rw [hm.1,hm.2,hp.1,hp.2]
  simp only [smul_eq_mul,Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_sub,symmetric_function_vertical_integral_real t _ f hconj,neg_zero,add_zero]
  congr 2
  funext x
  congr 1
  push_cast
  ring


theorem slopingIntegral_re_eq_half_horizontal {t : ℝ} (ht : 0 < t) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (complexOpenRect (-2) 0 (-t) t))
    (hconj : ∀ z, f (conj z) = conj (f z))
    (hperiod : ∀ z, f (z+(1+I*t)) = f z)
    (hcont : Continuous (fun x : ℝ => f ((x:ℂ)+I*((t/2:ℝ):ℂ)))) :
    (slopingIntegral t f).re = ((1/2:ℂ)*∫ x : ℝ in (-1)..1,
      f ((x:ℂ)+I*((t/2:ℝ):ℂ))).re := by
  let g := fun x : ℝ => f ((x:ℂ)+I*((t/2:ℝ):ℂ))
  have hp : Function.Periodic (fun x => (g x).re) 1 := by
    intro x
    have he : ((x+1:ℝ):ℂ)+I*((t/2:ℝ):ℂ) =
        conj ((x:ℂ)+I*((t/2:ℝ):ℂ))+(1+I*t) := by
      simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
      push_cast
      ring
    dsimp [g]
    rw [he,hperiod,hconj,Complex.conj_re]
  have hre (b c : ℝ) : (∫ x : ℝ in b..c, (g x).re) = (∫ x : ℝ in b..c, g x).re :=
    Complex.reCLM.intervalIntegral_comp_comm (hcont.intervalIntegrable b c)
  have he := hp.intervalIntegral_add_eq (-3/2) (-1)
  norm_num at he
  rw [hre,hre] at he
  have he2 := hp.intervalIntegral_add_eq (0) (-1)
  norm_num at he2
  rw [hre,hre] at he2
  have hs := congrArg Complex.re (intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (-1) 0 (μ := volume)) (hcont.intervalIntegrable 0 1 (μ := volume)))
  change (∫ x : ℝ in (-1)..0, g x).re+(∫ x : ℝ in 0..1, g x).re =
    (∫ x : ℝ in (-1)..1, g x).re at hs
  rw [slopingIntegral_re_horizontal_segment ht f hf hconj]
  change (∫ x : ℝ in (-3/2)..(-1/2), g x).re = ((1/2:ℂ)*∫ x : ℝ in (-1)..1, g x).re
  simp only [Complex.mul_re,Complex.div_ofNat_re,Complex.div_ofNat_im,
    Complex.one_re,Complex.one_im,zero_div,zero_mul,sub_zero]
  have he' : (∫ x : ℝ in (-3/2)..(-1/2), g x).re = (∫ x : ℝ in (-1)..0, g x).re := by
    simpa only [neg_div] using he
  linarith

end TwoAxisHelicoid
