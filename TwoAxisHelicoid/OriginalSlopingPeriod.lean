import TwoAxisHelicoid.RectanglePrimitive
import TwoAxisHelicoid.AllHorizontalRegularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped ComplexConjugate Interval
attribute [local irreducible] thetaA

noncomputable def originalPeriodPath (t s : ℝ) : ℂ := -1+(s:ℂ)*(1-I*t)/2

noncomputable def originalSlopingPeriod (t a : ℝ) : ℂ :=
  ((1-I*t)/2)*(∫ s : ℝ in (-1)..1, thetaA t a (originalPeriodPath t s))

theorem rhombic_open_rectangle_not_mem {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ complexOpenRect (-2) 0 (-t) t) :
    z ∉ (rhombicPeriodPair t ht).lattice := by
  intro hl
  obtain ⟨m,n,hr,hi⟩ := (rhombic_mem_lattice_iff ht z).mp hl
  have hn0 : (-1:ℤ) < n := by
    exact_mod_cast (show (-1:ℝ) < n by nlinarith [hz.2.1])
  have hn1 : n < (1:ℤ) := by
    exact_mod_cast (show (n:ℝ) < 1 by nlinarith [hz.2.2])
  have hn : n = 0 := by omega
  simp only [hn,Int.cast_zero,add_zero] at hr
  have hm0 : (-1:ℤ) < m := by exact_mod_cast (show (-1:ℝ) < m by linarith [hz.1.1])
  have hm1 : m < (0:ℤ) := by exact_mod_cast (show (m:ℝ) < 0 by linarith [hz.1.2])
  omega

theorem originalPeriodPath_mem_rectangle {t : ℝ} (ht : 0 < t) {s : ℝ}
    (hs : s ∈ Icc (-1:ℝ) 1) :
    originalPeriodPath t s ∈ complexOpenRect (-2) 0 (-t) t := by
  simp only [originalPeriodPath,complexOpenRect,mem_ofPred_eq,mem_Ioo,
    Complex.add_re,Complex.add_im,Complex.neg_re,Complex.neg_im,Complex.one_re,
    Complex.one_im,Complex.div_ofNat_re,Complex.div_ofNat_im,Complex.mul_re,
    Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,one_mul,zero_add,
    add_zero,sub_zero,neg_zero,zero_sub]
  constructor <;> constructor <;> nlinarith [hs.1,hs.2]

theorem thetaA_holomorphic_original_rectangle {t : ℝ} (ht : 0 < t) (a : ℝ) :
    DifferentiableOn ℂ (thetaA t a) (complexOpenRect (-2) 0 (-t) t) := by
  intro z hz
  have hreg := mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht z).mp
    (rhombic_open_rectangle_not_mem ht hz)
  exact (thetaA_differentiableAt ht a hreg).differentiableWithinAt

theorem originalSlopingPeriod_eq_wedge {t : ℝ} (ht : 0 < t) (a : ℝ) :
    originalSlopingPeriod t a =
      wedgeIntegral (originalPeriodPath t (-1)) (originalPeriodPath t 1) (thetaA t a) := by
  let c := originalPeriodPath t (-1)
  let F := fun z => wedgeIntegral c z (thetaA t a)
  have hhol := thetaA_holomorphic_original_rectangle ht a
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
  have hcont : ContinuousOn (fun s => thetaA t a (originalPeriodPath t s)) (uIcc (-1:ℝ) 1) :=
    hhol.continuousOn.comp (by unfold originalPeriodPath; fun_prop) hmaps
  have hd (s : ℝ) (hs : s ∈ uIcc (-1:ℝ) 1) :
      HasDerivAt (fun s => F (originalPeriodPath t s))
        (((1-I*t)/2)*thetaA t a (originalPeriodPath t s)) s := by
    convert (hF _ (hmaps hs)).comp s (hpath s) using 1
    · rfl
    · ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hcont.intervalIntegrable.const_mul ((1-I*t)/2))
  rw [intervalIntegral.integral_const_mul] at he
  simpa [originalSlopingPeriod,F,c,wedgeIntegral] using he

theorem symmetric_vertical_integral_real (t a x : ℝ) :
    (∫ y : ℝ in (t/2)..(-t/2), thetaA t a ((x:ℂ)+y*I)).im = 0 := by
  let f := fun y : ℝ => thetaA t a ((x:ℂ)+y*I)
  have hc (y : ℝ) : conj (f y) = f (-y) := by
    dsimp [f]
    rw [← thetaA_conj]
    congr 1
    simp
  have he : conj (∫ y : ℝ in (t/2)..(-t/2), f y) =
      ∫ y : ℝ in (t/2)..(-t/2), f y := by
    rw [← intervalIntegral.intervalIntegral_conj]
    simp_rw [hc]
    rw [intervalIntegral.integral_comp_neg]
    congr 1 <;> ring
  have hi := congrArg Complex.im he
  simp only [Complex.conj_im] at hi
  change (∫ y : ℝ in (t/2)..(-t/2), f y).im = 0
  linarith

theorem originalSlopingPeriod_re_horizontal_segment {t : ℝ} (ht : 0 < t) (a : ℝ) :
    (originalSlopingPeriod t a).re =
      (∫ x : ℝ in (-3/2)..(-1/2), thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ))).re := by
  rw [originalSlopingPeriod_eq_wedge ht a]
  have hm : (originalPeriodPath t (-1)).re = -3/2 ∧
      (originalPeriodPath t (-1)).im = t/2 := by
    norm_num [originalPeriodPath,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  have hp : (originalPeriodPath t 1).re = -1/2 ∧
      (originalPeriodPath t 1).im = -t/2 := by
    norm_num [originalPeriodPath,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  unfold wedgeIntegral
  rw [hm.1,hm.2,hp.1,hp.2]
  simp only [smul_eq_mul,Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_sub,symmetric_vertical_integral_real,neg_zero,add_zero]
  congr 2
  funext x
  congr 1
  push_cast
  ring

theorem originalSlopingPeriod_re_eq_horizontal {t : ℝ} (ht : 0 < t) (a : ℝ) :
    (originalSlopingPeriod t a).re = thetaHorizontalPeriod t a := by
  rw [originalSlopingPeriod_re_horizontal_segment ht a,horizontal_period_half ht a]
  have hc := horizontal_integrand_continuous ht a
  let f := fun x : ℝ => (thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ))).re
  have hp : Function.Periodic f 1 := by
    intro x
    dsimp [f]
    rw [thetaA_midline_add_one ht a]
    rfl
  have he := hp.intervalIntegral_add_eq (-3/2) (-1)
  norm_num at he
  dsimp only [f] at he
  have hre (b c : ℝ) :
      (∫ x : ℝ in b..c, (thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ))).re) =
      (∫ x : ℝ in b..c, thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ))).re :=
    Complex.reCLM.intervalIntegral_comp_comm (hc.intervalIntegrable b c)
  rw [hre,hre] at he
  simpa only [neg_div] using he

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.originalSlopingPeriod_re_eq_horizontal
