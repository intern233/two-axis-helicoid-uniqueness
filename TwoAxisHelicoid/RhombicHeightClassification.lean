import TwoAxisHelicoid.EllipticRealNormalization
import TwoAxisHelicoid.AllHeightPeriods
import TwoAxisHelicoid.WeierstrassAllMonotone

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology ComplexConjugate
set_option maxHeartbeats 1200000

/-- The height coefficient is forced into the explicit normalized form by
its one double pole, reflection symmetry, genuine lattice periodicity and
the zero real period on the sloping generator. -/
theorem rhombic_height_coefficient_classification {t : ℝ} (ht : 0 < t)
    {f g : ℂ → ℂ} {A : ℂ} (hA : A ≠ 0)
    (hf : ∀ z ∉ (rhombicPeriodPair t ht).lattice, DifferentiableAt ℂ f z)
    (hp : ∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice → f (z+ω)=f z)
    (hg : AnalyticAt ℂ g 0)
    (hloc : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → f z=A/z^2+g z)
    (hconj : ∀ z ∉ (rhombicPeriodPair t ht).lattice, f (conj z)= -conj (f z))
    (hP : (ellipticLinePeriod f (-1) (1+I*t)).re=0) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      f z=I*c*((rhombicPeriodPair t ht).weierstrassP z-
        ((Real.pi/t-(thetaEtaExpression t).re : ℝ) : ℂ)) := by
  have hform := elliptic_double_pole_classification (rhombicPeriodPair t ht) A hf hp hg hloc
  have hr (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      A.re*((rhombicPeriodPair t ht).weierstrassP x).re+(g 0).re=0 := by
    have hn := real_not_mem_rhombic_lattice_of_pos ht hx.1 (by linarith [hx.2] : x < 2)
    have he := congrArg Complex.re (hconj x hn)
    rw [Complex.conj_ofReal,Complex.neg_re,Complex.conj_re] at he
    have hz : (f x).re=0 := by linarith
    rw [hform x hn,Complex.add_re,Complex.mul_re,rhombic_weierstrassP_real ht x,mul_zero,sub_zero] at hz
    exact hz
  have hr₁ := hr (1/4) (by norm_num)
  have hr₂ := hr (1/2) (by norm_num)
  have hwp := rhombic_weierstrassP_strictAnti_of_pos ht ht
    (show (1/4 : ℝ) ∈ Ioo 0 1 by norm_num) (show (1/2 : ℝ) ∈ Ioo 0 1 by norm_num)
    (by norm_num : (1/4 : ℝ) < 1/2)
  have hprod : A.re*(((rhombicPeriodPair t ht).weierstrassP ((1/4 : ℝ) : ℂ)).re-
      ((rhombicPeriodPair t ht).weierstrassP ((1/2 : ℝ) : ℂ)).re)=0 := by
    linear_combination hr₁-hr₂
  have hAr : A.re=0 := (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr (ne_of_gt hwp))
  have hBr : (g 0).re=0 := by rw [hAr,zero_mul,zero_add] at hr₁; exact hr₁
  have hAe : A=I*(A.im : ℂ) := by apply Complex.ext <;> simp [hAr]
  have hBe : g 0=I*((g 0).im : ℂ) := by apply Complex.ext <;> simp [hBr]
  have hc : A.im ≠ 0 := by intro h; apply hA; rw [hAe,h]; simp
  let u : ℝ := -(g 0).im/A.im
  have huform (z : ℂ) (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
      f z=I*(A.im : ℂ)*((rhombicPeriodPair t ht).weierstrassP z-(u : ℂ)) := by
    rw [hform z hz,hAe,hBe]
    dsimp [u]
    push_cast
    simp only [Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,one_mul,zero_add]
    field_simp [Complex.ofReal_ne_zero.mpr hc]
    ring
  have hperiod : ellipticLinePeriod f (-1) (1+I*t)=heightPeriodHalf t ht A.im u := by
    unfold ellipticLinePeriod heightPeriodHalf heightLineIntegral
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [huform _ (rhombic_sloping_line_not_mem ht s)]
  have hu : u=Real.pi/t-(thetaEtaExpression t).re :=
    (height_periods_close_iff_of_pos ht ht hc u).mp
      ⟨heightPeriodTwo_re_zero_of_pos ht ht A.im u,by rw [← hperiod]; exact hP⟩
  refine ⟨A.im,hc,?_⟩
  intro z hz
  rw [huform z hz,hu]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rhombic_height_coefficient_classification
