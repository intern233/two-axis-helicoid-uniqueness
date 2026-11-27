import TwoAxisHelicoid.PhysicalLevelThetaPhase
import TwoAxisHelicoid.GaussPeriodicity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace TwoAxisHelicoid
open Complex Set

/-- Throughout the low slab, the physical phase lies within a cone
of slope one quarter. The two endpoint projections therefore control
the true first spatial component of every horizontal tangent. -/
theorem low_slab_gauss_imag_negative {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (low : 29/50≤a)
    (root : thetaG t a=0) {z : ℂ} :
    let F := centralPhaseThetaRatio t a z
    let H := actualComplexHeight t a 1 ht z
    |H.re|≤1/4 →
      ((∀ q : ℝ, |q|≤1 → 4*F.re+q*F.im<0) ∨ (H.re≤0 ∧ F.re<0 ∧ 0≤F.im)) →
        (thetaGauss t a 1 z).im<0 := by
  intro F H height hypotheses
  let θ := 2*(a-1)*H.re
  have slope : |2*(a-1)|≤21/25 := abs_le.mpr ⟨by linarith,by linarith [ha.2]⟩
  have phase : |θ|≤21/100 := by
    rw [show |θ|=|2*(a-1)| * |H.re| from abs_mul ..]
    calc
      _ ≤ (21/25:ℝ)*(1/4) := mul_le_mul slope height (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have si : |Real.sin θ|≤21/100 := Real.abs_sin_le_abs.trans phase
  have sq : θ^2≤(21/100:ℝ)^2 := by
    rw [← sq_abs θ]
    exact pow_le_pow_left₀ (abs_nonneg θ) phase 2
  have co : 9/10≤Real.cos θ := by nlinarith [Real.one_sub_sq_div_two_le_cos (x:=θ)]
  have cp : 0<Real.cos θ := lt_of_lt_of_le (by norm_num) co
  let b := Real.exp (-(2*(a-1))*H.im)
  have form : (thetaGauss t a 1 z).im=b*(Real.cos θ*F.re-Real.sin θ*F.im) := by
    have v := physical_level_gauss_theta_ratio ht ha root z
    change thetaGauss t a 1 z=I*exp (I*(θ:ℂ))*(b:ℂ)*F at v
    rw [v,mul_comm I (θ:ℂ)]
    simp [Complex.mul_re,Complex.mul_im,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]
    ring
  rw [form]
  apply mul_neg_of_pos_of_neg (Real.exp_pos _)
  rcases hypotheses with cone|⟨hh,fr,fi⟩
  · let q := -4*Real.sin θ/Real.cos θ
    have qin : |q|≤1 := by
      rw [show |q|=4*|Real.sin θ|/Real.cos θ by dsimp [q]; rw [abs_div,abs_mul,abs_of_pos cp]; norm_num]
      apply (div_le_iff₀ cp).mpr
      linarith
    have algebra : Real.cos θ*F.re-Real.sin θ*F.im=(Real.cos θ/4)*(4*F.re+q*F.im) := by
      dsimp [q]
      field_simp [cp.ne']
      ring
    rw [algebra]
    exact mul_neg_of_pos_of_neg (div_pos cp (by norm_num)) (cone q qin)
  · have th : 0≤θ := mul_nonneg_of_nonpos_of_nonpos (by linarith [ha.2]) hh
    have sn := Real.sin_nonneg_of_nonneg_of_le_pi th (by linarith [(abs_le.mp phase).2,Real.pi_gt_three])
    linarith [mul_neg_of_pos_of_neg cp fr,mul_nonneg sn fi]

/-- The half-period turn preserves the sign of the imaginary component
of the Gauss map. -/
theorem quarter_gauss_halfturn_imag {t a : ℝ} (lower : 43/50≤t) (ht : 0<t) {z : ℂ} (hy : z.im∈Ioo 0 t) :
    (thetaGauss t a 1 (-z+(1+I*t))).im<0 ↔ (thetaGauss t a 1 z).im<0 := by
  let L := rhombicPeriodPair t ht
  have off := rhombic_horizontal_strip_not_mem (z:=z) ht hy
  have m : z-a∉L.lattice := rhombic_horizontal_strip_not_mem ht (by change (z-a).im∈Ioo 0 t; simpa using hy)
  have p : z+a∉L.lattice := rhombic_horizontal_strip_not_mem ht (by change (z+a).im∈Ioo 0 t; simpa using hy)
  rw [thetaGauss_period_half lower ht 1 (by simpa using off)]
  let g := thetaGauss t a 1 z
  have gn : g≠0 := thetaGauss_ne_zero ht a 1 m p
  have eq : thetaGauss t a 1 (-z)= -1/g :=
    (eq_div_iff gn).mpr (thetaGauss_neg_product ht a 1 m p)
  rw [eq,neg_div,one_div,neg_im,inv_im,neg_div,neg_neg]
  rw [div_lt_iff₀ (normSq_pos.mpr gn),zero_mul]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.low_slab_gauss_imag_negative
#print axioms TwoAxisHelicoid.quarter_gauss_halfturn_imag
