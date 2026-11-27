import TwoAxisHelicoid.LeftComparisonLower

namespace TwoAxisHelicoid
open Set MeasureTheory

/-- The four estimates on the actual integration window in Section 7,
including the intermediate identity for the numerator of the kernel. -/
theorem actual_left_chord_window_estimates {t ξ : ℝ} (ht : 0<t) (htu : t≤1/8)
    (window : ξ ∈ Icc (1/(2*leftKappa t)) (2/leftKappa t)) :
    let κ := leftKappa t
    let h := leftChordH (leftNome t)
    let k := leftChordK (leftNome t)
    let v := -1+ξ
    h^2≤ξ/4 ∧ k^2-v^2=2*ξ-ξ^2-h^2 ∧ (3/2)*ξ≤k^2-v^2 ∧
      h^2+(v-1)^2≤4 ∧ 9/10≤Real.cos (κ*h) := by
  let κ := leftKappa t
  let h := leftChordH (leftNome t)
  let k := leftChordK (leftNome t)
  obtain ⟨hh,hk,hsq,hκh⟩ := actual_left_chord_parameters ht htu
  have high := leftKappa_gt ht htu
  have hκ : 0<κ := lt_trans (by norm_num : (0:ℝ)<25/2) high
  have par := left_chord_parameter_estimates high hh hk hsq hκh
  have win := left_chord_subinterval_estimates (v := -1+ξ) high par.2.2.1
    (add_le_add (le_refl (-1 : ℝ)) window.1) (add_le_add (le_refl (-1 : ℝ)) window.2)
  rw [show -1+ξ+1=ξ by ring] at win
  obtain ⟨pos,upper,small⟩ := win
  have sq : ξ^2≤ξ/4 := by nlinarith [mul_nonneg pos.le (sub_nonneg.mpr upper)]
  change h^2+k^2=1 at hsq
  change h^2≤ξ/4 at small
  change h^2≤ξ/4 ∧ k^2-(-1+ξ)^2=2*ξ-ξ^2-h^2 ∧ (3/2)*ξ≤k^2-(-1+ξ)^2 ∧
    h^2+(-1+ξ-1)^2≤4 ∧ 9/10≤Real.cos (κ*h)
  exact ⟨small,by nlinarith,by nlinarith,by nlinarith,
    (left_chord_trig_bounds (mul_pos hκ hh).le hκh).1⟩

/-- Lower bound for the actual comparison period before replacing the
positive weight by a constant. The integral retains both printed
endpoints after the translation ξ=v+1. -/
theorem leftComparisonPeriod_weighted_integral_lower {t : ℝ} (ht : 0<t) (htu : t≤1/8) :
    let κ := leftKappa t
    (Real.pi*Real.exp κ/(2*t))*(27/80)*(∫ ξ : ℝ in (1/(2*κ))..(2/κ), ξ*Real.exp (-κ*ξ))
      ≤leftComparisonPeriod t := by
  let κ := leftKappa t
  let h := leftChordH (leftNome t)
  let k := leftChordK (leftNome t)
  let a := 1/(2*κ)
  let b := 2/κ
  let W (ξ : ℝ) := ξ*Real.exp (-κ*ξ)
  let c := Real.exp κ*(27/80)
  obtain ⟨hh,hk,hsq,hκh⟩ := actual_left_chord_parameters ht htu
  have high := leftKappa_gt ht htu
  have hκ : 0<κ := lt_trans (by norm_num : (0:ℝ)<25/2) high
  have par := left_chord_parameter_estimates high hh hk hsq hκh
  have ab : a≤b := (div_le_div_iff₀ (show 0<2*κ by positivity) hκ).mpr (by linarith)
  have order : -1+a ≤ -1+b := add_le_add (le_refl (-1 : ℝ)) ab
  have cc := leftChordRealKernel_continuous hh.ne' κ
  have wc : Continuous (fun v : ℝ => c*W (v+1)) := by dsimp only [W]; fun_prop
  have point (v : ℝ) (hv : v∈Icc (-1+a) (-1+b)) : c*W (v+1)≤leftChordRealKernel κ h v := by
    obtain ⟨p,u,bound⟩ := left_chord_subinterval_estimates high par.2.2.1 hv.1 hv.2
    obtain ⟨co,si⟩ := left_chord_trig_bounds (mul_pos hκ hh).le hκh
    have ratio := left_chord_ratio_lower hh p u bound co si
    rw [show -1+(v+1)=v by ring] at ratio
    calc
      c*W (v+1) = Real.exp (-κ*v)*((27/80)*(v+1)) := by
        rw [show -κ*v=κ+(-κ*(v+1)) by ring,Real.exp_add]
        dsimp only [c,W]
        ring
      _ ≤ leftChordRealKernel κ h v := mul_le_mul_of_nonneg_left ratio (Real.exp_pos _).le
  have sub := intervalIntegral.integral_mono_on (μ := volume) order
    (wc.intervalIntegrable _ _) (cc.intervalIntegrable _ _) point
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_add_right W 1,
    show -1+a+1=a by ring,show -1+b+1=b by ring] at sub
  have nonneg : 0≤ᵐ[volume.restrict (Ioc (-k) k)] leftChordRealKernel κ h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact leftChordRealKernel_nonneg (mul_pos hκ hh).le hκh hh.le hsq ⟨hv.1.le,hv.2⟩
  have whole := intervalIntegral.integral_mono_interval par.2.2.2.1 order par.2.2.2.2 nonneg
    (cc.intervalIntegrable (-k) k)
  calc
    _ = (Real.pi/(2*t))*(c*(∫ ξ in a..b, W ξ)) := by dsimp only [a,b,W,c,κ]; ring
    _ ≤ (Real.pi/(2*t))*(∫ v in (-k)..k, leftChordRealKernel κ h v) :=
      mul_le_mul_of_nonneg_left (sub.trans whole) (by positivity)
    _ = leftComparisonPeriod t := (leftComparisonPeriod_eq_chord ht).symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_left_chord_window_estimates
#print axioms TwoAxisHelicoid.leftComparisonPeriod_weighted_integral_lower
