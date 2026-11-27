import TwoAxisHelicoid.RightAnalyticGerms
import TwoAxisHelicoid.EvenAnalyticSquare
import TwoAxisHelicoid.RightEndpointTheorem
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology
attribute [local irreducible] verticalA actualPeriodAlong

theorem exists_actualPeriodAlong_right_analytic_extension : ∃ P : ℝ → ℝ,
    AnalyticAt ℝ P ellipticVerticalUpper ∧
    P ellipticVerticalUpper = -Real.pi/ellipticVerticalUpper ∧
    P =ᶠ[𝓝[<] ellipticVerticalUpper] actualPeriodAlong := by
  obtain ⟨f,g,hf,hg,hf0,hg0,hfe,hge,halign⟩ := exists_right_even_analytic_germs
  obtain ⟨F,hF,hfF⟩ := even_analytic_factor_square hf hfe
  obtain ⟨G,hG,hgG⟩ := even_analytic_factor_square hg hge
  let T := ellipticVerticalUpper
  let x : ℝ → ℝ := fun t => verticalA t-1
  let y : ℝ → ℝ := fun t => x t^2
  have hF0 : F 0 = T := by
    have hh := hfF.self_of_nhds
    simpa only [zero_pow (by decide : 2 ≠ 0),hf0] using hh.symm
  have hG0 : G 0 = -Real.pi/T := by
    have hh := hgG.self_of_nhds
    simpa only [zero_pow (by decide : 2 ≠ 0),hg0] using hh.symm
  have hx : Tendsto x (𝓝[<] T) (𝓝 0) := by
    simpa only [sub_self] using verticalA_tendsto_one.sub_const 1
  have hy : Tendsto y (𝓝[<] T) (𝓝 0) := by simpa only [zero_pow (by decide : 2 ≠ 0)] using hx.pow 2
  have hyne : Tendsto y (𝓝[<] T) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hy,?_⟩
    filter_upwards [verticalDomain_eventually_left] with t ht
    exact pow_ne_zero 2 (sub_ne_zero.mpr (verticalA_spec ht).1.2.ne)
  have hFA : ∀ᶠ t : ℝ in 𝓝[<] T, F (y t) = t ∧ G (y t) = actualPeriodAlong t := by
    filter_upwards [halign,hx.eventually hfF,hx.eventually hgG] with t ht hft hgt
    exact ⟨hft.symm.trans ht.1,hgt.symm.trans ht.2⟩
  have hFs : Tendsto (fun t : ℝ => (F (y t)-T)/y t) (𝓝[<] T) (𝓝 (deriv F 0)) := by
    have hh := hF.differentiableAt.hasDerivAt.tendsto_slope.comp hyne
    simpa only [Function.comp_def,slope_fun_def_field,sub_zero,hF0] using hh
  have hxs : Tendsto (fun t : ℝ => x t^2/(T-t)) (𝓝[<] T) (𝓝 (1/Real.pi)) := by
    simpa only [x,sub_sq_comm] using verticalA_square_gap_limit
  have hn : (1/Real.pi:ℝ) ≠ 0 := one_div_ne_zero Real.pi_ne_zero
  have hi : Tendsto (fun t : ℝ => -((x t^2/(T-t))⁻¹)) (𝓝[<] T) (𝓝 (-Real.pi)) := by
    simpa only [one_div,inv_inv] using (hxs.inv₀ hn).neg
  have his : Tendsto (fun t : ℝ => (F (y t)-T)/y t) (𝓝[<] T) (𝓝 (-Real.pi)) := by
    apply hi.congr'
    filter_upwards [hFA] with t ht
    rw [ht.1,inv_div]
    change -((T-t)/x t^2) = (t-T)/x t^2
    ring
  have hFd : deriv F 0 = -Real.pi := tendsto_nhds_unique hFs his
  have hFn : deriv F 0 ≠ 0 := by rw [hFd]; exact neg_ne_zero.mpr Real.pi_ne_zero
  let J := hF.hasStrictDerivAt.localInverse F (deriv F 0) 0 hFn
  have hJ : AnalyticAt ℝ J T := by simpa only [hF0] using hF.analyticAt_localInverse hFn
  have hleft : ∀ᶠ s in 𝓝 (0:ℝ), J (F s) = s := hF.hasStrictDerivAt.eventually_left_inverse hFn
  have hJ0 : J T = 0 := by simpa only [hF0] using hleft.self_of_nhds
  have hP : AnalyticAt ℝ (fun t => G (J t)) T := by
    have hgJ : AnalyticAt ℝ G (J T) := by rw [hJ0]; exact hG
    exact hgJ.comp (f := J) (x := T) hJ
  refine ⟨fun t => G (J t),hP,?_,?_⟩
  · change G (J T) = -Real.pi/T
    rw [hJ0,hG0]
  filter_upwards [hFA,hy.eventually hleft] with t ht hj
  rw [ht.1] at hj
  rw [hj,ht.2]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exists_actualPeriodAlong_right_analytic_extension
