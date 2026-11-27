import TwoAxisHelicoid.RightAnalyticGerms
import TwoAxisHelicoid.EvenScaledRemainder
import TwoAxisHelicoid.RightEndpointTheorem

namespace TwoAxisHelicoid
open Set Filter Asymptotics
open scoped Topology
attribute [local irreducible] verticalA actualPeriodAlong

theorem right_second_order_remainder_limits : ∃ r q : ℝ,
    Tendsto (fun t : ℝ => ((1-verticalA t)^2-(ellipticVerticalUpper-t)/Real.pi)/
      (ellipticVerticalUpper-t)^2) (𝓝[<] ellipticVerticalUpper) (𝓝 r) ∧
    Tendsto (fun t : ℝ => (actualPeriodAlong t+Real.pi/ellipticVerticalUpper-
      (-deriv ellipticFReal ellipticVerticalUpper+
        ellipticI ellipticVerticalUpper ellipticVerticalUpper_pos/Real.pi)*(t-ellipticVerticalUpper))/
      (ellipticVerticalUpper-t)^2) (𝓝[<] ellipticVerticalUpper) (𝓝 q) := by
  obtain ⟨f,g,hf,hg,hf0,hg0,hfe,hge,halign⟩ := exists_right_even_analytic_germs
  let T := ellipticVerticalUpper
  let D := -deriv ellipticFReal T+ellipticI T ellipticVerticalUpper_pos/Real.pi
  let x : ℝ → ℝ := fun t => verticalA t-1
  let d : ℝ → ℝ := fun t => T-t
  have hx : Tendsto x (𝓝[<] T) (𝓝 0) := by
    simpa only [sub_self] using verticalA_tendsto_one.sub_const 1
  have hk : Tendsto (fun t => x t^2/d t) (𝓝[<] T) (𝓝 (1/Real.pi)) := by
    simpa only [x,d,sub_sq_comm] using verticalA_square_gap_limit
  have hkn : (1/Real.pi:ℝ) ≠ 0 := one_div_ne_zero Real.pi_ne_zero
  have hdn : ∀ᶠ t in 𝓝[<] T, d t ≠ 0 := by
    filter_upwards [verticalDomain_eventually_left] with t ht
    exact (sub_pos.mpr ht.2).ne'
  have hs : Tendsto (fun t => (f (x t)-f 0)/d t) (𝓝[<] T) (𝓝 (-1:ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [halign,hdn] with t ht hd
    rw [hf0,ht.1]
    dsimp only [d,T] at hd ⊢
    field_simp
    ring
  have hsG : Tendsto (fun t => (g (x t)-g 0)/d t) (𝓝[<] T) (𝓝 (-D)) := by
    apply actualPeriodAlong_right_slope.neg.congr'
    filter_upwards [halign,hdn] with t ht hd
    rw [hg0,ht.2]
    dsimp only [d,T] at hd ⊢
    rw [show t-ellipticVerticalUpper = -(ellipticVerticalUpper-t) by ring,div_neg]
    ring
  obtain ⟨rf,hrf⟩ := even_analytic_scaled_remainder hf hfe hx hk hkn hdn hs
  obtain ⟨rg,hrg⟩ := even_analytic_scaled_remainder hg hge hx hk hkn hdn hsG
  have hfLim : Tendsto (fun t => (t-T+Real.pi*x t^2)/d t^2) (𝓝[<] T) (𝓝 rf) := by
    apply hrf.congr'
    filter_upwards [halign] with t ht
    rw [hf0,ht.1]
    dsimp only [T]
    field_simp
    ring
  have hgLim : Tendsto (fun t => (actualPeriodAlong t+Real.pi/T+Real.pi*D*x t^2)/d t^2)
      (𝓝[<] T) (𝓝 rg) := by
    apply hrg.congr'
    filter_upwards [halign] with t ht
    rw [hg0,ht.2]
    dsimp only [T]
    field_simp
    ring
  refine ⟨rf/Real.pi,rg-D*rf,?_,?_⟩
  · apply (hfLim.div_const Real.pi).congr'
    filter_upwards [hdn] with t hd
    dsimp only [d,x,T] at hd ⊢
    field_simp
    ring
  · apply (hgLim.sub (hfLim.const_mul D)).congr'
    filter_upwards [hdn] with t hd
    dsimp only [d,T] at hd ⊢
    change (actualPeriodAlong t+Real.pi/ellipticVerticalUpper+Real.pi*D*x t^2)/
      (ellipticVerticalUpper-t)^2-D*((t-ellipticVerticalUpper+Real.pi*x t^2)/
      (ellipticVerticalUpper-t)^2) =
      (actualPeriodAlong t+Real.pi/ellipticVerticalUpper-D*(t-ellipticVerticalUpper))/
      (ellipticVerticalUpper-t)^2
    ring

theorem verticalA_square_right_remainder_isBigO :
    (fun t : ℝ => (1-verticalA t)^2-(ellipticVerticalUpper-t)/Real.pi) =O[𝓝[<] ellipticVerticalUpper]
      (fun t => (ellipticVerticalUpper-t)^2) := by
  obtain ⟨r,q,hr,_hq⟩ := right_second_order_remainder_limits
  apply isBigO_of_div_tendsto_nhds _ r hr
  filter_upwards [verticalDomain_eventually_left] with t ht
  exact fun he => False.elim ((pow_ne_zero 2 (sub_pos.mpr ht.2).ne') he)

theorem actualPeriodAlong_right_remainder_isBigO :
    (fun t : ℝ => actualPeriodAlong t+Real.pi/ellipticVerticalUpper-
      (-deriv ellipticFReal ellipticVerticalUpper+
        ellipticI ellipticVerticalUpper ellipticVerticalUpper_pos/Real.pi)*(t-ellipticVerticalUpper))
      =O[𝓝[<] ellipticVerticalUpper] (fun t => (ellipticVerticalUpper-t)^2) := by
  obtain ⟨r,q,_hr,hq⟩ := right_second_order_remainder_limits
  apply isBigO_of_div_tendsto_nhds _ q hq
  filter_upwards [verticalDomain_eventually_left] with t ht
  exact fun he => False.elim ((pow_ne_zero 2 (sub_pos.mpr ht.2).ne') he)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.verticalA_square_right_remainder_isBigO
#print axioms TwoAxisHelicoid.actualPeriodAlong_right_remainder_isBigO
