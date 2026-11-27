import TwoAxisHelicoid.WeierstrassRotation

namespace TwoAxisHelicoid
open Complex Filter
open scoped Topology

theorem weierstrass_primitive_reparametrization {X : ℂ → Fin 3 → ℝ}
    {K : ℂ → ℂ} {ξ d g h : ℂ}
    (hX : HasFDerivAt X (nullRealDerivative (weierstrassTriple g h)) (K ξ))
    (hK : HasDerivAt K d ξ) :
    HasFDerivAt (fun ξ => X (K ξ)) (nullRealDerivative (weierstrassTriple g (d*h))) ξ := by
  have hd := hX.comp ξ (hK.hasFDerivAt.restrictScalars ℝ)
  have he : (nullRealDerivative (weierstrassTriple g h)).comp
      ((ContinuousLinearMap.toSpanSingleton ℂ d).restrictScalars ℝ) =
      nullRealDerivative (weierstrassTriple g (d*h)) := by
    ext w j
    change ((w*d)*weierstrassTriple g h j).re = (w*weierstrassTriple g (d*h) j).re
    apply congrArg Complex.re
    fin_cases j <;> dsimp [weierstrassTriple] <;> ring
  simpa only [he,Function.comp_def] using! hd

theorem height_inverse_derivative {H K : ℂ → ℂ} {ξ h d : ℂ}
    (hH : HasDerivAt H h (K ξ)) (hK : HasDerivAt K d ξ)
    (he : (fun ξ => H (K ξ)) =ᶠ[𝓝 ξ] (fun ξ => ξ)) : h*d = 1 := by
  have hd := hH.comp ξ hK
  exact (hd.congr_of_eventuallyEq he.symm).unique (hasDerivAt_id ξ)

theorem weierstrass_height_coordinate_derivative {X : ℂ → Fin 3 → ℝ}
    {H K : ℂ → ℂ} {ξ d g h : ℂ}
    (hX : HasFDerivAt X (nullRealDerivative (weierstrassTriple g h)) (K ξ))
    (hH : HasDerivAt H h (K ξ)) (hK : HasDerivAt K d ξ)
    (he : (fun ξ => H (K ξ)) =ᶠ[𝓝 ξ] (fun ξ => ξ)) :
    HasFDerivAt (fun ξ => X (K ξ)) (nullRealDerivative (weierstrassTriple g 1)) ξ := by
  have hd := weierstrass_primitive_reparametrization hX hK
  rw [mul_comm d h,height_inverse_derivative hH hK he] at hd
  exact hd

theorem weierstrass_height_coordinate_quarter_turn {X : ℂ → Fin 3 → ℝ}
    {H K : ℂ → ℂ} {ξ d g h : ℂ}
    (hX : HasFDerivAt X (nullRealDerivative (weierstrassTriple g h)) (K ξ))
    (hH : HasDerivAt H h (K ξ)) (hK : HasDerivAt K d ξ)
    (he : (fun ξ => H (K ξ)) =ᶠ[𝓝 ξ] (fun ξ => ξ)) :
    HasFDerivAt (fun ξ => verticalRotation I (X (K ξ)))
      (nullRealDerivative (weierstrassTriple (I*g) 1)) ξ := by
  have hd := (verticalRotation I).hasFDerivAt.comp ξ
    (weierstrass_height_coordinate_derivative hX hH hK he)
  rwa [← nullRealDerivative_unit_multiplier (c := I) (by simp)] at hd

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.weierstrass_height_coordinate_quarter_turn
