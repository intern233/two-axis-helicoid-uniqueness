import TwoAxisHelicoid.LopezRosSimpleVerticalPoint
import TwoAxisHelicoid.LopezRosNullFamily
import TwoAxisHelicoid.NullGaussAlgebra
import Mathlib.Analysis.Complex.HasPrimitives

namespace TwoAxisHelicoid
open Complex Set Filter Metric Topology
open scoped Topology ComplexConjugate

private theorem lopezRos_position_components (k : ℝ) (p : Fin 3 → ℂ) :
    ((lopezRosCoefficients (k:ℂ) p 0).re : ℂ)+I*((lopezRosCoefficients (k:ℂ) p 1).re : ℂ) =
      ((k:ℂ)*nullHorizontalPlus p+conj (nullHorizontalMinus p)/(k:ℂ))/2 := by
  let q := lopezRosCoefficients (k:ℂ) p
  obtain ⟨h₁,h₂⟩ := lopezRosHorizontal_characteristic (k:ℂ) (p 0) (p 1)
  change q 0+I*q 1 = (k:ℂ)*nullHorizontalPlus p at h₁
  change q 0-I*q 1 = (k:ℂ)⁻¹*nullHorizontalMinus p at h₂
  have he : conj (q 0-I*q 1) = conj (nullHorizontalMinus p)/(k:ℂ) := by
    rw [h₂,map_mul,Complex.conj_inv,Complex.conj_ofReal,div_eq_inv_mul]
  rw [← h₁,← he]
  change ((q 0).re : ℂ)+I*((q 1).re : ℂ) = _
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,Complex.div_ofNat_re,Complex.div_ofNat_im] <;> ring

/-- A simple zero of the height differential with nonvanishing minus
characteristic forces a local double point in every actual real
López–Ros primitive with sufficiently large positive multiplier. -/
theorem lopez_ros_immersions_cross_near_simple_vertical_point
    (p : ℂ → Fin 3 → ℂ) {r : ℝ} (hr : 0 < r)
    (hhol : AnalyticOnNhd ℂ p (ball 0 r))
    (hnull : ∀ z ∈ ball 0 r, ComplexNull (p z))
    (hm : nullHorizontalMinus (p 0) ≠ 0) (hh : p 0 2 = 0)
    (hs : deriv (fun z => p z 2) 0 ≠ 0)
    (Y : ℝ → ℂ → Fin 3 → ℝ)
    (hY : ∀ k > 0, ∀ z ∈ ball 0 r,
      HasFDerivAt (Y k) (nullRealDerivative (lopezRosCoefficients (k:ℂ) (p z))) z)
    {U : Set ℂ} (hU : U ∈ 𝓝 0) :
    ∀ᶠ k : ℝ in atTop, ∃ x ∈ U, ∃ y ∈ U, x ≠ y ∧ Y k x = Y k y := by
  have pin : (0:ℂ) ∈ ball 0 r := mem_ball_self hr
  have nb := isOpen_ball.mem_nhds pin
  obtain ⟨V,_,hV⟩ := hhol.differentiableOn.isExactOn_ball.with_val_at 0 0
  have hcomp (j : Fin 3) (z : ℂ) (hz : z ∈ ball 0 r) : HasDerivAt (fun w => V w j) (p z j) z :=
    (hasDerivAt_pi.mp (hV z hz)) j
  have haV (j : Fin 3) : AnalyticAt ℂ (fun w => V w j) 0 :=
    DifferentiableOn.analyticAt (fun w hw => (hcomp j w hw).differentiableAt.differentiableWithinAt) nb
  let A := fun w => V w 0+I*V w 1
  let B := fun w => V w 0-I*V w 1
  let C := fun w => V w 2
  have eA (z : ℂ) (hz : z ∈ ball 0 r) : deriv A z = nullHorizontalPlus (p z) :=
    ((hcomp 0 z hz).add ((hcomp 1 z hz).const_mul I)).deriv
  have eB (z : ℂ) (hz : z ∈ ball 0 r) : deriv B z = nullHorizontalMinus (p z) :=
    ((hcomp 0 z hz).sub ((hcomp 1 z hz).const_mul I)).deriv
  have eC : deriv C =ᶠ[𝓝 0] fun z => p z 2 := by
    filter_upwards [nb] with z hz using (hcomp 2 z hz).deriv
  have hn : ∀ᶠ z : ℂ in 𝓝 0, deriv A z*deriv B z+(deriv C z)^2=0 := by
    filter_upwards [nb,eC] with z hz he
    rw [eA z hz,eB z hz,he,mul_comm,null_horizontal_product (hnull z hz),neg_add_cancel]
  have crossings := lopez_ros_large_multiplier_at_simple_vertical_point A B C
    ((haV 0).add (analyticAt_const.mul (haV 1))) ((haV 0).sub (analyticAt_const.mul (haV 1)))
    (haV 2) hn ((eB _ pin).trans_ne hm) (eC.self_of_nhds.trans hh) (eC.deriv_eq.trans_ne hs)
    (inter_mem hU nb)
  filter_upwards [crossings,eventually_gt_atTop (0:ℝ)] with k hk hkpos
  obtain ⟨x,hx,y,hy,hne,he⟩ := hk
  let W := fun z => lopezRosCoefficients (k:ℂ) (V z)
  have dW (z : ℂ) (hz : z ∈ ball 0 r) : HasDerivAt W (lopezRosCoefficients (k:ℂ) (p z)) z := by
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases j
    · exact ((hcomp 0 z hz).const_mul _).add ((hcomp 1 z hz).const_mul _)
    · exact ((hcomp 1 z hz).const_mul _).sub ((hcomp 0 z hz).const_mul _)
    · exact hcomp 2 z hz
  let Z := fun z => coordinateRealPart (W z)
  have dZ z hz := realPart_primitive_hasFDerivAt (dW z hz)
  obtain ⟨b,hb⟩ := isOpen_ball.exists_eq_add_of_fderiv_eq (convex_ball (0:ℂ) r).isPreconnected
    (fun z hz => (hY k hkpos z hz).differentiableAt.differentiableWithinAt)
    (g := Z) (fun z hz => (dZ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hY k hkpos z hz).fderiv.trans (dZ z hz).fderiv.symm)
  refine ⟨x,hx.1,y,hy.1,hne,?_⟩
  rw [hb hx.2,hb hy.2]
  change Z x+b=Z y+b
  apply congrArg (fun w : Fin 3 → ℝ => w+b)
  have hxy := congrArg Prod.fst he
  change ((k:ℂ)*nullHorizontalPlus (V x)+conj (nullHorizontalMinus (V x))/(k:ℂ))/2 =
    ((k:ℂ)*nullHorizontalPlus (V y)+conj (nullHorizontalMinus (V y))/(k:ℂ))/2 at hxy
  rw [← lopezRos_position_components k (V x),← lopezRos_position_components k (V y)] at hxy
  funext j
  fin_cases j
  · simp only [Z,W,coordinateRealPart_apply]
    simpa [Complex.mul_re] using congrArg Complex.re hxy
  · simp only [Z,W,coordinateRealPart_apply]
    simpa [Complex.mul_im] using congrArg Complex.im hxy
  · exact congrArg Prod.snd he

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lopez_ros_immersions_cross_near_simple_vertical_point
