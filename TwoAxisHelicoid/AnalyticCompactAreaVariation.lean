import TwoAxisHelicoid.CompactQuarticArea
import TwoAxisHelicoid.HeightNormalAreaFormula

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory Function
open scoped Topology ContDiff

/-- Actual Weierstrass data and a smooth compact test function suffice to
differentiate the finite-patch normal area twice. No separate joint
continuity or parameter-C2 hypotheses are assumed. -/
theorem compact_actual_area_second_variation_of_analytic_data
    {X : ℂ → Fin 3 → ℝ} {W : ℂ → ℂ} {v : ℝ × ℝ → ℝ}
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hsupport : tsupport v ⊆ K)
    (hv : ContDiff ℝ ∞ v)
    (hX : ∀ p ∈ K, HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (W (planeComplex p))) 1)) (planeComplex p))
    (hW : ∀ p ∈ K, AnalyticAt ℂ W (planeComplex p)) :
    HasDerivAt (deriv (fun s => ∫ p in K, coordinateVariationDensity X W v s p))
      (planarQuadraticEnergy (gaussNormalDirichletDensity W) v) 0 := by
  let D : ℝ × ℝ → ℂ := fun p => deriv W (planeComplex p)
  let g : ℝ × ℝ → ℝ := fun p => (Real.cosh (W (planeComplex p)).re)^2
  let b : ℝ × ℝ → ℝ := fun p => -(D p).re
  let c : ℝ × ℝ → ℝ := fun p => (D p).im
  let u := v
  let dx : ℝ × ℝ → ℝ := fun p => fderiv ℝ v p (1,0)
  let dy : ℝ × ℝ → ℝ := fun p => fderiv ℝ v p (0,1)
  let A : ℝ × ℝ → ℝ := fun p => g p*((dx p)^2+(dy p)^2)-2*(u p)^2*((b p)^2+(c p)^2)
  let B : ℝ × ℝ → ℝ := fun p => 2*u p*b p*((dx p)^2-(dy p)^2)+4*u p*c p*dx p*dy p
  let C : ℝ × ℝ → ℝ := fun p =>
    (u p)^4*((b p)^2+(c p)^2)^2/(g p)^2+
      (u p)^2*((b p)^2+(c p)^2)/g p*((dx p)^2+(dy p)^2)
  have hwC : ContinuousOn (fun p => W (planeComplex p)) K := by
    intro p hp
    exact ((hW p hp).continuousAt.comp (f := planeComplex) (by unfold planeComplex; fun_prop)).continuousWithinAt
  have hDC : ContinuousOn D K := by
    intro p hp
    exact ((hW p hp).deriv.continuousAt.comp (f := planeComplex)
      (by unfold planeComplex; fun_prop)).continuousWithinAt
  have hgC : ContinuousOn g K :=
    (Real.continuous_cosh.comp_continuousOn
      (Complex.continuous_re.comp_continuousOn hwC)).pow 2
  have hbC : ContinuousOn b K := (Complex.continuous_re.comp_continuousOn hDC).neg
  have hcC : ContinuousOn c K := Complex.continuous_im.comp_continuousOn hDC
  have huC : ContinuousOn u K := hv.continuous.continuousOn
  have hdxC : ContinuousOn dx K :=
    ((hv.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
  have hdyC : ContinuousOn dy K :=
    ((hv.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
  have hgpos p : 0 < g p := by dsimp [g]; positivity
  have hgnz p : g p ≠ 0 := (hgpos p).ne'
  have hAC : ContinuousOn A K := by dsimp only [A]; fun_prop
  have hBC : ContinuousOn B K := by dsimp only [B]; fun_prop
  have hCC : ContinuousOn C K := by
    dsimp only [C]
    fun_prop (disch := intros; positivity)
  have hg1 p : 1 ≤ g p := by
    dsimp [g]
    nlinarith [Real.one_le_cosh (W (planeComplex p)).re]
  have hform p (hp : p ∈ K) : (fun s => coordinateVariationDensity X W v s p) =
      fun s => Real.sqrt (areaQuartic (g p) (A p) (B p) (C p) s) := by
    have he := actual_coordinate_variation_scalar_area_formula (hX p hp)
      (hW p hp).differentiableAt.hasDerivAt ((hv.differentiable (by simp)) p)
    rw [normalVariationArea_eq_quartic (sq_pos_of_pos (Real.cosh_pos _)).ne'] at he
    exact he
  have hd := compact_quartic_area_integral_second_derivative hK hgC hAC hBC hCC (fun p _ => hg1 p)
  have hI : (fun s => ∫ p in K, coordinateVariationDensity X W v s p) =
      fun s => ∫ p in K, Real.sqrt (areaQuartic (g p) (A p) (B p) (C p) s) := by
    funext s
    apply setIntegral_congr_fun hK.measurableSet
    intro p hp
    exact congrFun (hform p hp) s
  rw [← hI] at hd
  have hhess p (hp : p ∈ K) : coordinateNormalAreaHessian X W v p = A p/g p := by
    change deriv (deriv (fun s => coordinateVariationDensity X W v s p)) 0 = _
    rw [hform p hp]
    exact (areaQuartic_sqrt_second_derivative (hgpos p) (A p) (B p) (C p)).deriv
  have hi : (∫ p in K, coordinateNormalAreaHessian X W v p) =
      integratedCoordinateAreaHessian X W v := by
    rw [← integral_indicator hK.measurableSet]
    unfold integratedCoordinateAreaHessian
    congr 1
    funext p
    by_cases hp : p ∈ K
    · exact indicator_of_mem hp _
    · rw [indicator_of_notMem hp]
      exact (coordinateNormalAreaHessian_zero_off_support X W
        (fun hmem => hp (hsupport hmem))).symm
  have hcoeff : (∫ p in K, A p/g p) = integratedCoordinateAreaHessian X W v := by
    rw [← hi]
    apply setIntegral_congr_fun hK.measurableSet
    intro p hp
    exact (hhess p hp).symm
  rw [hcoeff,integratedCoordinateAreaHessian_eq_planar (hv.differentiable (by simp))
    (fun p hp => hX p (hsupport hp))
    (fun p hp => (hW p (hsupport hp)).differentiableAt)] at hd
  exact hd

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.compact_actual_area_second_variation_of_analytic_data
