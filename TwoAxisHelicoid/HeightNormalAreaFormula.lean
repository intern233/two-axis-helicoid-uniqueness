import TwoAxisHelicoid.CompactAreaVariation

namespace TwoAxisHelicoid
open Complex

theorem actual_coordinate_variation_scalar_area_formula
    {X : ℂ → Fin 3 → ℝ} {W : ℂ → ℂ} {v : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {D : ℂ}
    (hX : HasFDerivAt X (nullRealDerivative (weierstrassTriple (exp (W (planeComplex p))) 1)) (planeComplex p))
    (hW : HasDerivAt W D (planeComplex p)) (hv : DifferentiableAt ℝ v p) :
    (fun s => coordinateVariationDensity X W v s p) =
      normalVariationArea ((Real.cosh (W (planeComplex p)).re)^2) (-D.re) D.im
        (v p) (fderiv ℝ v p (1,0)) (fderiv ℝ v p (0,1)) := by
  have he := weierstrass_normal_variation_area_formula hX hW
    (scalarComplexLift_line_x hv) (scalarComplexLift_line_y hv)
  change (fun s => coordinateVariationDensity X W v s p) = _ at he
  rw [he,scalarComplexLift_planeComplex]
  obtain ⟨hA,hB⟩ := weierstrass_exp_real_tangents (W (planeComplex p))
  have hnx : deriv (fun s : ℝ => holomorphicLogGaussNormal W (planeComplex p+(s : ℂ))) 0 =
      logGaussNormalX (W (planeComplex p)).re (W (planeComplex p)).im D := by
    simpa only [mul_one,one_mul,logGaussNormalX] using
      (holomorphicLogGaussNormal_line_hasDerivAt hW 1).deriv
  have hny : deriv (fun s : ℝ => holomorphicLogGaussNormal W (planeComplex p+I*(s : ℂ))) 0 =
      logGaussNormalY (W (planeComplex p)).re (W (planeComplex p)).im D := by
    simpa [logGaussNormalY,Complex.mul_re,Complex.mul_im,mul_comm (I : ℂ)] using
      (holomorphicLogGaussNormal_line_hasDerivAt hW I).deriv
  rw [hA,hB,hnx,hny]
  exact vectorNormalVariationArea_formula
    (logGauss_conformal_normal_frame (W (planeComplex p)).re (W (planeComplex p)).im D) _ _ _

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_coordinate_variation_scalar_area_formula
