import TwoAxisHelicoid.VariableHeightNormalFrame

namespace TwoAxisHelicoid
open Complex Matrix

private theorem normal_variation_density_from_derivative {X : ℂ → Fin 3 → ℝ} {W : ℂ → ℂ} {φ : ℂ → ℝ}
    {z D : ℂ} {J : ℂ →L[ℝ] (Fin 3 → ℝ)} (hX : HasFDerivAt X J z) (hW : HasDerivAt W D z)
    {ux uy : ℝ} (hx : HasDerivAt (fun v : ℝ => φ (z+(v:ℂ))) ux 0)
    (hy : HasDerivAt (fun v : ℝ => φ (z+I*(v:ℂ))) uy 0) :
    (fun s => coordinateAreaDensity (weierstrassNormalVariation X W φ s) z)=
      vectorNormalVariationArea (J 1) (J I) (logGaussSphere (W z).re (W z).im)
        (logGaussNormalX (W z).re (W z).im D) (logGaussNormalY (W z).re (W z).im D) (φ z) ux uy := by
  have dX := complex_line_composition_hasDerivAt hX 1
  have dY := complex_line_composition_hasDerivAt hX I
  have nX := holomorphicLogGaussNormal_line_hasDerivAt hW 1
  have nY := holomorphicLogGaussNormal_line_hasDerivAt hW I
  simp only [mul_one] at dX nX
  simp only [mul_comm (I:ℂ)] at hy
  funext s
  have dx := ((dX.add ((hx.smul nX).const_smul s))).deriv
  have dy := ((dY.add ((hy.smul nY).const_smul s))).deriv
  simp only [Complex.ofReal_zero,zero_mul,add_zero] at dx dy
  unfold coordinateAreaDensity
  simp only [mul_comm (I:ℂ)]
  change deriv (fun v : ℝ => weierstrassNormalVariation X W φ s (z+(v:ℂ))) 0 = _ at dx
  change deriv (fun v : ℝ => weierstrassNormalVariation X W φ s (z+(v:ℂ)*I)) 0 = _ at dy
  rw [dx,dy]
  simp only [vectorNormalVariationArea,holomorphicLogGaussNormal,logGaussNormalX,logGaussNormalY,Complex.I_mul_re,
    Complex.I_mul_im,add_comm,one_mul]

/-- Actual area in an arbitrary regular holomorphic Weierstrass chart.
The first fundamental coefficient includes the true height differential. -/
theorem variable_height_normal_variation_area {X : ℂ → Fin 3 → ℝ} {W : ℂ → ℂ} {v : ℝ × ℝ → ℝ}
    {p : ℝ × ℝ} {D h : ℂ} (nh : h≠0)
    (hX : HasFDerivAt X (nullRealDerivative (weierstrassTriple (exp (W (planeComplex p))) h)) (planeComplex p))
    (hW : HasDerivAt W D (planeComplex p)) (hv : DifferentiableAt ℝ v p) :
    (fun s => coordinateVariationDensity X W v s p)=
      normalVariationArea (‖h‖^2*(Real.cosh (W (planeComplex p)).re)^2)
        (h.re*(-D.re)+h.im*D.im) (-h.im*(-D.re)+h.re*D.im) (v p) (fderiv ℝ v p (1,0)) (fderiv ℝ v p (0,1)) := by
  have eq := normal_variation_density_from_derivative hX hW (scalarComplexLift_line_x hv) (scalarComplexLift_line_y hv)
  change (fun s => coordinateVariationDensity X W v s p)=_ at eq
  rw [eq,scalarComplexLift_planeComplex]
  exact vectorNormalVariationArea_formula (variable_height_log_gauss_frame _ D h nh) _ _ _

/-- At a regular point the second area derivative depends on the energy
of the normal and the Euclidean gradient of the test. The height factor
cancels for every nonzero complex value. -/
theorem variable_height_coordinate_hessian {X : ℂ → Fin 3 → ℝ} {W : ℂ → ℂ} {v : ℝ × ℝ → ℝ}
    {p : ℝ × ℝ} {D h : ℂ} (nh : h≠0)
    (hX : HasFDerivAt X (nullRealDerivative (weierstrassTriple (exp (W (planeComplex p))) h)) (planeComplex p))
    (hW : HasDerivAt W D (planeComplex p)) (hv : DifferentiableAt ℝ v p) :
    coordinateNormalAreaHessian X W v p=
      (fderiv ℝ v p (1,0))^2+(fderiv ℝ v p (0,1))^2-gaussNormalDirichletDensity W p*(v p)^2 := by
  let w := W (planeComplex p)
  have sq (a : ℂ) : a.re^2+a.im^2=‖a‖^2 := by
    simpa [Complex.normSq_apply,pow_two] using Complex.normSq_eq_norm_sq a
  have num : (h.re*(-D.re)+h.im*D.im)^2+(-h.im*(-D.re)+h.re*D.im)^2=‖h‖^2*‖D‖^2 := by
    rw [← sq h,← sq D]
    ring
  have metric : 0<‖h‖^2*(Real.cosh w.re)^2 := mul_pos (sq_pos_of_pos (norm_pos_iff.mpr nh)) (sq_pos_of_pos (Real.cosh_pos _))
  change deriv (deriv (fun s => coordinateVariationDensity X W v s p)) 0=_
  rw [variable_height_normal_variation_area nh hX hW hv,(conformal_normal_area_second_variation metric _ _ _ _ _).deriv,
    num,gaussNormalDirichletDensity_formula hW]
  change _- (_/(_*(Real.cosh w.re)^2))*(v p)^2=_- (_/(Real.cosh w.re)^2)*(v p)^2
  field_simp [norm_ne_zero_iff.mpr nh,(Real.cosh_pos w.re).ne']

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.variable_height_normal_variation_area
#print axioms TwoAxisHelicoid.variable_height_coordinate_hessian
