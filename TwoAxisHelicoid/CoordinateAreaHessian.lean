import TwoAxisHelicoid.WeierstrassNormalVariation
import TwoAxisHelicoid.GaussNormalIndex
import Mathlib.Analysis.Calculus.Deriv.Support

set_option autoImplicit false
namespace TwoAxisHelicoid
open Complex Matrix Set Filter Function
open scoped Topology

noncomputable def scalarComplexLift (v : ℝ × ℝ → ℝ) (z : ℂ) : ℝ := v (z.re,z.im)

@[simp] theorem scalarComplexLift_planeComplex (v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    scalarComplexLift v (planeComplex p) = v p := by simp [scalarComplexLift,planeComplex]

theorem scalarComplexLift_line_x {v : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hv : DifferentiableAt ℝ v p) :
    HasDerivAt (fun t : ℝ => scalarComplexLift v (planeComplex p+(t : ℂ)))
      (fderiv ℝ v p (1,0)) 0 := by
  have hl : HasDerivAt (fun t : ℝ => p+(t,0)) (1,0) 0 := by
    simpa using (HasDerivAt.prodMk (hasDerivAt_id (0 : ℝ)) (hasDerivAt_const (0 : ℝ) (0 : ℝ))).const_add p
  have hp0 : p+((0 : ℝ),0) = p := Prod.ext (add_zero _) (add_zero _)
  have hv' : HasFDerivAt v (fderiv ℝ v p) (p+((0 : ℝ),0)) := by
    simpa only [hp0] using hv.hasFDerivAt
  have h := hv'.comp_hasDerivAt 0 hl
  change HasDerivAt (fun t => v (p.1+t,p.2+0)) (fderiv ℝ v p (1,0)) 0 at h
  simpa [scalarComplexLift,planeComplex] using h

theorem scalarComplexLift_line_y {v : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hv : DifferentiableAt ℝ v p) :
    HasDerivAt (fun t : ℝ => scalarComplexLift v (planeComplex p+I*(t : ℂ)))
      (fderiv ℝ v p (0,1)) 0 := by
  have hl : HasDerivAt (fun t : ℝ => p+(0,t)) (0,1) 0 := by
    simpa using (HasDerivAt.prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ)) (hasDerivAt_id (0 : ℝ))).const_add p
  have hp0 : p+(0,(0 : ℝ)) = p := Prod.ext (add_zero _) (add_zero _)
  have hv' : HasFDerivAt v (fderiv ℝ v p) (p+(0,(0 : ℝ))) := by
    simpa only [hp0] using hv.hasFDerivAt
  have h := hv'.comp_hasDerivAt 0 hl
  change HasDerivAt (fun t => v (p.1+0,p.2+t)) (fderiv ℝ v p (0,1)) 0 at h
  simpa [scalarComplexLift,planeComplex,Complex.mul_re,Complex.mul_im] using
    h

noncomputable def coordinateNormalAreaHessian (X : ℂ → Fin 3 → ℝ) (W : ℂ → ℂ)
    (v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (deriv (fun s => coordinateAreaDensity
    (weierstrassNormalVariation X W (scalarComplexLift v) s) (planeComplex p))) 0

theorem gaussNormalDirichletDensity_formula {W : ℂ → ℂ} {D : ℂ} {p : ℝ × ℝ}
    (hW : HasDerivAt W D (planeComplex p)) :
    gaussNormalDirichletDensity W p = 2*‖D‖^2/(Real.cosh (W (planeComplex p)).re)^2 := by
  obtain ⟨nx,ny,hx,hy,he⟩ := holomorphicLogGaussNormal_energy hW
  unfold gaussNormalDirichletDensity
  rw [hx.deriv,hy.deriv]
  exact he

theorem coordinateNormalAreaHessian_formula
    {X : ℂ → Fin 3 → ℝ} {W : ℂ → ℂ} {v : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {D : ℂ}
    (hX : HasFDerivAt X (nullRealDerivative (weierstrassTriple (exp (W (planeComplex p))) 1)) (planeComplex p))
    (hW : HasDerivAt W D (planeComplex p)) (hv : DifferentiableAt ℝ v p) :
    coordinateNormalAreaHessian X W v p =
      (fderiv ℝ v p (1,0))^2+(fderiv ℝ v p (0,1))^2-gaussNormalDirichletDensity W p*v p^2 := by
  have h := (actual_weierstrass_normal_area_second_variation hX hW
    (scalarComplexLift_line_x hv) (scalarComplexLift_line_y hv)).deriv
  simpa only [coordinateNormalAreaHessian,scalarComplexLift_planeComplex,
    gaussNormalDirichletDensity_formula hW] using h

theorem complex_line_tendsto_zero (z w : ℂ) :
    Tendsto (fun t : ℝ => z+(t : ℂ)*w) (𝓝 0) (𝓝 z) := by
  simpa using (complex_line_hasDerivAt z w).continuousAt.tendsto

theorem coordinateAreaDensity_congr_local {X Y : ℂ → Fin 3 → ℝ} {z : ℂ}
    (h : X =ᶠ[𝓝 z] Y) : coordinateAreaDensity X z = coordinateAreaDensity Y z := by
  have hx := h.comp_tendsto (complex_line_tendsto_zero z 1)
  have hy := h.comp_tendsto (complex_line_tendsto_zero z I)
  simp only [mul_one,Function.comp_def] at hx
  simp only [Function.comp_def] at hy
  unfold coordinateAreaDensity
  simp only [mul_comm (I : ℂ)]
  rw [hx.deriv_eq,hy.deriv_eq]

theorem coordinateNormalAreaHessian_zero_off_support
    (X : ℂ → Fin 3 → ℝ) (W : ℂ → ℂ) {v : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∉ tsupport v) : coordinateNormalAreaHessian X W v p = 0 := by
  have hz := notMem_tsupport_iff_eventuallyEq.mp hp
  have hc : Tendsto (fun z : ℂ => (z.re,z.im)) (𝓝 (planeComplex p)) (𝓝 p) := by
    simpa [planeComplex] using
      (Complex.continuous_re.prodMk Complex.continuous_im).tendsto (planeComplex p)
  have hφ : scalarComplexLift v =ᶠ[𝓝 (planeComplex p)] 0 := hz.comp_tendsto hc
  have he : (fun s => coordinateAreaDensity
      (weierstrassNormalVariation X W (scalarComplexLift v) s) (planeComplex p)) =
      fun _ : ℝ => coordinateAreaDensity X (planeComplex p) := by
    funext s
    apply coordinateAreaDensity_congr_local
    filter_upwards [hφ] with z hz
    simp [weierstrassNormalVariation,hz]
  unfold coordinateNormalAreaHessian
  rw [he]
  simp

noncomputable def integratedCoordinateAreaHessian (X : ℂ → Fin 3 → ℝ) (W : ℂ → ℂ)
    (v : ℝ × ℝ → ℝ) : ℝ := ∫ p : ℝ × ℝ, coordinateNormalAreaHessian X W v p

/-- Equality of the integral of actual pointwise area second derivatives
with the planar Jacobi form. The geometric and holomorphic assumptions
are needed only on the support of the test function. This theorem does
not interchange differentiation with a possibly infinite total area. -/
theorem integratedCoordinateAreaHessian_eq_planar
    {X : ℂ → Fin 3 → ℝ} {W : ℂ → ℂ} {v : ℝ × ℝ → ℝ}
    (hv : Differentiable ℝ v)
    (hX : ∀ p ∈ tsupport v, HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (W (planeComplex p))) 1)) (planeComplex p))
    (hW : ∀ p ∈ tsupport v, DifferentiableAt ℂ W (planeComplex p)) :
    integratedCoordinateAreaHessian X W v = planarQuadraticEnergy (gaussNormalDirichletDensity W) v := by
  unfold integratedCoordinateAreaHessian planarQuadraticEnergy
  congr 1
  funext p
  by_cases hp : p ∈ tsupport v
  · exact coordinateNormalAreaHessian_formula (hX p hp) (hW p hp).hasDerivAt (hv p)
  · rw [coordinateNormalAreaHessian_zero_off_support X W hp]
    have he := notMem_tsupport_iff_eventuallyEq.mp hp
    have hz : v p = 0 := he.self_of_nhds
    have hd : fderiv ℝ v p = 0 := by simpa using he.fderiv_eq
    simp [hz,hd]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.integratedCoordinateAreaHessian_eq_planar
