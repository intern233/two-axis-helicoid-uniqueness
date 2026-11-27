import TwoAxisHelicoid.ComplexCurveLocalStokes
import TwoAxisHelicoid.RectangularGreenFlux
import TwoAxisHelicoid.SpatialConormalFlux

namespace TwoAxisHelicoid
open Complex Set Filter Topology MeasureTheory InnerProductSpace Laplacian
open scoped Topology ContDiff

/-- The complex coefficient whose imaginary part as a one-form equals
the outward conormal flux of u times the gradient of v. -/
noncomputable def jacobiBoundaryCoefficient (u v : ℂ → ℝ) (z : ℂ) : ℂ :=
  ⟨u z*planePartial 1 v z,-(u z*planePartial I v z)⟩

private theorem linear_form_real_coordinates (T : ℂ →L[ℝ] ℝ) (w : ℂ) :
    T w=w.re*T 1+w.im*T I := by
  have eq : w=w.re • (1:ℂ)+w.im • I := by simpa only [Complex.real_smul,mul_one] using w.re_add_im.symm
  calc T w=T (w.re • (1:ℂ)+w.im • I) := congrArg T eq
       _=_ := by simp only [map_add,map_smul,smul_eq_mul]

/-- Pulling back a Jacobi flux coefficient uses the ordinary
holomorphic one-form transition law, even though the Jacobi fields
themselves are real-valued and need not be harmonic. -/
theorem jacobi_boundary_coefficient_chart_change {φ : ℂ → ℂ} {z : ℂ}
    (hol : DifferentiableAt ℂ φ z) {u v U V : ℂ → ℝ}
    (sameU : u z=U (φ z)) (sameV : v =ᶠ[𝓝 z] V ∘ φ) (smooth : DifferentiableAt ℝ V (φ z)) :
    jacobiBoundaryCoefficient u v z=jacobiBoundaryCoefficient U V (φ z)*deriv φ z := by
  let T := fderiv ℝ V (φ z)
  let k := deriv φ z
  have dφ := hol.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have df := smooth.hasFDerivAt.comp z dφ
  have derivs (w : ℂ) : planePartial w v z=T (w*k) := by
    change fderiv ℝ v z w=_
    rw [sameV.fderiv_eq,df.fderiv]
    rfl
  have dx := (derivs 1).trans (linear_form_real_coordinates T (1*k))
  have dy := (derivs I).trans (linear_form_real_coordinates T (I*k))
  apply Complex.ext <;>
    simp only [jacobiBoundaryCoefficient,Complex.mul_re,Complex.mul_im,dx,dy,sameU,one_mul,
      I_re,I_im,zero_mul,one_mul,zero_sub,zero_add] <;>
    dsimp only [T,k,planePartial] <;> ring

/-- The imaginary part of the exterior derivative of P-iQ is exactly
the planar divergence of the physical flux density. -/
theorem imaginary_exterior_eq_divergence {P Q : ℂ → ℝ} {z : ℂ}
    (p : DifferentiableAt ℝ P z) (q : DifferentiableAt ℝ Q z) :
    (complexFormExteriorCoefficient (fun w => (⟨P w,-Q w⟩:ℂ)) z).im=
      planePartial 1 P z+planePartial I Q z := by
  let E := Complex.equivRealProdCLM.symm
  have der := E.hasFDerivAt.comp z (p.hasFDerivAt.prodMk q.hasFDerivAt.neg)
  have h (w : ℂ) : fderiv ℝ (fun y => (⟨P y,-Q y⟩:ℂ)) z w=
      (⟨fderiv ℝ P z w,-fderiv ℝ Q z w⟩:ℂ) := by
    exact congrArg (fun L : ℂ →L[ℝ] ℂ => L w) der.fderiv
  simp only [complexFormExteriorCoefficient,h,Complex.sub_im,Complex.mul_im,I_re,I_im,zero_mul,
    one_mul,zero_add,sub_neg_eq_add,planePartial]

theorem jacobi_boundary_coefficient_c1 {u v : ℂ → ℝ} {z : ℂ}
    (cu : ContDiffAt ℝ 1 u z) (cv : ContDiffAt ℝ 2 v z) :
    ContDiffAt ℝ 1 (jacobiBoundaryCoefficient u v) z :=
  Complex.equivRealProdCLM.symm.contDiff.contDiffAt.comp z
    ((cu.mul (plane_partial_c1_of_c2 cv 1)).prodMk (cu.mul (plane_partial_c1_of_c2 cv I)).neg)

/-- Pointwise energy density in Green's first identity with arbitrary
test field u and actual scalar Jacobi solution v. -/
theorem imaginary_jacobi_exterior {u v W : ℂ → ℝ} {z : ℂ}
    (cu : ContDiffAt ℝ 1 u z) (cv : ContDiffAt ℝ 2 v z) (equation : (Δ v) z+W z*v z=0) :
    (complexFormExteriorCoefficient (jacobiBoundaryCoefficient u v) z).im=
      planePartial 1 u z*planePartial 1 v z+planePartial I u z*planePartial I v z-W z*u z*v z := by
  let P := fun y => u y*planePartial 1 v y
  let Q := fun y => u y*planePartial I v y
  have p := cu.mul (plane_partial_c1_of_c2 cv 1)
  have q := cu.mul (plane_partial_c1_of_c2 cv I)
  change (complexFormExteriorCoefficient (fun y => (⟨P y,-Q y⟩:ℂ)) z).im=_
  rw [imaginary_exterior_eq_divergence (p.differentiableAt one_ne_zero) (q.differentiableAt one_ne_zero)]
  have h (w : ℂ) := planePartial_mul (cu.differentiableAt one_ne_zero)
    ((plane_partial_c1_of_c2 cv w).differentiableAt one_ne_zero) w
  rw [h 1,h I]
  rw [laplacian_plane_partials_c2 cv] at equation
  linear_combination (u z)*equation

/-- The parameter direction giving the scalar outward conormal
derivative maps to the actual spatial right unit conormal. -/
theorem parameter_unit_normal_maps_to_spatial_conormal (X : ℂ → Fin 3 → ℝ) (z w : ℂ) :
    let D := fderiv ℝ (coordinateToEuclidean ∘ X) z
    D (‖D (-I*w)‖⁻¹ • (-I*w))=chartRightUnitConormal X z w := by
  simp only [chartRightUnitConormal,map_smul]

/-- Physical speed times scalar conormal derivative equals the
imaginary part of the flux one-form along the oriented boundary. -/
theorem jacobi_boundary_form_physical_flux {X : ℂ → Fin 3 → ℝ} {p : Fin 3 → ℂ} {z w : ℂ}
    (null : ComplexNull p) (dX : HasFDerivAt X (nullRealDerivative p) z)
    (nz : fderiv ℝ (coordinateToEuclidean ∘ X) z w ≠ 0) (u v : ℂ → ℝ) :
    let D := fderiv ℝ (coordinateToEuclidean ∘ X) z
    ‖D w‖*(u z*fderiv ℝ v z (‖D (-I*w)‖⁻¹ • (-I*w)))=(w*jacobiBoundaryCoefficient u v z).im := by
  let D := fderiv ℝ (coordinateToEuclidean ∘ X) z
  have d := (coordinateToEuclidean.hasFDerivAt.comp z dX).fderiv
  have norm (q : ℂ) : ‖D q‖^2=nullMetric p*‖q‖^2 := by
    dsimp only [D]
    rw [d]
    exact nullRealDerivative_euclidean_norm_sq null q
  have same : ‖D (-I*w)‖=‖D w‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by rw [norm,norm]; simp)
  have ns : ‖D w‖≠0 := norm_ne_zero_iff.mpr nz
  dsimp only
  change ‖D w‖*(u z*fderiv ℝ v z (‖D (-I*w)‖⁻¹ • (-I*w)))=_
  rw [same,map_smul,smul_eq_mul,linear_form_real_coordinates (fderiv ℝ v z) (-I*w)]
  simp only [jacobiBoundaryCoefficient,planePartial,Complex.mul_im,Complex.mul_re,Complex.neg_re,
    Complex.neg_im,I_im,I_re,neg_zero,neg_one_mul,zero_mul,sub_neg_eq_add,zero_add]
  field_simp [ns]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.jacobi_boundary_coefficient_chart_change
#print axioms TwoAxisHelicoid.imaginary_jacobi_exterior
#print axioms TwoAxisHelicoid.jacobi_boundary_form_physical_flux
