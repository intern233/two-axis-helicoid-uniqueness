import TwoAxisHelicoid.PhysicalHalfHelicoidStability

namespace TwoAxisHelicoid
open Complex Set MeasureTheory Filter Topology
open scoped ContDiff Topology

/-- The area on any compact parameter set of the actual helicoid can
be differentiated twice without restricting the support of the varying
function to that set. This permits Dirichlet data touching the axis. -/
theorem physical_helicoid_patch_area_hessian {K : Set (ℝ × ℝ)} (kc : IsCompact K)
    {v : ℝ × ℝ → ℝ} (smooth : ContDiff ℝ ∞ v) :
    deriv (deriv (fun s => ∫ p in K,
      coordinateVariationDensity verticalHeightHelicoid (fun z => I*z) v s p)) 0=
      ∫ p in K, (fderiv ℝ v p (1,0))^2+(fderiv ℝ v p (0,1))^2-2*(Real.cosh p.2)⁻¹^2*v p^2 := by
  let g := fun p : ℝ × ℝ => (Real.cosh p.2)^2
  let x := fun p : ℝ × ℝ => fderiv ℝ v p (1,0)
  let y := fun p : ℝ × ℝ => fderiv ℝ v p (0,1)
  let A := fun p => g p*(x p^2+y p^2)-2*v p^2
  let B := fun p => 4*v p*x p*y p
  let C := fun p => v p^4/g p^2+v p^2/g p*(x p^2+y p^2)
  have cg : Continuous g := (Real.continuous_cosh.comp continuous_snd).pow 2
  have cx : Continuous x := (smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have cy : Continuous y := (smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have gp (p : ℝ × ℝ) : 0<g p := sq_pos_of_pos (Real.cosh_pos _)
  have ca : Continuous A := (cg.mul ((cx.pow 2).add (cy.pow 2))).sub (continuous_const.mul (smooth.continuous.pow 2))
  have cb : Continuous B := (((continuous_const.mul smooth.continuous).mul cx).mul cy)
  have cc : Continuous C := ((smooth.continuous.pow 4).div (cg.pow 2) (fun p => pow_ne_zero _ (gp p).ne')).add
    (((smooth.continuous.pow 2).div cg (fun p => (gp p).ne')).mul ((cx.pow 2).add (cy.pow 2)))
  have h := compact_quartic_area_integral_second_derivative kc cg.continuousOn ca.continuousOn cb.continuousOn cc.continuousOn
    (fun p _ => by dsimp [g]; nlinarith [Real.one_le_cosh p.2])
  have density (p : ℝ × ℝ) : (fun s => coordinateVariationDensity verticalHeightHelicoid (fun z => I*z) v s p)=
      fun s => Real.sqrt (areaQuartic (g p) (A p) (B p) (C p) s) := by
    have d : HasDerivAt (fun z : ℂ => I*z) I (planeComplex p) := by
      simpa only [mul_one] using (hasDerivAt_id' (planeComplex p)).const_mul I
    have eq := actual_coordinate_variation_scalar_area_formula (verticalHeightHelicoid_weierstrass _) d
      ((smooth.differentiable (by simp)) p)
    rw [normalVariationArea_eq_quartic (sq_pos_of_pos (Real.cosh_pos _)).ne'] at eq
    simpa [g,x,y,A,B,C,planeComplex,Complex.I_mul_re,Real.cosh_neg] using eq
  have area : (fun s => ∫ p in K, coordinateVariationDensity verticalHeightHelicoid (fun z => I*z) v s p)=
      fun s => ∫ p in K, Real.sqrt (areaQuartic (g p) (A p) (B p) (C p) s) := by
    funext s
    exact setIntegral_congr_fun kc.measurableSet fun p _ => congrFun (density p) s
  rw [area,h.deriv]
  apply setIntegral_congr_fun kc.measurableSet
  intro p _
  dsimp [A,x,y,g]
  field_simp [(Real.cosh_pos p.2).ne']

/-- Fixed boundary means that the test vanishes on the axis and on the
other three sides. Its transverse derivative at the axis is unrestricted.
The mass and second variation are both evaluated on the physical patch. -/
theorem physical_half_helicoid_fixed_boundary_gap {R T : ℝ} (rp : 0<R) (tp : 0<T)
    {v : ℝ × ℝ → ℝ} (smooth : ContDiff ℝ ∞ v)
    (sides : ∀ t∈Icc (0:ℝ) T, v (-R,t)=0 ∧ v (R,t)=0)
    (ends : ∀ x∈Icc (-R) R, v (x,0)=0 ∧ v (x,T)=0) :
    let K := Icc (-R) R ×ˢ Icc (0:ℝ) T
    ((1/(R+1))^2/(Real.cosh T)^2)*(∫ p in K, (Real.cosh p.2)^2*v p^2)≤
      deriv (deriv (fun s => ∫ p in K, coordinateVariationDensity verticalHeightHelicoid (fun z => I*z) v s p)) 0 := by
  let K := Icc (-R) R ×ˢ Icc (0:ℝ) T
  have kc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have uniform := half_helicoid_rectangle_stability rp tp.le smooth sides ends
  have small : (∫ p in K, (Real.cosh p.2)^2*v p^2)≤(Real.cosh T)^2*(∫ p in K, v p^2) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on ((((Real.continuous_cosh.comp continuous_snd).pow 2).mul
      (smooth.continuous.pow 2)).continuousOn.integrableOn_compact kc)
      ((continuous_const.mul (smooth.continuous.pow 2)).continuousOn.integrableOn_compact kc) kc.measurableSet
    intro p hp
    have order : Real.cosh p.2≤Real.cosh T := Real.cosh_le_cosh.mpr (by
      rw [abs_of_nonneg hp.2.1,abs_of_nonneg tp.le]; exact hp.2.2)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.cosh_pos _).le order 2) (sq_nonneg _)
  change _≤deriv (deriv (fun s => ∫ p in K, coordinateVariationDensity verticalHeightHelicoid (fun z => I*z) v s p)) 0
  rw [physical_helicoid_patch_area_hessian kc smooth]
  calc
    _ ≤ ((1/(R+1))^2/(Real.cosh T)^2)*((Real.cosh T)^2*(∫ p in K, v p^2)) :=
      mul_le_mul_of_nonneg_left small (by positivity)
    _ = (1/(R+1))^2*(∫ p in K, v p^2) := by field_simp [(Real.cosh_pos T).ne']
    _ ≤ _ := uniform

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_helicoid_patch_area_hessian
#print axioms TwoAxisHelicoid.physical_half_helicoid_fixed_boundary_gap
