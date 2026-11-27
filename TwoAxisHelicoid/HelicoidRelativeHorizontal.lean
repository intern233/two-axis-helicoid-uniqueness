import TwoAxisHelicoid.HelicoidAngularPhase
import TwoAxisHelicoid.RhombicPhysicalAxisPreimages
import TwoAxisHelicoid.VerticalAxisDividedDifference

namespace TwoAxisHelicoid
open Complex Set Filter Topology Matrix
open scoped Topology

/-- Horizontal position in the rotating frame of a comparison helicoid. -/
noncomputable def helicoidRelativeHorizontal (α b : ℝ) (p : Fin 3 → ℝ) : ℂ :=
  Complex.exp (-((α*(p 2-b):ℝ):ℂ)*I)*spatialGraphProjection 0 1 p

theorem helicoidRelativeHorizontal_analytic (α b : ℝ) (p : Fin 3 → ℝ) :
    AnalyticAt ℝ (helicoidRelativeHorizontal α b) p := by
  have hp : AnalyticAt ℝ (fun v : Fin 3 → ℝ => v 2) p := (ContinuousLinearMap.proj (2 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ).analyticAt p
  have ah : AnalyticAt ℝ (fun v : Fin 3 → ℝ => α*(v 2-b)) p := analyticAt_const.mul (hp.sub analyticAt_const)
  have ac : AnalyticAt ℝ (fun v : Fin 3 → ℝ => -((α*(v 2-b):ℝ):ℂ)*I) p :=
    (((ofRealCLM.analyticAt _).comp ah).neg).mul analyticAt_const
  exact ((analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp ac).mul ((spatialGraphProjection 0 1).analyticAt p)

theorem helicoidRelativeHorizontal_eq_zero_iff (α b : ℝ) (p : Fin 3 → ℝ) :
    helicoidRelativeHorizontal α b p=0 ↔ p 0=0 ∧ p 1=0 := by
  rw [helicoidRelativeHorizontal,mul_eq_zero,or_iff_right (Complex.exp_ne_zero _)]
  exact Complex.ext_iff

/-- The comparison side is the imaginary coordinate of the rotated
horizontal position after a constant phase change. -/
theorem helicoid_side_relative_argument (p : Fin 3 → ℝ) (k α b : ℝ) :
    axisHelicoidSide (helicoidPhaseNormal k) α b p =
      (exp (-(k:ℂ)*I)*helicoidRelativeHorizontal α b p).im := by
  let h := α*(p 2-b)
  have a : helicoidPhaseNormal k * exp (I*(h:ℂ))=I*exp (((k+h:ℝ):ℂ)*I) := by
    unfold helicoidPhaseNormal
    rw [mul_assoc,← Complex.exp_add]
    push_cast
    ring_nf
  have e : exp (-(k:ℂ)*I)*exp (-(h:ℂ)*I)=exp (((-(k+h):ℝ):ℂ)*I) := by
    rw [← Complex.exp_add]
    push_cast
    ring_nf
  change (helicoidPhaseNormal k * exp (I*(h:ℂ))).re * p 0 +
    (helicoidPhaseNormal k * exp (I*(h:ℂ))).im * p 1 =
      (exp (-(k:ℂ)*I)*(exp (-(h:ℂ)*I)*spatialGraphProjection 0 1 p)).im
  rw [a,← mul_assoc,e,Complex.I_mul_re,Complex.I_mul_im,exp_ofReal_mul_I_re,exp_ofReal_mul_I_im,Complex.mul_im,
    exp_ofReal_mul_I_re,exp_ofReal_mul_I_im,Real.sin_neg,Real.cos_neg]
  change -Real.sin (k+h)*p 0+Real.cos (k+h)*p 1=Real.cos (k+h)*p 1+-Real.sin (k+h)*p 0
  ring

/-- At a point of a vertical parameter line mapped into the spatial
axis, the tangential derivative of the horizontal projection vanishes
and the transverse derivative is nonzero. The latter follows from
regularity and conformality of the actual immersion. -/
theorem vertical_axis_horizontal_derivatives {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (ax : AnalyticAt ℝ X z) (hc : ConformalCoordinateDerivatives X z) (hi : Function.Injective (fderiv ℝ X z))
    (line : ∀ᶠ s : ℝ in 𝓝 0, spatialGraphProjection 0 1 (X (z+s • I))=0) :
    let P := fun w => spatialGraphProjection 0 1 (X w)
    fderiv ℝ P z I=0 ∧ fderiv ℝ P z 1≠0 := by
  let D := fderiv ℝ X z
  let P := fun w => spatialGraphProjection 0 1 (X w)
  have dp : fderiv ℝ P z=(spatialGraphProjection 0 1).comp D := ((spatialGraphProjection 0 1).hasFDerivAt.comp z ax.differentiableAt.hasFDerivAt).fderiv
  have hl : HasDerivAt (fun s : ℝ => z+s • I) I 0 := by
    simpa only [Pi.add_apply,zero_add,one_smul] using! (hasDerivAt_const (0:ℝ) z).add ((hasDerivAt_id 0).smul_const I)
  have pp : DifferentiableAt ℝ P z := (spatialGraphProjection 0 1).differentiableAt.comp z ax.differentiableAt
  have aa := ((show HasFDerivAt P (fderiv ℝ P z) (z+(0:ℝ) • I) by simpa using pp.hasFDerivAt).comp_hasDerivAt 0 hl)
  have coinc : (fun s : ℝ => P (z+s • I)) =ᶠ[𝓝 0] (fun _ => (0:ℂ)) := line
  have ez : fderiv ℝ P z I=0 := (aa.congr_of_eventuallyEq coinc.symm).unique (hasDerivAt_const _ (0 : ℂ))
  refine ⟨ez,?_⟩
  intro zero
  rw [dp] at ez zero
  have a₀ : D 1 0=0 := congrArg re zero
  have a₁ : D 1 1=0 := congrArg im zero
  have b₀ : D I 0=0 := congrArg re ez
  have b₁ : D I 1=0 := congrArg im ez
  have ortho : D 1 ⬝ᵥ D I=0 := ((conformalCoordinateDerivatives_iff_dot ax.differentiableAt).mp hc).2
  have nz (v : ℂ) (nv : v ≠ 0) : D v≠0 := fun eq => nv (hi (eq.trans D.map_zero.symm))
  have nzB : D I 2 ≠ 0 := by
    intro b₂
    apply nz I Complex.I_ne_zero
    funext j
    fin_cases j <;> assumption
  have a₂ : D 1 2=0 := by
    have prod : D 1 2*D I 2=0 := by simpa [dotProduct,Fin.sum_univ_succ,a₀,a₁] using ortho
    exact (mul_eq_zero.mp prod).resolve_right nzB
  apply nz 1 one_ne_zero
  funext j
  fin_cases j <;> assumption

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.helicoid_side_relative_argument
#print axioms TwoAxisHelicoid.vertical_axis_horizontal_derivatives
