import TwoAxisHelicoid.MinimalSimilarityJacobi

namespace TwoAxisHelicoid
open Complex Matrix Filter InnerProductSpace Laplacian
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem c2_plane_second_column {f : ℂ → E} {z : ℂ} (c : ContDiffAt ℝ 2 f z) (v w : ℂ) :
    planePartial v (planePartial w f) z = fderiv ℝ (fderiv ℝ f) z v w := by
  have d := ((c.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have h := (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp z d
  change fderiv ℝ ((ContinuousLinearMap.apply ℝ E w) ∘ fderiv ℝ f) z v = _
  rw [h.fderiv]
  rfl

theorem c2_plane_laplacian_columns {f : ℂ → E} {z : ℂ} (c : ContDiffAt ℝ 2 f z) :
    (Δ f) z = planePartial 1 (planePartial 1 f) z + planePartial I (planePartial I f) z := by
  simp only [laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,
    c2_plane_second_column c,Matrix.cons_val_zero,Matrix.cons_val_one]

private theorem c2_first_column_differentiable {f : ℂ → E} {z : ℂ} (c : ContDiffAt ℝ 2 f z)
    (v : ℂ) : DifferentiableAt ℝ (planePartial v f) z :=
  (ContinuousLinearMap.apply ℝ E v).differentiableAt.comp z
    ((c.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero)

/-- Only two ordinary derivatives of the velocity are needed in the product
rule for its normal component. In particular, a smooth compactly supported
variation is allowed. -/
theorem c2_spatial_laplacian_dot {F G : ℂ → Fin 3 → ℝ} {z : ℂ}
    (cf : ContDiffAt ℝ 2 F z) (cg : ContDiffAt ℝ 2 G z) :
    (Δ (fun w => F w ⬝ᵥ G w)) z = F z ⬝ᵥ (Δ G) z + (Δ F) z ⬝ᵥ G z +
      2*(planePartial 1 F z ⬝ᵥ planePartial 1 G z + planePartial I F z ⬝ᵥ planePartial I G z) := by
  have df := cf.differentiableAt (by norm_num)
  have dg := cg.differentiableAt (by norm_num)
  have cp : ContDiffAt ℝ 2 (fun w => F w ⬝ᵥ G w) z :=
    (spatialDotBilinear.contDiff.contDiffAt.comp z cf).clm_apply cg
  have d2 (v : ℂ) : planePartial v (planePartial v (fun w => F w ⬝ᵥ G w)) z =
      F z ⬝ᵥ planePartial v (planePartial v G) z + planePartial v (planePartial v F) z ⬝ᵥ G z +
      2*(planePartial v F z ⬝ᵥ planePartial v G z) := by
    let a := fun w => F w ⬝ᵥ planePartial v G w
    let b := fun w => planePartial v F w ⬝ᵥ G w
    have eq : planePartial v (fun w => F w ⬝ᵥ G w) =ᶠ[𝓝 z] fun w => a w+b w := by
      filter_upwards [cf.eventually (by norm_num),cg.eventually (by norm_num)] with w f g
      exact planePartial_dot (f.differentiableAt (by norm_num)) (g.differentiableAt (by norm_num)) v
    have der := congrArg (fun D : ℂ →L[ℝ] ℝ => D v) (eq.fderiv_eq (𝕜:=ℝ))
    have f1 := c2_first_column_differentiable cf v
    have g1 := c2_first_column_differentiable cg v
    have da : DifferentiableAt ℝ a z :=
      (spatialDotBilinear.hasFDerivAt_of_bilinear df.hasFDerivAt g1.hasFDerivAt).differentiableAt
    have db : DifferentiableAt ℝ b z :=
      (spatialDotBilinear.hasFDerivAt_of_bilinear f1.hasFDerivAt dg.hasFDerivAt).differentiableAt
    change planePartial v _ z=planePartial v _ z at der
    rw [der,planePartial_add da db]
    dsimp only [a,b]
    rw [planePartial_dot df g1,planePartial_dot f1 dg]
    ring
  rw [c2_plane_laplacian_columns cp,c2_plane_laplacian_columns cg,c2_plane_laplacian_columns cf,
    d2,d2,dotProduct_add,add_dotProduct]
  ring

/-- Intrinsic Jacobi operator applied to the normal velocity of any spatial
C² field along a minimal chart, with every term computed from the immersion. -/
theorem jacobi_normal_velocity_identity {X W : ℂ → Fin 3 → ℝ} {z : ℂ}
    (regular : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun p => X p j) w) ∧
      ConformalCoordinateDerivatives X w ∧ Function.Injective (fderiv ℝ X w))
    (cw : ContDiffAt ℝ 2 W z) :
    let N := harmonicChartNormal X
    let g := planePartial 1 X z ⬝ᵥ planePartial 1 X z
    g*conformalSurfaceJacobi X (fun p => W p ⬝ᵥ N p) z =
      (Δ W) z ⬝ᵥ N z + 2*(planePartial 1 W z ⬝ᵥ planePartial 1 N z +
        planePartial I W z ⬝ᵥ planePartial I N z) := by
  let N := harmonicChartNormal X
  let g := planePartial 1 X z ⬝ᵥ planePartial 1 X z
  let V := planePartial 1 N z ⬝ᵥ planePartial 1 N z + planePartial I N z ⬝ᵥ planePartial I N z
  have cx : AnalyticAt ℝ X z :=
    analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (regular.self_of_nhds.1 j)
  have data := harmonicChartNormal_data cx regular.self_of_nhds.2.1 regular.self_of_nhds.2.2
  have gpos : 0 < g := data.2.1
  have normal : (Δ N) z = -(V • N z) :=
    eq_neg_of_add_eq_zero_left (harmonic_chart_gauss_normal_equation regular)
  have eq := c2_spatial_laplacian_dot cw (show ContDiffAt ℝ 2 N z from data.1.contDiffAt)
  rw [normal,dotProduct_neg,dotProduct_smul,smul_eq_mul] at eq
  change g*(((Δ (fun p => W p ⬝ᵥ N p)) z + V*(W z ⬝ᵥ N z))/g) = _
  rw [eq]
  field_simp [gpos.ne']
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.c2_spatial_laplacian_dot
#print axioms TwoAxisHelicoid.jacobi_normal_velocity_identity
