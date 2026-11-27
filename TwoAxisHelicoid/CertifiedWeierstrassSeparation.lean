import TwoAxisHelicoid.WeierstrassLocalSeparation
import TwoAxisHelicoid.CertifiedGlobalImmersion
import TwoAxisHelicoid.PuncturedLatticePlane

namespace TwoAxisHelicoid
open Complex Set Filter Metric Topology
open scoped Topology

/-- The coordinatewise error test certifies injectivity of the actual
certified torus map on the projected box, including any crossing of
a fundamental-parallelogram boundary. -/
theorem certified_projected_box_injective {U : Set ℂ} (convex : Convex ℝ U) (off : U⊆(certifiedPeriodPair.lattice : Set ℂ)ᶜ)
    {p₀ : Fin 3 → ℂ} (null : ComplexNull p₀) {ε : ℝ} (ep : 0≤ε)
    (error : ∀ z∈U, ∀ j, ‖coordinateData certifiedClosedParameters.t certifiedClosedParameters.a 1 certifiedClosedParameters.height_pos z j-p₀ j‖≤ε)
    (margin : 3*ε^2<nullMetric p₀) :
    InjOn certifiedTorusImmersion ((puncturedPlaneProjection certifiedPeriodPair) '' (Subtype.val ⁻¹' U)) := by
  let p := certifiedClosedParameters
  let X := actualGlobalImmersion p.t p.a 1 p.height_pos
  have H := actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0) p.vertical_closed p.horizontal_closed
  have localInj : InjOn X U := weierstrass_box_injective convex (fun z hz => (H.2.2.2 z (off hz)).1) null ep error margin
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ eq
  have same : X x.1=X y.1 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective eq
  exact congrArg (puncturedPlaneProjection certifiedPeriodPair) (Subtype.ext (localInj hx hy same))

/-- Every regular parameter value admits such a certified box with
rational positive radius and rational positive coefficient tolerance.
No lower bound on the separation of any other sheet is assumed. -/
theorem certified_rational_local_separation {z : ℂ} (nz : z∉certifiedPeriodPair.lattice) :
    let p := certifiedClosedParameters
    let f := coordinateData p.t p.a 1 p.height_pos
    ∃ (r ε : ℚ), 0<r ∧ 0<ε ∧ 3*(ε:ℝ)^2<nullMetric (f z) ∧
      ball z (r:ℝ)⊆(certifiedPeriodPair.lattice : Set ℂ)ᶜ ∧
      (∀ w∈ball z (r:ℝ), ∀ j, ‖f w j-f z j‖≤(ε:ℝ)) ∧
      InjOn certifiedTorusImmersion ((puncturedPlaneProjection certifiedPeriodPair) '' (Subtype.val ⁻¹' ball z (r:ℝ))) := by
  let p := certifiedClosedParameters
  let f := coordinateData p.t p.a 1 p.height_pos
  let q := nullMetric (f z)
  have hn : ComplexNull (f z) := coordinateData_null p.height_pos p.abscissa_mem nz
  have qp : 0<q := nullMetric_pos hn (coordinateData_ne_zero p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0) nz)
  obtain ⟨ε,ep,eb⟩ := exists_rat_btwn (show 0<Real.sqrt q/2 by positivity)
  have sq : 3*(ε:ℝ)^2<q := by
    have h := (sq_lt_sq₀ ep.le (by positivity : 0≤Real.sqrt q/2)).mpr eb
    nlinarith [Real.sq_sqrt qp.le]
  have near (j : Fin 3) : ∀ᶠ w in 𝓝 z, ‖f w j-f z j‖≤(ε:ℝ) := by
    have c : ContinuousAt (fun w => f w j) z := (continuous_apply j).continuousAt.comp ((coordinateData_analyticAt (a := p.a) (c := 1) p.height_pos nz).continuousAt)
    exact (c.tendsto.eventually (ball_mem_nhds _ ep)).mono (fun w h => (dist_eq_norm (f w j) (f z j)) ▸ (mem_ball.mp h).le)
  have all : (certifiedPeriodPair.lattice : Set ℂ)ᶜ ∩ {w | ∀ j, ‖f w j-f z j‖≤(ε:ℝ)} ∈ 𝓝 z :=
    inter_mem (certifiedPeriodPair.isClosed_lattice.isOpen_compl.mem_nhds nz) (Filter.eventually_all.mpr near)
  obtain ⟨v,vp,sub⟩ := Metric.mem_nhds_iff.mp all
  obtain ⟨r,rp,rv⟩ := exists_rat_btwn vp
  have sub' := (ball_subset_ball rv.le).trans sub
  have off := sub'.trans inter_subset_left
  have bound (w) (hw : w∈ball z (r:ℝ)) := (sub' hw).2
  exact ⟨r,ε,by exact_mod_cast rp,by exact_mod_cast ep,sq,off,bound,
    certified_projected_box_injective (convex_ball _ _) off hn ep.le bound sq⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_projected_box_injective
#print axioms TwoAxisHelicoid.certified_rational_local_separation
