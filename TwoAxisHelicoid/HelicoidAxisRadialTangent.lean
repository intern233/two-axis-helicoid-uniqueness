import TwoAxisHelicoid.HelicoidGraphSpatialGrowth
import TwoAxisHelicoid.AxisHelicoidTangentPlanes
import TwoAxisHelicoid.NullCoordinateRecognition
import TwoAxisHelicoid.CoordinateTubeHomeomorph

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

private noncomputable def radialProjection (θ : ℝ) : HelicoidTubeCoordinates →L[ℝ] ℝ :=
  Real.cos θ • ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ))+
  Real.sin θ • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ))

private theorem radialProjection_apply (θ : ℝ) (v : HelicoidTubeCoordinates) :
    radialProjection θ v=Real.cos θ*v.1.1+Real.sin θ*v.1.2 := rfl

/-- The horizontal projection onto the fixed radial direction of a
normal graph has strictly positive derivative along a radial line,
regardless of the graph slope. -/
theorem helicoid_graph_radial_tangent {u : ℝ × ℝ → ℝ} {p : ℂ}
    (du : DifferentiableAt ℝ u (helicoidConformalBase p)) :
    let G := helicoidGraphMap u ∘ helicoidConformalBase
    Real.cos p.im*(fderiv ℝ G p 1).1.1+Real.sin p.im*(fderiv ℝ G p 1).1.2=Real.cosh p.re := by
  let G := helicoidGraphMap u ∘ helicoidConformalBase
  let q := radialProjection p.im
  let line := fun s : ℝ => p+(s:ℂ)
  have dg := (helicoidGraphMap_differentiableAt du).comp p (helicoidConformalBase_hasFDerivAt p).differentiableAt
  have l : HasDerivAt line 1 0 := by simpa [line] using! (Complex.ofRealCLM.hasDerivAt (x := 0)).const_add p
  have lp : line 0=p := by simp [line]
  have dq : HasDerivAt (fun s => q (G (line s))) (q (fderiv ℝ G p 1)) 0 := by
    have d : HasFDerivAt (q ∘ G) (q.comp (fderiv ℝ G p)) (line 0) := lp ▸ (q.hasFDerivAt.comp p dg.hasFDerivAt)
    exact d.comp_hasDerivAt 0 l
  have val (s : ℝ) : q (G (line s))=Real.sinh (p.re+s) := by
    let a := u (helicoidConformalBase (line s))
    have r : (line s).re=p.re+s := by simp [line]
    have h : (line s).im=p.im := by simp [line]
    change Real.cos p.im*(Real.sinh (line s).re*Real.cos (line s).im+a/helicoidQ _*Real.sin (line s).im)+
      Real.sin p.im*(Real.sinh (line s).re*Real.sin (line s).im-a/helicoidQ _*Real.cos (line s).im)=_
    rw [r,h]
    linear_combination (Real.sinh (p.re+s))*(Real.sin_sq_add_cos_sq p.im)
  have dh : HasDerivAt (fun s : ℝ => Real.sinh (p.re+s)) (Real.cosh p.re) 0 := by
    simpa only [id_eq,add_zero,mul_one] using! ((hasDerivAt_id (0:ℝ)).const_add p.re).sinh
  exact dq.unique (dh.congr_of_eventuallyEq (.of_forall val))

theorem helicoid_projected_parameter_axis (h : ℝ) :
    helicoidProjectedComplexParameter ((0,0),h)=⟨0,h⟩ := by
  let p : ℂ := ⟨0,h⟩
  let u := fun _ : ℝ × ℝ => (0:ℝ)
  have sp : helicoidGraphMap u (helicoidConformalBase p)=((0,0),h) := by
    simp [u,p,helicoidGraphMap,helicoidConformalBase,helicoidTubeMap,helicoidNormalMap,helicoidAngle]
  exact sp ▸ (helicoidProjectedComplexParameter_graph (z := p) (u := u) (by norm_num [u])).2

/-- The true Gauss map of a conformal regular patch on a helicoidal
normal graph never equals the outward horizontal radial direction at
its projected graph parameter. -/
theorem graph_gauss_ne_radial {X : ℂ → Fin 3 → ℝ} {p : Fin 3 → ℂ} {z : ℂ} {u : ℝ × ℝ → ℝ}
    (dx : HasFDerivAt X (nullRealDerivative p) z) (pn : ComplexNull p) (nh : p 2≠0)
    (imm : Function.Injective (fderiv ℝ X z))
    (tube : coordinateToTube (X z)∈helicoidTubeEquiv.target)
    (du : DifferentiableAt ℝ u (helicoidConformalBase (helicoidProjectedComplexParameter (coordinateToTube (X z)))))
    (eq : coordinateToTube ∘ X =ᶠ[𝓝 z] (helicoidGraphMap u ∘ helicoidConformalBase) ∘
      (helicoidProjectedComplexParameter ∘ (coordinateToTube ∘ X))) :
    nullGauss p≠Complex.exp (((helicoidProjectedComplexParameter (coordinateToTube (X z))).im:ℂ)*I) := by
  let Y := coordinateToTube ∘ X
  let P := helicoidProjectedComplexParameter ∘ Y
  let G := helicoidGraphMap u ∘ helicoidConformalBase
  have dy := coordinateToTube.hasFDerivAt.comp z dx
  have dp := (helicoidProjectedComplexParameter_differentiable tube).comp z dy.differentiableAt
  have dg := (helicoidGraphMap_differentiableAt du).comp (P z) (helicoidConformalBase_hasFDerivAt _).differentiableAt
  have chain : coordinateToTube.comp (nullRealDerivative p)=(fderiv ℝ G (P z)).comp (fderiv ℝ P z) :=
    dy.fderiv.symm.trans (eq.fderiv_eq.trans (fderiv_comp z dg dp))
  have inj : Function.Injective (fderiv ℝ P z) := by
    intro a b ab
    apply imm
    rw [dx.fderiv]
    apply coordinateTubeHomeomorph.injective
    change (coordinateToTube.comp (nullRealDerivative p)) a=(coordinateToTube.comp (nullRealDerivative p)) b
    rw [chain,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,ab]
  obtain ⟨w,hw⟩ := (LinearMap.injective_iff_surjective.mp (show Function.Injective (fderiv ℝ P z).toLinearMap from inj)) (1:ℂ)
  have vec : coordinateToTube (nullRealDerivative p w)=fderiv ℝ G (P z) 1 := by
    have d := congrArg (fun L : ℂ →L[ℝ] HelicoidTubeCoordinates => L w) chain
    change coordinateToTube (nullRealDerivative p w)=fderiv ℝ G (P z) (fderiv ℝ P z w) at d
    rwa [show fderiv ℝ P z w=1 from hw] at d
  intro radial
  let θ := (P z).im
  change nullGauss p=Complex.exp ((θ:ℂ)*I) at radial
  have unit : normSq (nullGauss p)=1 := by rw [radial,Complex.normSq_eq_norm_sq,Complex.norm_exp]; simp
  have plane : nullRealDerivative p w∈verticalGaussPlane (nullGauss p) := by
    rw [← weierstrass_unit_gauss_tangent_range unit nh,← null_eq_weierstrassTriple pn nh]
    exact mem_range_self w
  obtain ⟨a,b,ray⟩ := plane
  have h := helicoid_graph_radial_tangent du
  change Real.cos θ*(fderiv ℝ G (P z) 1).1.1+Real.sin θ*(fderiv ℝ G (P z) 1).1.2=Real.cosh (P z).re at h
  rw [← vec,ray] at h
  change Real.cos θ*(a*(nullGauss p).im)+Real.sin θ*(-a*(nullGauss p).re)=_ at h
  rw [radial,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im] at h
  nlinarith [Real.cosh_pos (P z).re]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.graph_gauss_ne_radial
