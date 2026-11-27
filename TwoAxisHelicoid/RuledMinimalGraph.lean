import TwoAxisHelicoid.ConformalGraphDifference

namespace TwoAxisHelicoid
open Complex Filter Set Topology
open scoped Topology ContDiff

/-- Cartesian graph over a plane containing the vertical direction:
the horizontal slope of the ruling depends only on height. -/
noncomputable def ruledCartesianHeight (a : ℝ → ℝ) (z : ℂ) : ℝ := z.re*a z.im

theorem ruledCartesianHeight_analytic {a : ℝ → ℝ} {z : ℂ} (ha : AnalyticAt ℝ a z.im) :
    AnalyticAt ℝ (ruledCartesianHeight a) z := (reCLM.analyticAt z).mul (ha.comp (f := Complex.im) (imCLM.analyticAt z))

private theorem ruled_height_partial {a : ℝ → ℝ} {z : ℂ} {b : ℝ} (ha : HasDerivAt a b z.im) (v : ℂ) :
    planePartial v (ruledCartesianHeight a) z=v.re*a z.im+z.re*(b*v.im) := by
  have h := reCLM.hasFDerivAt.mul (ha.hasFDerivAt.comp z imCLM.hasFDerivAt)
  have eq := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) h.fderiv
  change planePartial v (ruledCartesianHeight a) z=z.re*(v.im*b)+a z.im*v.re at eq
  rw [eq]
  ring

/-- The rulings of a helicoid yield a solution of the Cartesian minimal
graph equation wherever their slope is finite. The differential equation
for the slope is the only input. -/
theorem ruled_height_minimal_of_riccati {a : ℝ → ℝ} {z : ℂ} (k : ℝ) (ha : AnalyticAt ℝ a z.im)
    (ode : ∀ᶠ y in 𝓝 z.im, HasDerivAt a (k*(1+(a y)^2)) y) :
    cartesianMinimalGraphOperator (ruledCartesianHeight a) z=0 := by
  let g := ruledCartesianHeight a
  let b := fun y => k*(1+(a y)^2)
  let c := k*(2*a z.im*b z.im)
  have da : HasDerivAt a (b z.im) z.im := ode.self_of_nhds
  have db : HasDerivAt b c z.im := by
    convert ((da.pow 2).const_add 1).const_mul k using 1
    dsimp [c]; ring
  have deriva (v : ℂ) : planePartial v (a ∘ Complex.im) z=v.im*b z.im :=
    congrArg (fun L : ℂ →L[ℝ] ℝ => L v) (da.hasFDerivAt.comp z imCLM.hasFDerivAt).fderiv
  have sum : ∀ᶠ w in 𝓝 z, HasDerivAt a (b w.im) w.im := (imCLM.continuous.continuousAt (x := z)).eventually ode
  have first : planePartial 1 g =ᶠ[𝓝 z] a ∘ Complex.im := sum.mono fun w hw => by
    simpa only [Complex.one_re,Complex.one_im,one_mul,mul_zero,add_zero,Function.comp_apply] using ruled_height_partial hw 1
  have second : planePartial I g =ᶠ[𝓝 z] ruledCartesianHeight b := sum.mono fun w hw => by
    simpa only [g,Complex.I_re,Complex.I_im,zero_mul,zero_add,mul_one,ruledCartesianHeight] using! ruled_height_partial hw I
  let D := fderiv ℝ (fderiv ℝ g) z
  have hess (u v : ℂ) : D u v=planePartial u (planePartial v g) z := by
    have hg := ruledCartesianHeight_analytic ha
    exact (congrArg (fun F : ℂ →L[ℝ] ℝ => F u)
      ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp z hg.fderiv.differentiableAt.hasFDerivAt).fderiv).symm
  have xx : D 1 1=0 := by
    rw [hess]
    change fderiv ℝ (planePartial 1 g) z 1=0
    rw [first.fderiv_eq]
    simpa only [planePartial,Complex.one_im,zero_mul] using deriva 1
  have xy : D 1 I=b z.im := by
    rw [hess]
    change fderiv ℝ (planePartial I g) z 1=_
    rw [second.fderiv_eq]
    simpa only [planePartial,Complex.one_re,Complex.one_im,one_mul,mul_zero,add_zero] using ruled_height_partial db 1
  have yy : D I I=z.re*c := by
    rw [hess]
    change fderiv ℝ (planePartial I g) z I=_
    rw [second.fderiv_eq]
    simpa only [planePartial,Complex.I_re,Complex.I_im,zero_mul,zero_add,mul_one] using ruled_height_partial db I
  change (1+(planePartial I g z)^2)*D 1 1-2*planePartial 1 g z*planePartial I g z*D 1 I+(1+(planePartial 1 g z)^2)*D I I=0
  rw [first.self_of_nhds,second.self_of_nhds,xx,xy,yy]
  dsimp [ruledCartesianHeight,b,c]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ruled_height_minimal_of_riccati
