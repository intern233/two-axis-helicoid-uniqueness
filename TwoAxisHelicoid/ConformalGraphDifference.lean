import TwoAxisHelicoid.AnalyticCompositionLaplacian
import TwoAxisHelicoid.ConformalGraphTrace
import TwoAxisHelicoid.RegularGraphCoordinates
import TwoAxisHelicoid.HarmonicChartUnitNormal

namespace TwoAxisHelicoid
open Complex Matrix Filter Topology InnerProductSpace Laplacian
open scoped Topology ContDiff

/-- Height above a specified Cartesian graph. -/
noncomputable def immersionGraphDifference (X : ℂ → Fin 3 → ℝ) (g : ℂ → ℝ) (z : ℂ) : ℝ :=
  X z 2-g (spatialGraphProjection 0 1 (X z))

noncomputable def cartesianMinimalGraphOperator (g : ℂ → ℝ) (w : ℂ) : ℝ :=
  let p := fderiv ℝ g w 1
  let q := fderiv ℝ g w I
  let D := fderiv ℝ (fderiv ℝ g) w
  (1+q^2)*D 1 1-2*p*q*D 1 I+(1+p^2)*D I I

def horizontalMinor (A B : Fin 3 → ℝ) : ℝ := A 0*B 1-B 0*A 1

/-- The polynomial first-order coefficients of the graph difference in
a conformal chart. These contain no inverse horizontal Jacobian. -/
noncomputable def graphDifferenceDrift (A B : Fin 3 → ℝ) (G : ℂ →L[ℝ] ℝ)
    (D : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) : ℝ × ℝ :=
  let j := horizontalMinor A B
  let s := A 1*B 2-B 1*A 2
  let t := A 2*B 0-A 0*B 2
  let l := D I I*(s-G 1*j)-2*D 1 I*t
  let m := D 1 1*(t-G I*j)+2*D 1 I*G 1*j
  (B 1*l-B 0*m,A 0*m-A 1*l)

theorem immersionGraphDifference_analytic {X : ℂ → Fin 3 → ℝ} {g : ℂ → ℝ} {z : ℂ}
    (hX : AnalyticAt ℝ X z) (hg : AnalyticAt ℝ g (spatialGraphProjection 0 1 (X z))) :
    AnalyticAt ℝ (immersionGraphDifference X g) z := by
  have hU : AnalyticAt ℝ (spatialGraphProjection 0 1 ∘ X) z := ((spatialGraphProjection 0 1).analyticAt _).comp hX
  exact ((analyticAt_pi_iff.mp hX) 2).sub (hg.comp (f := spatialGraphProjection 0 1 ∘ X) hU)

/-- The ambient height difference between a harmonic conformal immersion
and a graph satisfies a scalar equation in the immersion's original
conformal parameter. The graph's mean curvature is the only forcing
term. -/
theorem harmonic_graph_difference_equation {X : ℂ → Fin 3 → ℝ} {g : ℂ → ℝ} {z : ℂ}
    (hh : ∀ j, HarmonicAt (fun w => X w j) z) (hc : ConformalCoordinateDerivatives X z)
    (hg : AnalyticAt ℝ g (spatialGraphProjection 0 1 (X z))) :
    let U := spatialGraphProjection 0 1 ∘ X
    let f := immersionGraphDifference X g
    let A := planePartial 1 X z
    let B := planePartial I X z
    let W := graphDifferenceDrift A B (fderiv ℝ g (U z)) (fderiv ℝ (fderiv ℝ g) (U z))
    (A ⬝ᵥ A)*(Δ f) z = W.1*planePartial 1 f z+W.2*planePartial I f z-
      (horizontalMinor A B)^2*cartesianMinimalGraphOperator g (U z) := by
  let P := spatialGraphProjection 0 1
  let U := P ∘ X
  let f := immersionGraphDifference X g
  let A := planePartial 1 X z
  let B := planePartial I X z
  let G := fderiv ℝ g (U z)
  let D := fderiv ℝ (fderiv ℝ g) (U z)
  change (A ⬝ᵥ A)*(Δ f) z = _*planePartial 1 f z+_*planePartial I f z-_
  have hX : AnalyticAt ℝ X z := analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (hh j))
  have hU : AnalyticAt ℝ U z := (P.analyticAt _).comp hX
  have dU := P.hasFDerivAt.comp z hX.differentiableAt.hasFDerivAt
  have eval (v : ℂ) : planePartial v U z=P (planePartial v X z) :=
    congrArg (fun F : ℂ →L[ℝ] ℂ => F v) dU.fderiv
  have differencePartial (v : ℂ) : planePartial v f z=planePartial v X z 2-G 1*planePartial v X z 0-G I*planePartial v X z 1 := by
    have dh := ((ContinuousLinearMap.proj 2 : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z
      hX.differentiableAt.hasFDerivAt).sub (hg.differentiableAt.hasFDerivAt.comp z dU)
    have d := congrArg (fun F : ℂ →L[ℝ] ℝ => F v) dh.fderiv
    change planePartial v f z=planePartial v X z 2-G (P (planePartial v X z)) at d
    rw [d,real_linear_complex_expansion G (P _)]
    change _-(planePartial v X z 0*G 1+planePartial v X z 1*G I)=_
    ring
  have lu : (Δ U) z = 0 := by
    have e := (show ContDiffAt ℝ 2 X z from hX.contDiffAt).laplacian_CLM_comp_left (l := P)
    exact e.trans (by rw [Function.comp_apply,harmonic_coordinate_laplacian_zero hh,map_zero])
  have lc := analytic_plane_laplacian_comp hU hg
  change (Δ (g ∘ U)) z = G ((Δ U) z) + D _ _ + D _ _ at lc
  rw [lu,map_zero,zero_add,eval 1,eval I] at lc
  have ht := analytic_plane_hessian_trace hg (P A) (P B)
  have lsum := lc.trans ht
  have lap : (Δ f) z = -(D 1 1*((A 0)^2+(B 0)^2)+2*D 1 I*(A 0*A 1+B 0*B 1)+D I I*((A 1)^2+(B 1)^2)) := by
    have eq := (show ContDiffAt ℝ 2 (fun w => X w 2) z from (hh 2).1).laplacian_sub
      (show ContDiffAt ℝ 2 (g ∘ U) z from (hg.comp (f := spatialGraphProjection 0 1 ∘ X) hU).contDiffAt)
    change (Δ f) z = _-_ at eq
    rw [eq,(hh 2).2.self_of_nhds,Pi.zero_apply,zero_sub,lsum]
    rfl
  have norm (T : Fin 3 → ℝ) : T ⬝ᵥ T = (T 0)^2+(T 1)^2+(T 2)^2 := by
    simp [dotProduct,Fin.sum_univ_succ,pow_two,add_assoc]
  have pair := (conformalCoordinateDerivatives_iff_dot hX.differentiableAt).mp hc
  have same : (A 0)^2+(A 1)^2+(A 2)^2 = (B 0)^2+(B 1)^2+(B 2)^2 := (norm A).symm.trans (pair.1.trans (norm B))
  have orth : A 0*B 0+A 1*B 1+A 2*B 2=0 := by
    simpa [dotProduct,Fin.sum_univ_succ,add_assoc] using (show A ⬝ᵥ B=0 from pair.2)
  have t := conformal_graph_hessian_trace (A 0) (B 0) (A 1) (B 1) (A 2) (B 2) (G 1) (G I)
    (D 1 1) (D 1 I) (D I I) same orth
  rw [lap,differencePartial 1,differencePartial I,norm]
  change _ = (graphDifferenceDrift A B G D).1*((A 2-G 1*A 0)-G I*A 1)+
    (graphDifferenceDrift A B G D).2*((B 2-G 1*B 0)-G I*B 1)-(horizontalMinor A B)^2*_
  dsimp only [graphDifferenceDrift,horizontalMinor,cartesianMinimalGraphOperator] at *
  linear_combination -t

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_graph_difference_equation
