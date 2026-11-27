import TwoAxisHelicoid.HarmonicChartGreenIdentities
import TwoAxisHelicoid.CoordinateAreaHessian
import TwoAxisHelicoid.DisplacedChartGramCoordinates

namespace TwoAxisHelicoid
open Complex Matrix Filter Topology InnerProductSpace
open scoped Topology

theorem complex_line_planePartial_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} {z : ℂ} (h : DifferentiableAt ℝ f z) (v : ℂ) :
    HasDerivAt (fun r : ℝ => f (z+(r:ℂ)*v)) (planePartial v f z) 0 := by
  have d : HasFDerivAt f (fderiv ℝ f z) (z+((0:ℝ):ℂ)*v) := by simpa using h.hasFDerivAt
  exact d.comp_hasDerivAt 0 (complex_line_hasDerivAt z v)

theorem coordinateAreaDensity_normal_displacement {Y : ℂ → Fin 3 → ℝ} {u : ℂ → ℝ} {N : ℂ → Fin 3 → ℝ} {z : ℂ}
    (dy : DifferentiableAt ℝ Y z) (du : DifferentiableAt ℝ u z) (dn : DifferentiableAt ℝ N z) :
    (fun s : ℝ => coordinateAreaDensity (fun w => Y w+s • (u w • N w)) z) =
      vectorNormalVariationArea (planePartial 1 Y z) (planePartial I Y z) (N z)
        (planePartial 1 N z) (planePartial I N z) (u z) (planePartial 1 u z) (planePartial I u z) :=
  displaced_chart_gram_area dy du dn

/-- Second derivative of the actual area density on every regular minimal
isothermal chart. A global compact test may pass through a zero of the
height differential or a pole of the stereographic Gauss function. -/
theorem coordinateAreaDensity_harmonic_normal_hessian {Y : ℂ → Fin 3 → ℝ} {u : ℂ → ℝ} {z : ℂ}
    (h : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun x => Y x j) w) ∧
      ConformalCoordinateDerivatives Y w ∧ Function.Injective (fderiv ℝ Y w))
    (du : DifferentiableAt ℝ u z) :
    HasDerivAt (deriv (fun s : ℝ => coordinateAreaDensity
      (fun w => Y w+s • (u w • harmonicChartNormal Y w)) z))
      (planePartial 1 u z^2+planePartial I u z^2-jacobiPotentialDensity Y z*(u z)^2) 0 := by
  have hy : AnalyticAt ℝ Y z :=
    analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (h.self_of_nhds.1 j)
  have frame := harmonic_chart_weingarten_frame h
  have hn := (harmonicChartNormal_data hy h.self_of_nhds.2.1 h.self_of_nhds.2.2).1
  have formula := coordinateAreaDensity_normal_displacement hy.differentiableAt du hn.differentiableAt
  let N := harmonicChartNormal Y
  let g := planePartial 1 Y z ⬝ᵥ planePartial 1 Y z
  let b := -(planePartial 1 N z ⬝ᵥ planePartial 1 Y z)
  let c := -(planePartial 1 N z ⬝ᵥ planePartial I Y z)
  have f : ConformalNormalFrame (planePartial 1 Y z) (planePartial I Y z) (N z)
      (planePartial 1 N z) (planePartial I N z) g b c := frame
  have curvature : jacobiPotentialDensity Y z = 2*(b^2+c^2)/g := by
    change planePartial 1 N z ⬝ᵥ planePartial 1 N z + planePartial I N z ⬝ᵥ planePartial I N z = _
    rw [f.nxnx, f.nyny]
    ring
  rw [formula, curvature]
  exact vector_normal_area_second_variation f (u z) (planePartial 1 u z) (planePartial I u z)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.coordinateAreaDensity_normal_displacement
#print axioms TwoAxisHelicoid.coordinateAreaDensity_harmonic_normal_hessian
