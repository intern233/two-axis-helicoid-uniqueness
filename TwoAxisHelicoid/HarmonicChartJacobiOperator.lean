import TwoAxisHelicoid.MinimalSimilarityJacobi

namespace TwoAxisHelicoid
open Complex Matrix Filter InnerProductSpace Laplacian
open scoped Topology

/-- The Jacobi potential is the metric contraction of the second
fundamental form computed from actual second derivatives of the immersion.
The metric factor is the squared length of the first coordinate tangent. -/
theorem harmonic_chart_jacobi_second_fundamental_form {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hreg : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun u => X u j) w) ∧
      ConformalCoordinateDerivatives X w ∧ Function.Injective (fderiv ℝ X w))
    (u : ℂ → ℝ) :
    let N := harmonicChartNormal X z
    let g := planePartial 1 X z ⬝ᵥ planePartial 1 X z
    let II := fun v w : ℂ => N ⬝ᵥ planePartial v (planePartial w X) z
    conformalSurfaceJacobi X u z = (Δ u) z/g +
      ((II 1 1)^2+(II 1 I)^2+(II I 1)^2+(II I I)^2)/g^2*u z := by
  let A := planePartial 1 X
  let B := planePartial I X
  let N := harmonicChartNormal X
  let nx := planePartial 1 N z
  let ny := planePartial I N z
  let g := A z ⬝ᵥ A z
  let b := -(nx ⬝ᵥ A z)
  let c := -(nx ⬝ᵥ B z)
  have H : ConformalNormalFrame (A z) (B z) (N z) nx ny g b c := harmonic_chart_weingarten_frame hreg
  have hdata := hreg.mono fun w hw => harmonicChartNormal_data
    (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hw.1 j)) hw.2.1 hw.2.2
  have hX : AnalyticAt ℝ X z := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hreg.self_of_nhds.1 j)
  have hA := (planePartial_analyticAt hX 1).differentiableAt
  have hB := (planePartial_analyticAt hX I).differentiableAt
  have hN : DifferentiableAt ℝ N z := hdata.self_of_nhds.1.differentiableAt
  have ha (v : ℂ) := derivative_of_constant_pairing (X := N) (Y := A) hN hA (c := 0)
    (hdata.mono fun _ h => h.2.2.2.2.2.2.1) v
  have hb (v : ℂ) := derivative_of_constant_pairing (X := N) (Y := B) hN hB (c := 0)
    (hdata.mono fun _ h => h.2.2.2.2.2.2.2) v
  have haa : N z ⬝ᵥ planePartial 1 A z = b := by linarith [ha 1,H.nxa]
  have hab : N z ⬝ᵥ planePartial 1 B z = c := by linarith [hb 1,H.nxb]
  have hba : N z ⬝ᵥ planePartial I A z = c := by linarith [ha I,H.nya]
  have hbb : N z ⬝ᵥ planePartial I B z = -b := by linarith [hb I,H.nyb]
  change ((Δ u) z+(nx ⬝ᵥ nx + ny ⬝ᵥ ny)*u z)/g = (Δ u) z/g+
    ((N z ⬝ᵥ planePartial 1 A z)^2+(N z ⬝ᵥ planePartial 1 B z)^2+
      (N z ⬝ᵥ planePartial I A z)^2+(N z ⬝ᵥ planePartial I B z)^2)/g^2*u z
  rw [H.nxnx,H.nyny,haa,hab,hba,hbb]
  field_simp [H.metric_pos.ne']
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_chart_jacobi_second_fundamental_form
